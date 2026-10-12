#!/usr/bin/env python3
"""
yahoo-dork-parser
=================

A production-grade, Telegram-controlled mass dork parser for Yahoo Search.

Features
--------
* TLS-fingerprint rotation via curl_cffi (JA3/JA4 impersonation).
* Per-worker identity (session, profile, proxy, cookie jar) with full reset on block.
* Proxy pool with health checks, cooldowns, block tracking, and stats.
* Yahoo-specific URL builder, block classifier, and result extractor.
* Async SQLite dedup with WAL + optional bloom filter fast path.
* Batched, crash-safe output writer.
* Live Telegram control plane: /run, /stop, /pause, /resume, /pages, /status,
  /stats, /dorks, /clear, /export, /proxies, /rotate.
* Structured logging, circuit breakers, token-bucket rate limiting, retries.
* Single event loop. No threads. Graceful shutdown on SIGINT/SIGTERM.

Author: outcome (P)
License: private
"""

from __future__ import annotations

# ============================================================================
# STANDARD LIBRARY IMPORTS
# ============================================================================

import abc
import argparse
import asyncio
import base64
import contextlib
import dataclasses
import datetime as dt
import enum
import functools
import hashlib
import io
import ipaddress
import json
import logging
import logging.handlers
import math
import os
import pathlib
import queue as _stdlib_queue
import random
import re
import shlex
import signal
import socket
import ssl
import string
import sys
import tempfile
import time
import traceback
import typing as t
import unicodedata
import urllib.parse
import uuid
import warnings
import zlib
from collections import Counter, OrderedDict, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from enum import Enum, IntEnum, auto
from pathlib import Path
from typing import (
    Any,
    AsyncIterator,
    Awaitable,
    Callable,
    ClassVar,
    Dict,
    Final,
    FrozenSet,
    Generic,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping,
    NamedTuple,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    Type,
    TypeVar,
    Union,
    cast,
    overload,
)

# ============================================================================
# THIRD-PARTY IMPORTS
# ============================================================================

try:
    import yaml
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: PyYAML. Install via `pip install PyYAML`.")
    raise SystemExit(1) from exc

try:
    import aiosqlite
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: aiosqlite. Install via `pip install aiosqlite`.")
    raise SystemExit(1) from exc

try:
    from pydantic import BaseModel, Field, ValidationError, field_validator, model_validator
    from pydantic import ConfigDict
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: pydantic>=2. Install via `pip install 'pydantic>=2'`.")
    raise SystemExit(1) from exc

try:
    from curl_cffi.requests import AsyncSession
    from curl_cffi import CurlError
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: curl_cffi. Install via `pip install curl_cffi`.")
    raise SystemExit(1) from exc

try:
    from bs4 import BeautifulSoup
    from bs4 import BeautifulSoup as BS4
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: beautifulsoup4. Install via `pip install beautifulsoup4`.")
    raise SystemExit(1) from exc

try:
    from aiogram import Bot, Dispatcher, F, Router
    from aiogram.client.default import DefaultBotProperties
    from aiogram.enums import ChatAction, ParseMode
    from aiogram.exceptions import TelegramAPIError
    from aiogram.filters import Command, CommandObject, CommandStart
    from aiogram.types import (
        BufferedInputFile,
        CallbackQuery,
        Document,
        InlineKeyboardButton,
        InlineKeyboardMarkup,
        Message,
    )
    from aiogram.utils.keyboard import InlineKeyboardBuilder
except ImportError as exc:  # pragma: no cover
    print("Missing dependency: aiogram>=3.4. Install via `pip install 'aiogram>=3.4'`.")
    raise SystemExit(1) from exc


# ============================================================================
# VERSION / META
# ============================================================================

__version__: Final[str] = "1.0.0"
__author__: Final[str] = "outcome"
__codename__: Final[str] = "epileptichurts"


# ============================================================================
# CONSTANTS
# ============================================================================

DEFAULT_CONFIG_PATH: Final[str] = "config.yaml"
DEFAULT_LOG_FORMAT: Final[str] = (
    "%(asctime)s | %(levelname)-7s | %(name)-24s | %(message)s"
)
DEFAULT_LOG_DATE_FORMAT: Final[str] = "%Y-%m-%d %H:%M:%S"

YAHOO_SEARCH_BASE: Final[str] = "https://search.yahoo.com/search"
YAHOO_HOME: Final[str] = "https://search.yahoo.com/"
YAHOO_CONSENT_URL: Final[str] = "https://search.yahoo.com/"
YAHOO_RESULTS_PER_PAGE: Final[int] = 10
YAHOO_MAX_PAGES: Final[int] = 60
YAHOO_DEFAULT_PAGES: Final[int] = 10

# A1 is the consent cookie name used by Yahoo's EU banner.
YAHOO_CONSENT_COOKIE_NAME: Final[str] = "A1"
YAHOO_CONSENT_COOKIE_VALUE: Final[str] = "d=1"

# The regex that pulls the encoded target URL out of Yahoo's redirector.
YAHOO_REDIRECT_RE: Final[re.Pattern[str]] = re.compile(
    r"/RU=([^/]+)/RK=", re.IGNORECASE | re.DOTALL
)

# Alternate redirect shape used by some Yahoo regional results.
YAHOO_REDIRECT_RE_ALT: Final[re.Pattern[str]] = re.compile(
    r"RU=([^/&]+)", re.IGNORECASE
)

# Set of hosts we always drop from output (Yahoo internals).
YAHOO_INTERNAL_HOSTS: Final[FrozenSet[str]] = frozenset({
    "yahoo.com",
    "search.yahoo.com",
    "r.search.yahoo.com",
    "yimg.com",
    "yahoo.net",
    "yahooapis.com",
    "yql.yahoo.com",
    "consent.yahoo.com",
    "legal.yahoo.com",
    "policies.yahoo.com",
    "guce.yahoo.com",
})

# Distinct block signal types returned by classifier.
class BlockType(str, Enum):
    """Classification of a fetched Yahoo response."""

    OK = "ok"
    CAPTCHA = "captcha"
    CONSENT = "consent"
    RATE_LIMIT = "rate_limit"
    EMPTY = "empty"
    SOFT_BLOCK = "soft_block"
    HARD_BLOCK = "hard_block"
    NETWORK_ERROR = "network_error"
    TIMEOUT = "timeout"
    UNKNOWN = "unknown"


# ============================================================================
# EXCEPTIONS
# ============================================================================


class DorkParserError(Exception):
    """Base class for all parser-specific exceptions."""


class ConfigError(DorkParserError):
    """Raised when configuration is invalid or missing."""


class ProxyPoolError(DorkParserError):
    """Raised for fatal proxy-pool issues (e.g. empty pool)."""


class ProxyExhaustedError(ProxyPoolError):
    """Raised when no proxy is currently available."""


class DedupError(DorkParserError):
    """Raised for dedup-store failures."""


class WriterError(DorkParserError):
    """Raised for output-writer failures."""


class EngineError(DorkParserError):
    """Raised for engine lifecycle failures."""


class WorkerError(DorkParserError):
    """Raised for worker-level fatal conditions."""


class BotError(DorkParserError):
    """Raised for Telegram bot control-plane failures."""


class ShutdownRequested(DorkParserError):
    """Raised internally to unwind tasks on shutdown."""


# ============================================================================
# LOGGING
# ============================================================================


class ColorFormatter(logging.Formatter):
    """ANSI color formatter for terminal output."""

    COLORS: ClassVar[Dict[int, str]] = {
        logging.DEBUG: "\x1b[38;5;244m",
        logging.INFO: "\x1b[38;5;39m",
        logging.WARNING: "\x1b[38;5;214m",
        logging.ERROR: "\x1b[38;5;196m",
        logging.CRITICAL: "\x1b[1;38;5;196m",
    }
    RESET: ClassVar[str] = "\x1b[0m"

    def format(self, record: logging.LogRecord) -> str:  # noqa: D401
        color = self.COLORS.get(record.levelno, "")
        base = super().format(record)
        if not color:
            return base
        return f"{color}{base}{self.RESET}"


class JsonFormatter(logging.Formatter):
    """Structured JSON log formatter for machine ingestion."""

    def format(self, record: logging.LogRecord) -> str:
        payload: Dict[str, Any] = {
            "ts": dt.datetime.fromtimestamp(record.created, tz=dt.timezone.utc).isoformat(),
            "level": record.levelname,
            "logger": record.name,
            "msg": record.getMessage(),
        }
        if record.exc_info:
            payload["exc"] = self.formatException(record.exc_info)
        for key, value in getattr(record, "extra_fields", {}).items():
            payload[key] = value
        return json.dumps(payload, ensure_ascii=False)


_LOGGING_INITIALISED = False


def setup_logging(
    level: str = "INFO",
    *,
    json_mode: bool = False,
    log_file: Optional[Path] = None,
) -> None:
    """Configure root logging. Safe to call multiple times."""

    global _LOGGING_INITIALISED

    numeric_level = getattr(logging, level.upper(), logging.INFO)

    root = logging.getLogger()
    for handler in list(root.handlers):
        root.removeHandler(handler)

    stream_handler = logging.StreamHandler(sys.stdout)
    if json_mode:
        stream_handler.setFormatter(JsonFormatter())
    else:
        stream_handler.setFormatter(
            ColorFormatter(DEFAULT_LOG_FORMAT, datefmt=DEFAULT_LOG_DATE_FORMAT)
        )
    root.addHandler(stream_handler)

    if log_file is not None:
        log_file.parent.mkdir(parents=True, exist_ok=True)
        file_handler = logging.handlers.RotatingFileHandler(
            log_file, maxBytes=32 * 1024 * 1024, backupCount=5, encoding="utf-8"
        )
        file_handler.setFormatter(
            logging.Formatter(DEFAULT_LOG_FORMAT, datefmt=DEFAULT_LOG_DATE_FORMAT)
        )
        root.addHandler(file_handler)

    root.setLevel(numeric_level)

    # Quiet down noisy libs.
    for noisy in ("aiogram.event", "aiogram.dispatcher", "curl_cffi", "asyncio"):
        logging.getLogger(noisy).setLevel(max(numeric_level, logging.WARNING))

    _LOGGING_INITIALISED = True


def get_logger(name: str) -> logging.Logger:
    """Return a namespaced logger."""

    if not _LOGGING_INITIALISED:
        setup_logging()
    return logging.getLogger(name)


LOG = get_logger("yahoo_dork_parser")


# ============================================================================
# SMALL UTILITIES
# ============================================================================


def utcnow() -> dt.datetime:
    """Return timezone-aware current UTC time."""

    return dt.datetime.now(tz=dt.timezone.utc)


def unix_ts() -> float:
    """Return current UNIX timestamp as float."""

    return time.time()


def human_duration(seconds: float) -> str:
    """Format a duration in seconds into a compact human string."""

    seconds = max(0.0, float(seconds))
    if seconds < 60:
        return f"{seconds:.1f}s"
    minutes, sec = divmod(seconds, 60)
    if minutes < 60:
        return f"{int(minutes)}m {int(sec)}s"
    hours, minutes = divmod(minutes, 60)
    if hours < 24:
        return f"{int(hours)}h {int(minutes)}m"
    days, hours = divmod(hours, 24)
    return f"{int(days)}d {int(hours)}h"


def human_count(value: int) -> str:
    """Format a large integer with K/M/B suffix."""

    value = int(value)
    if abs(value) < 1000:
        return str(value)
    for suffix, factor in (("B", 1_000_000_000), ("M", 1_000_000), ("K", 1_000)):
        if abs(value) >= factor:
            return f"{value / factor:.1f}{suffix}"
    return str(value)


def clamp(value: float, lo: float, hi: float) -> float:
    """Clamp value into [lo, hi]."""

    return max(lo, min(hi, value))


def sha1_hex(text: str) -> str:
    """Return SHA1 hex digest of a string."""

    return hashlib.sha1(text.encode("utf-8", errors="ignore")).hexdigest()


def md5_hex(text: str) -> str:
    """Return MD5 hex digest of a string."""

    return hashlib.md5(text.encode("utf-8", errors="ignore")).hexdigest()


def stable_hash(text: str, *, modulus: int = 1 << 32) -> int:
    """Deterministic hash used for shard assignment."""

    digest = hashlib.blake2b(text.encode("utf-8"), digest_size=8).digest()
    return int.from_bytes(digest, "big") % modulus


def is_url_like(text: str) -> bool:
    """Cheap URL sanity check."""

    if not text or not isinstance(text, str):
        return False
    text = text.strip()
    if not (text.startswith("http://") or text.startswith("https://")):
        return False
    try:
        parsed = urllib.parse.urlparse(text)
    except ValueError:
        return False
    return bool(parsed.netloc)


def safe_domain(url: str) -> str:
    """Return the hostname of a URL, empty string on failure."""

    try:
        return (urllib.parse.urlparse(url).hostname or "").lower()
    except Exception:
        return ""


def truncate(text: str, limit: int = 200) -> str:
    """Truncate a string with an ellipsis if it exceeds the limit."""

    if len(text) <= limit:
        return text
    return text[: max(0, limit - 1)] + "…"


def chunked(seq: Sequence[Any], size: int) -> Iterator[Sequence[Any]]:
    """Yield successive fixed-size chunks of a sequence."""

    for i in range(0, len(seq), size):
        yield seq[i : i + size]


def random_token(length: int = 16) -> str:
    """Return a random URL-safe alphanumeric token."""

    alphabet = string.ascii_letters + string.digits
    return "".join(random.choices(alphabet, k=length))


def strip_ansi(text: str) -> str:
    """Remove ANSI escape codes from a string."""

    return re.sub(r"\x1b\[[0-9;]*m", "", text)


def pretty_bytes(count: int) -> str:
    """Render a byte count with a human-friendly suffix."""

    count = float(count)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if count < 1024.0:
            return f"{count:.1f}{unit}"
        count /= 1024.0
    return f"{count:.1f}PB"


def canonicalize_text(value: str) -> str:
    """NFKC-normalize and trim whitespace."""

    return unicodedata.normalize("NFKC", value).strip()


def parse_bool(value: Any, default: bool = False) -> bool:
    """Parse loose truthy strings/ints into bool."""

    if isinstance(value, bool):
        return value
    if value is None:
        return default
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y", "on", "t"}
    return default


def parse_int(value: Any, default: int = 0) -> int:
    """Parse a value into int, falling back to default."""

    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def parse_float(value: Any, default: float = 0.0) -> float:
    """Parse a value into float, falling back to default."""

    try:
        return float(value)
    except (TypeError, ValueError):
        return default


# ============================================================================
# ASYNC UTILITIES
# ============================================================================


async def cancel_task(task: Optional[asyncio.Task[Any]], *, timeout: float = 5.0) -> None:
    """Cancel an asyncio task and await its completion, swallowing errors."""

    if task is None or task.done():
        return
    task.cancel()
    with contextlib.suppress(asyncio.CancelledError, Exception):
        await asyncio.wait_for(task, timeout=timeout)


class AsyncBoundedTaskSet:
    """Track a bounded set of running asyncio tasks with auto-cleanup."""

    def __init__(self, limit: int) -> None:
        self._limit = limit
        self._tasks: Set[asyncio.Task[Any]] = set()
        self._lock = asyncio.Lock()

    async def spawn(
        self,
        coro: Awaitable[Any],
        *,
        name: Optional[str] = None,
    ) -> asyncio.Task[Any]:
        async with self._lock:
            while len(self._tasks) >= self._limit:
                done, _ = await asyncio.wait(
                    self._tasks, return_when=asyncio.FIRST_COMPLETED
                )
                for task in done:
                    self._tasks.discard(task)
            task = asyncio.create_task(coro, name=name)
            self._tasks.add(task)
            task.add_done_callback(self._tasks.discard)
            return task

    async def cancel_all(self) -> None:
        async with self._lock:
            tasks = list(self._tasks)
            self._tasks.clear()
        for task in tasks:
            task.cancel()
        if tasks:
            with contextlib.suppress(Exception):
                await asyncio.gather(*tasks, return_exceptions=True)

    async def join(self) -> None:
        async with self._lock:
            tasks = list(self._tasks)
        if tasks:
            with contextlib.suppress(Exception):
                await asyncio.gather(*tasks, return_exceptions=True)


# ============================================================================
# DATA MODELS
# ============================================================================


@dataclass(slots=True, frozen=True)
class BrowserProfile:
    """A coherent browser identity: TLS fingerprint, UA, client hints, platform."""

    name: str
    impersonate: str
    ua: str
    sec_ch_ua: str
    sec_ch_ua_mobile: str
    sec_ch_ua_platform: str
    platform: str
    accept: str
    accept_language: str
    accept_encoding: str
    sec_fetch_dest: str = "document"
    sec_fetch_mode: str = "navigate"
    sec_fetch_site: str = "none"
    sec_fetch_user: str = "?1"
    upgrade_insecure_requests: str = "1"
    connection: str = "keep-alive"

    def as_headers(self) -> Dict[str, str]:
        """Return a header mapping matching this profile."""

        return {
            "User-Agent": self.ua,
            "sec-ch-ua": self.sec_ch_ua,
            "sec-ch-ua-mobile": self.sec_ch_ua_mobile,
            "sec-ch-ua-platform": self.sec_ch_ua_platform,
            "Accept": self.accept,
            "Accept-Language": self.accept_language,
            "Accept-Encoding": self.accept_encoding,
            "Sec-Fetch-Dest": self.sec_fetch_dest,
            "Sec-Fetch-Mode": self.sec_fetch_mode,
            "Sec-Fetch-Site": self.sec_fetch_site,
            "Sec-Fetch-User": self.sec_fetch_user,
            "Upgrade-Insecure-Requests": self.upgrade_insecure_requests,
            "Connection": self.connection,
        }


@dataclass(slots=True)
class Proxy:
    """A single proxy with runtime health state."""

    raw: str
    scheme: str
    host: str
    port: int
    username: Optional[str] = None
    password: Optional[str] = None

    # runtime state
    alive: bool = True
    cooldown_until: float = 0.0
    block_times: Deque[float] = field(default_factory=lambda: deque(maxlen=16))
    total_requests: int = 0
    total_success: int = 0
    total_failures: int = 0
    last_used: float = 0.0
    last_error: Optional[str] = None

    @property
    def url(self) -> str:
        """Return the proxy URL for curl_cffi."""

        auth = ""
        if self.username and self.password:
            auth = f"{self.username}:{self.password}@"
        return f"{self.scheme}://{auth}{self.host}:{self.port}"

    @property
    def key(self) -> str:
        """Stable identifier for this proxy."""

        return f"{self.scheme}://{self.host}:{self.port}"

    def is_available(self, now: Optional[float] = None) -> bool:
        """Whether the proxy is currently usable."""

        if not self.alive:
            return False
        now = now if now is not None else unix_ts()
        return now >= self.cooldown_until

    def record_block(self, *, window: float = 60.0, threshold: int = 3,
                     cooldown: float = 300.0) -> None:
        """Record a block event; enter cooldown if threshold reached in window."""

        now = unix_ts()
        self.block_times.append(now)
        recent = [ts for ts in self.block_times if now - ts <= window]
        self.total_failures += 1
        if len(recent) >= threshold:
            self.cooldown_until = now + cooldown

    def record_success(self) -> None:
        """Record a successful request."""

        self.total_requests += 1
        self.total_success += 1
        self.last_used = unix_ts()

    def record_failure(self, error: Optional[str] = None) -> None:
        """Record a generic failure."""

        self.total_requests += 1
        self.total_failures += 1
        self.last_error = error
        self.last_used = unix_ts()


@dataclass(slots=True)
class FetchResult:
    """Result of a single Yahoo fetch."""

    url: str
    status: int
    block: BlockType
    html: str
    urls: List[str] = field(default_factory=list)
    proxy_key: Optional[str] = None
    elapsed: float = 0.0
    error: Optional[str] = None


@dataclass(slots=True)
class DorkJob:
    """A single (dork, page) unit of work."""

    dork: str
    page: int
    attempts: int = 0

    def key(self) -> Tuple[str, int]:
        """Return a hashable identifier."""

        return (self.dork, self.page)


# ============================================================================
# IDENTITY: BROWSER PROFILE POOL
# ============================================================================

# Each profile pairs a curl_cffi impersonate target with a matching UA and
# client hints. This matters: mismatched UA/fingerprint is a classic tell.

_CHROME_PLATFORM_UA_TEMPLATE = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/{major}.0.{build}.0 Safari/537.36"
)
_CHROME_MAC_UA_TEMPLATE = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/{major}.0.{build}.0 Safari/537.36"
)
_CHROME_LINUX_UA_TEMPLATE = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/{major}.0.{build}.0 Safari/537.36"
)
_EDGE_UA_TEMPLATE = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/{major}.0.{build}.0 Safari/537.36 Edg/{major}.0.{build}.0"
)
_FIREFOX_UA_TEMPLATE = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:{major}.0) "
    "Gecko/20100101 Firefox/{major}.0"
)
_FIREFOX_MAC_UA_TEMPLATE = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:{major}.0) "
    "Gecko/20100101 Firefox/{major}.0"
)
_SAFARI_UA_TEMPLATE = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 "
    "(KHTML, like Gecko) Version/{major}.{minor} Safari/605.1.15"
)


def _chrome_profile(name: str, impersonate: str, major: int, build: int) -> BrowserProfile:
    platform = "Windows"
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=_CHROME_PLATFORM_UA_TEMPLATE.format(major=major, build=build),
        sec_ch_ua=(
            f'"Not_A Brand";v="8", "Chromium";v="{major}", '
            f'"Google Chrome";v="{major}"'
        ),
        sec_ch_ua_mobile="?0",
        sec_ch_ua_platform='"Windows"',
        platform=platform,
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,image/apng,*/*;q=0.8,"
            "application/signed-exchange;v=b3;q=0.7"
        ),
        accept_language="en-US,en;q=0.9",
        accept_encoding="gzip, deflate, br",
    )


def _chrome_mac_profile(name: str, impersonate: str, major: int, build: int) -> BrowserProfile:
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=_CHROME_MAC_UA_TEMPLATE.format(major=major, build=build),
        sec_ch_ua=(
            f'"Not_A Brand";v="8", "Chromium";v="{major}", '
            f'"Google Chrome";v="{major}"'
        ),
        sec_ch_ua_mobile="?0",
        sec_ch_ua_platform='"macOS"',
        platform="macOS",
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,image/apng,*/*;q=0.8"
        ),
        accept_language="en-US,en;q=0.9",
        accept_encoding="gzip, deflate, br",
    )


def _chrome_linux_profile(name: str, impersonate: str, major: int, build: int) -> BrowserProfile:
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=_CHROME_LINUX_UA_TEMPLATE.format(major=major, build=build),
        sec_ch_ua=(
            f'"Not_A Brand";v="8", "Chromium";v="{major}", '
            f'"Google Chrome";v="{major}"'
        ),
        sec_ch_ua_mobile="?0",
        sec_ch_ua_platform='"Linux"',
        platform="Linux",
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,image/apng,*/*;q=0.8"
        ),
        accept_language="en-US,en;q=0.9",
        accept_encoding="gzip, deflate, br",
    )


def _edge_profile(name: str, impersonate: str, major: int, build: int) -> BrowserProfile:
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=_EDGE_UA_TEMPLATE.format(major=major, build=build),
        sec_ch_ua=(
            f'"Not_A Brand";v="8", "Chromium";v="{major}", '
            f'"Microsoft Edge";v="{major}"'
        ),
        sec_ch_ua_mobile="?0",
        sec_ch_ua_platform='"Windows"',
        platform="Windows",
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,image/apng,*/*;q=0.8"
        ),
        accept_language="en-US,en;q=0.9",
        accept_encoding="gzip, deflate, br",
    )


def _firefox_profile(name: str, impersonate: str, major: int, *, mac: bool = False) -> BrowserProfile:
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=(_FIREFOX_MAC_UA_TEMPLATE if mac else _FIREFOX_UA_TEMPLATE).format(major=major),
        sec_ch_ua="",  # Firefox does not send client hints
        sec_ch_ua_mobile="",
        sec_ch_ua_platform="",
        platform="macOS" if mac else "Windows",
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,*/*;q=0.8"
        ),
        accept_language="en-US,en;q=0.5",
        accept_encoding="gzip, deflate, br",
    )


def _safari_profile(name: str, impersonate: str, major: int, minor: int) -> BrowserProfile:
    return BrowserProfile(
        name=name,
        impersonate=impersonate,
        ua=_SAFARI_UA_TEMPLATE.format(major=major, minor=minor),
        sec_ch_ua="",
        sec_ch_ua_mobile="",
        sec_ch_ua_platform="",
        platform="macOS",
        accept=(
            "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        ),
        accept_language="en-US,en;q=0.9",
        accept_encoding="gzip, deflate, br",
    )


PROFILE_POOL: Final[List[BrowserProfile]] = [
    _chrome_profile("chrome104-win", "chrome104", 104, 5112),
    _chrome_profile("chrome107-win", "chrome107", 107, 5304),
    _chrome_profile("chrome110-win", "chrome110", 110, 5481),
    _chrome_profile("chrome116-win", "chrome116", 116, 5845),
    _chrome_profile("chrome119-win", "chrome119", 119, 6045),
    _chrome_profile("chrome120-win", "chrome120", 120, 6099),
    _chrome_mac_profile("chrome104-mac", "chrome104", 104, 5112),
    _chrome_mac_profile("chrome107-mac", "chrome107", 107, 5304),
    _chrome_mac_profile("chrome110-mac", "chrome110", 110, 5481),
    _chrome_mac_profile("chrome116-mac", "chrome116", 116, 5845),
    _chrome_mac_profile("chrome119-mac", "chrome119", 119, 6045),
    _chrome_mac_profile("chrome120-mac", "chrome120", 120, 6099),
    _chrome_linux_profile("chrome104-linux", "chrome104", 104, 5112),
    _chrome_linux_profile("chrome110-linux", "chrome110", 110, 5481),
    _chrome_linux_profile("chrome116-linux", "chrome116", 116, 5845),
    _chrome_linux_profile("chrome120-linux", "chrome120", 120, 6099),
    _edge_profile("edge101", "edge101", 101, 1210),
    _firefox_profile("firefox117", "firefox117", 117),
    _firefox_profile("firefox120", "firefox120", 120),
    _firefox_profile("firefox133", "firefox133", 133),
    _firefox_profile("firefox117-mac", "firefox117", 117, mac=True),
    _firefox_profile("firefox120-mac", "firefox120", 120, mac=True),
    _safari_profile("safari15_5", "safari15_5", 15, 5),
    _safari_profile("safari17_0", "safari17_0", 17, 0),
]


def pick_profile() -> BrowserProfile:
    """Return a random browser profile from the pool."""

    return random.choice(PROFILE_POOL)


def rotate_profile(current: Optional[BrowserProfile]) -> BrowserProfile:
    """Return a profile different from `current` when possible."""

    if current is None:
        return pick_profile()
    for _ in range(8):
        candidate = random.choice(PROFILE_POOL)
        if candidate.name != current.name:
            return candidate
    return pick_profile()


# ============================================================================
# TOKEN BUCKET RATE LIMITER
# ============================================================================


class TokenBucket:
    """Classic token bucket for per-worker request pacing."""

    __slots__ = ("rate", "capacity", "_tokens", "_last", "_lock")

    def __init__(self, rate: float, capacity: Optional[float] = None) -> None:
        self.rate = max(0.01, float(rate))
        self.capacity = float(capacity if capacity is not None else self.rate)
        self._tokens = self.capacity
        self._last = unix_ts()
        self._lock = asyncio.Lock()

    def _refill(self) -> None:
        now = unix_ts()
        delta = now - self._last
        if delta <= 0:
            return
        self._tokens = min(self.capacity, self._tokens + delta * self.rate)
        self._last = now

    async def acquire(self, tokens: float = 1.0) -> None:
        """Wait until `tokens` tokens are available."""

        while True:
            async with self._lock:
                self._refill()
                if self._tokens >= tokens:
                    self._tokens -= tokens
                    return
                missing = tokens - self._tokens
                wait = missing / self.rate
            await asyncio.sleep(min(wait, 5.0))

    def try_acquire(self, tokens: float = 1.0) -> bool:
        """Non-blocking attempt to consume tokens."""

        self._refill()
        if self._tokens >= tokens:
            self._tokens -= tokens
            return True
        return False


# ============================================================================
# CIRCUIT BREAKER
# ============================================================================


class CircuitState(str, Enum):
    CLOSED = "closed"
    OPEN = "open"
    HALF_OPEN = "half_open"


class CircuitBreaker:
    """Standard three-state circuit breaker."""

    def __init__(
        self,
        *,
        failure_threshold: int = 5,
        recovery_timeout: float = 30.0,
        half_open_successes: int = 2,
    ) -> None:
        self.failure_threshold = failure_threshold
        self.recovery_timeout = recovery_timeout
        self.half_open_successes = half_open_successes

        self.state = CircuitState.CLOSED
        self._failures = 0
        self._successes = 0
        self._opened_at = 0.0
        self._lock = asyncio.Lock()

    async def allow(self) -> bool:
        """Return True if the call is allowed to proceed."""

        async with self._lock:
            if self.state == CircuitState.CLOSED:
                return True
            if self.state == CircuitState.OPEN:
                if unix_ts() - self._opened_at >= self.recovery_timeout:
                    self.state = CircuitState.HALF_OPEN
                    self._successes = 0
                    return True
                return False
            # HALF_OPEN
            return True

    async def record_success(self) -> None:
        """Record success; possibly transition back to CLOSED."""

        async with self._lock:
            if self.state == CircuitState.HALF_OPEN:
                self._successes += 1
                if self._successes >= self.half_open_successes:
                    self.state = CircuitState.CLOSED
                    self._failures = 0
                    self._successes = 0
            else:
                self._failures = 0

    async def record_failure(self) -> None:
        """Record failure; possibly OPEN the circuit."""

        async with self._lock:
            self._failures += 1
            if self.state == CircuitState.HALF_OPEN:
                self.state = CircuitState.OPEN
                self._opened_at = unix_ts()
                return
            if self._failures >= self.failure_threshold:
                self.state = CircuitState.OPEN
                self._opened_at = unix_ts()


# ============================================================================
# RETRY WITH EXPONENTIAL BACKOFF + JITTER
# ============================================================================


async def retry_async(
    fn: Callable[[], Awaitable[T]],
    *,
    attempts: int = 4,
    base_delay: float = 0.4,
    max_delay: float = 8.0,
    jitter: float = 0.3,
    retry_on: Tuple[Type[BaseException], ...] = (Exception,),
    on_giveup: Optional[Callable[[BaseException], None]] = None,
) -> T:
    """Retry an async function with exponential backoff and jitter."""

    last_exc: Optional[BaseException] = None
    for attempt in range(1, attempts + 1):
        try:
            return await fn()
        except retry_on as exc:
            last_exc = exc
            if attempt >= attempts:
                break
            delay = min(max_delay, base_delay * (2 ** (attempt - 1)))
            delay *= 1.0 + random.uniform(-jitter, jitter)
            await asyncio.sleep(max(0.0, delay))
    if on_giveup and last_exc:
        on_giveup(last_exc)
    assert last_exc is not None
    raise last_exc


# ============================================================================
# CONFIG
# ============================================================================


class TelegramConfig(BaseModel):
    """Telegram control-plane configuration."""

    model_config = ConfigDict(extra="forbid")

    token: str = Field(default="", description="Bot token from @BotFather.")
    allowed_chat_ids: List[int] = Field(default_factory=list)

    @field_validator("token")
    @classmethod
    def _token_shape(cls, value: str) -> str:
        value = value.strip()
        if not value:
            return value
        # Telegram tokens are "<digits>:<base64ish>"
        if ":" not in value:
            raise ValueError("Telegram token must contain ':'")
        head, _, tail = value.partition(":")
        if not head.isdigit():
            raise ValueError("Telegram token prefix must be numeric")
        if len(tail) < 20:
            raise ValueError("Telegram token suffix looks truncated")
        return value


class ScraperConfig(BaseModel):
    """Scraper tuning knobs."""

    model_config = ConfigDict(extra="forbid")

    workers: int = Field(default=100, ge=1, le=500)
    default_pages: int = Field(default=YAHOO_DEFAULT_PAGES, ge=1, le=YAHOO_MAX_PAGES)
    max_pages: int = Field(default=YAHOO_MAX_PAGES, ge=1, le=YAHOO_MAX_PAGES)
    request_timeout: float = Field(default=12.0, gt=0.5, le=120.0)
    jitter_min: float = Field(default=0.4, ge=0.0, le=10.0)
    jitter_max: float = Field(default=2.1, ge=0.0, le=20.0)
    burst_every: int = Field(default=20, ge=1)
    burst_sleep_min: float = Field(default=3.0, ge=0.0)
    burst_sleep_max: float = Field(default=7.0, ge=0.0)
    telemetry_interval: float = Field(default=10.0, gt=1.0, le=600.0)
    result_batch_size: int = Field(default=500, ge=10, le=10000)
    result_flush_interval: float = Field(default=2.0, gt=0.1, le=60.0)
    proxy_health_concurrency: int = Field(default=50, ge=1, le=500)
    proxy_health_timeout: float = Field(default=5.0, gt=1.0, le=60.0)
    proxy_block_window: float = Field(default=60.0, gt=1.0)
    proxy_block_threshold: int = Field(default=3, ge=1)
    proxy_cooldown: float = Field(default=300.0, gt=1.0)
    job_max_attempts: int = Field(default=2, ge=1, le=10)
    empty_pages_per_dork: int = Field(default=3, ge=1, le=10)

    @model_validator(mode="after")
    def _check_ranges(self) -> "ScraperConfig":
        if self.jitter_min > self.jitter_max:
            raise ValueError("jitter_min cannot exceed jitter_max")
        if self.burst_sleep_min > self.burst_sleep_max:
            raise ValueError("burst_sleep_min cannot exceed burst_sleep_max")
        if self.default_pages > self.max_pages:
            raise ValueError("default_pages cannot exceed max_pages")
        return self


class PathsConfig(BaseModel):
    """Filesystem paths used by the parser."""

    model_config = ConfigDict(extra="forbid")

    dorks: Path = Field(default=Path("data/dorks.txt"))
    proxies: Path = Field(default=Path("data/proxies.txt"))
    output: Path = Field(default=Path("data/output.txt"))
    dedup_db: Path = Field(default=Path("data/urls.db"))
    log_file: Optional[Path] = Field(default=Path("data/parser.log"))

    @field_validator("dorks", "proxies", "output", "dedup_db", "log_file", mode="before")
    @classmethod
    def _coerce(cls, value: Any) -> Any:
        if value is None:
            return None
        return Path(str(value))


class LoggingConfig(BaseModel):
    """Logging configuration."""

    model_config = ConfigDict(extra="forbid")

    level: str = Field(default="INFO")
    json_mode: bool = Field(default=False)

    @field_validator("level")
    @classmethod
    def _validate_level(cls, value: str) -> str:
        value = value.upper()
        if value not in {"DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"}:
            raise ValueError(f"Unsupported log level: {value}")
        return value


class Config(BaseModel):
    """Root configuration object."""

    model_config = ConfigDict(extra="forbid")

    telegram: TelegramConfig = Field(default_factory=TelegramConfig)
    scraper: ScraperConfig = Field(default_factory=ScraperConfig)
    paths: PathsConfig = Field(default_factory=PathsConfig)
    logging: LoggingConfig = Field(default_factory=LoggingConfig)


def _ensure_parent_dirs(paths: PathsConfig) -> None:
    """Create parent directories for all configured paths."""

    for path in (paths.dorks, paths.proxies, paths.output, paths.dedup_db, paths.log_file):
        if path is None:
            continue
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            raise ConfigError(f"Cannot create parent dir for {path}: {exc}") from exc


def load_config(path: Union[str, Path] = DEFAULT_CONFIG_PATH) -> Config:
    """Load config from YAML; raise ConfigError on failure."""

    path = Path(path)
    if not path.exists():
        raise ConfigError(f"Config file not found: {path}")

    try:
        raw = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise ConfigError(f"Malformed YAML in {path}: {exc}") from exc

    if not isinstance(raw, dict):
        raise ConfigError(f"Config root must be a mapping, got {type(raw).__name__}")

    try:
        config = Config.model_validate(raw)
    except ValidationError as exc:
        raise ConfigError(f"Invalid config:\n{exc}") from exc

    _ensure_parent_dirs(config.paths)
    return config


# ============================================================================
# PROXY POOL
# ============================================================================


class ProxyPool:
    """Concurrency-safe pool of proxies with health tracking."""

    def __init__(
        self,
        *,
        block_window: float = 60.0,
        block_threshold: int = 3,
        cooldown: float = 300.0,
    ) -> None:
        self._proxies: List[Proxy] = []
        self._lock = asyncio.Lock()
        self._cursor = 0
        self.block_window = block_window
        self.block_threshold = block_threshold
        self.cooldown = cooldown

        # counters
        self.total_acquired = 0
        self.total_blocks = 0
        self.total_successes = 0
        self.total_failures = 0

    # ----- loading -----

    @staticmethod
    def _parse_line(line: str) -> Optional[Proxy]:
        line = line.strip()
        if not line or line.startswith("#"):
            return None

        scheme = "http"
        if "://" in line:
            scheme, _, rest = line.partition("://")
            scheme = scheme.lower()
        else:
            rest = line

        username = password = None
        if "@" in rest:
            creds, _, rest = rest.rpartition("@")
            if ":" in creds:
                username, _, password = creds.partition(":")

        host, _, port_s = rest.rpartition(":")
        if not host:
            host, port_s = rest, "8080"
        try:
            port = int(port_s)
        except ValueError:
            return None
        if not host or not (0 < port < 65536):
            return None

        return Proxy(
            raw=line,
            scheme=scheme,
            host=host,
            port=port,
            username=username,
            password=password,
        )

    def load_from_file(self, path: Union[str, Path]) -> int:
        """Load proxies from a text file. Returns count loaded."""

        path = Path(path)
        if not path.exists():
            LOG.warning("Proxy file %s does not exist; pool will be empty", path)
            return 0

        proxies: List[Proxy] = []
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            proxy = self._parse_line(line)
            if proxy is not None:
                proxies.append(proxy)

        # Deduplicate by key while preserving order.
        seen: Set[str] = set()
        unique: List[Proxy] = []
        for proxy in proxies:
            if proxy.key in seen:
                continue
            seen.add(proxy.key)
            unique.append(proxy)

        self._proxies = unique
        LOG.info("Loaded %d proxies from %s", len(unique), path)
        return len(unique)

    # ----- health -----

    async def health_check(
        self,
        *,
        concurrency: int = 50,
        timeout: float = 5.0,
        probe_url: str = "https://search.yahoo.com/robots.txt",
    ) -> Tuple[int, int]:
        """Filter out dead proxies. Returns (alive, dead)."""

        if not self._proxies:
            return (0, 0)

        semaphore = asyncio.Semaphore(max(1, concurrency))
        results: List[bool] = []

        async def probe(proxy: Proxy) -> bool:
            async with semaphore:
                try:
                    session = AsyncSession(
                        impersonate="chrome120",
                        timeout=timeout,
                        proxies={"https": proxy.url, "http": proxy.url},
                    )
                    try:
                        resp = await session.get(probe_url)
                        ok = resp.status_code < 500
                    finally:
                        await session.close()
                    return ok
                except Exception as exc:  # noqa: BLE001
                    LOG.debug("Proxy %s failed health check: %s", proxy.key, exc)
                    return False

        coros = [probe(p) for p in self._proxies]
        results = await asyncio.gather(*coros)

        alive = 0
        dead = 0
        for proxy, ok in zip(self._proxies, results):
            proxy.alive = bool(ok)
            if ok:
                alive += 1
            else:
                dead += 1

        self._proxies = [p for p in self._proxies if p.alive]
        LOG.info("Proxy health: %d alive, %d dropped", alive, dead)
        return (alive, dead)

    # ----- acquire / release -----

    async def acquire(self) -> Proxy:
        """Return an available proxy, rotating round-robin."""

        async with self._lock:
            if not self._proxies:
                raise ProxyExhaustedError("No proxies in pool")
            now = unix_ts()
            n = len(self._proxies)
            for offset in range(n):
                idx = (self._cursor + offset) % n
                proxy = self._proxies[idx]
                if proxy.is_available(now):
                    self._cursor = (idx + 1) % n
                    self.total_acquired += 1
                    return proxy
        raise ProxyExhaustedError("All proxies in cooldown")

    async def report_block(self, proxy: Proxy) -> None:
        """Record a block against a proxy."""

        async with self._lock:
            proxy.record_block(
                window=self.block_window,
                threshold=self.block_threshold,
                cooldown=self.cooldown,
            )
            self.total_blocks += 1

    async def report_success(self, proxy: Proxy) -> None:
        """Record success against a proxy."""

        async with self._lock:
            proxy.record_success()
            self.total_successes += 1

    async def report_failure(self, proxy: Proxy, error: Optional[str] = None) -> None:
        """Record a generic failure against a proxy."""

        async with self._lock:
            proxy.record_failure(error)
            self.total_failures += 1

    # ----- info -----

    def stats(self) -> Dict[str, Any]:
        """Return pool statistics snapshot."""

        now = unix_ts()
        alive = sum(1 for p in self._proxies if p.alive)
        cooldown = sum(1 for p in self._proxies if p.alive and not p.is_available(now))
        return {
            "total": len(self._proxies),
            "alive": alive,
            "cooldown": cooldown,
            "acquired": self.total_acquired,
            "blocks": self.total_blocks,
            "successes": self.total_successes,
            "failures": self.total_failures,
        }

    def __len__(self) -> int:
        return len(self._proxies)

    @property
    def empty(self) -> bool:
        return not self._proxies


# ============================================================================
# YAHOO URL BUILDER + BLOCK CLASSIFIER
# ============================================================================


class YahooClient:
    """Static helpers for building URLs and detecting blocks."""

    @staticmethod
    def build_url(dork: str, page: int, *, lang: str = "en") -> str:
        """Build a Yahoo search URL for a dork at a given page (1-indexed)."""

        page = max(1, int(page))
        b = YAHOO_RESULTS_PER_PAGE * (page - 1) + 1
        params = {
            "p": dork,
            "b": str(b),
            "pz": str(YAHOO_RESULTS_PER_PAGE),
            "ei": "UTF-8",
        }
        return f"{YAHOO_SEARCH_BASE}?{urllib.parse.urlencode(params)}"

    @staticmethod
    def detect_block(status: int, html: str, *, elapsed: float = 0.0) -> BlockType:
        """Classify a Yahoo response into a BlockType."""

        if status == 0:
            return BlockType.NETWORK_ERROR
        if status == 429:
            return BlockType.RATE_LIMIT
        if status in (401, 403):
            return BlockType.HARD_BLOCK
        if status >= 500:
            return BlockType.SOFT_BLOCK

        if html is None:
            return BlockType.UNKNOWN

        html_len = len(html)

        if html_len < 2500:
            # Empty responses often indicate a soft block or a rate limit landing page.
            return BlockType.SOFT_BLOCK

        head = html[:4000].lower()

        if "verify you are human" in head or "captcha" in head and "g-recaptcha" in head:
            return BlockType.CAPTCHA
        if "are you a robot" in head or "unusual traffic" in head:
            return BlockType.CAPTCHA
        if "/consent" in head or "before you continue" in head or "guce.yahoo.com" in head:
            return BlockType.CONSENT
        if "too many requests" in head:
            return BlockType.RATE_LIMIT
        if "access denied" in head or "you don't have permission" in head:
            return BlockType.HARD_BLOCK

        # Real results pages contain the .algo class and RU= redirect links.
        has_algo = ("class=\"algo" in html) or ("class='algo" in html)
        has_ru = ("/RU=" in html) or ("RU=http" in html)

        if not has_algo and not has_ru:
            return BlockType.SOFT_BLOCK

        if has_algo and not has_ru:
            # Results present but no extractable redirects -> likely a "no results" page.
            return BlockType.EMPTY

        return BlockType.OK

    @staticmethod
    def consent_cookies() -> Dict[str, str]:
        """Return cookies to set for consent bypass."""

        return {YAHOO_CONSENT_COOKIE_NAME: YAHOO_CONSENT_COOKIE_VALUE}


# ============================================================================
# HTML PARSER / URL EXTRACTOR
# ============================================================================


class YahooParser:
    """Extract result URLs from a Yahoo SERP HTML document."""

    RESULT_SELECTORS: ClassVar[Tuple[str, ...]] = (
        "div.algo h3 a",
        "div.dd.algo h3 a",
        "div.algo h3.title a",
        "div#web h3.title a",
        "h3.title a",
    )

    @classmethod
    def extract_urls(cls, html: str) -> List[str]:
        """Return a list of target URLs from Yahoo result HTML."""

        if not html:
            return []

        urls: List[str] = []
        seen: Set[str] = set()

        # Primary path: DOM parsing.
        try:
            soup = BeautifulSoup(html, "lxml")
        except Exception:
            soup = None

        if soup is not None:
            for selector in cls.RESULT_SELECTORS:
                for anchor in soup.select(selector):
                    href = anchor.get("href")
                    if not href:
                        continue
                    target = cls._decode_redirect(href)
                    if target and target not in seen:
                        seen.add(target)
                        urls.append(target)

        # Fallback: regex against raw HTML.
        if not urls:
            for match in YAHOO_REDIRECT_RE.finditer(html):
                raw = match.group(1)
                target = cls._safe_unquote(raw)
                if is_url_like(target) and target not in seen:
                    seen.add(target)
                    urls.append(target)

            for match in YAHOO_REDIRECT_RE_ALT.finditer(html):
                raw = match.group(1)
                target = cls._safe_unquote(raw)
                if is_url_like(target) and target not in seen:
                    seen.add(target)
                    urls.append(target)

        return urls

    @staticmethod
    def _decode_redirect(href: str) -> Optional[str]:
        """Pull the target URL out of a Yahoo redirect wrapper."""

        if not href:
            return None

        # Absolute wrappers look like /RU=<encoded>/RK=...
        match = YAHOO_REDIRECT_RE.search(href)
        if match:
            candidate = YahooParser._safe_unquote(match.group(1))
            if is_url_like(candidate):
                return candidate

        match = YAHOO_REDIRECT_RE_ALT.search(href)
        if match:
            candidate = YahooParser._safe_unquote(match.group(1))
            if is_url_like(candidate):
                return candidate

        # Some Yahoo variants pass through the target directly.
        if is_url_like(href):
            return href

        # Relative URL on Yahoo's own domain: reject.
        return None

    @staticmethod
    def _safe_unquote(raw: str) -> str:
        """URL-decode with a couple of retries on double-encoding."""

        if not raw:
            return ""
        try:
            decoded = urllib.parse.unquote(raw)
            if "%" in decoded and len(decoded) > 20:
                # Try one more pass for double-encoded values.
                decoded2 = urllib.parse.unquote(decoded)
                if is_url_like(decoded2):
                    return decoded2
            return decoded
        except Exception:
            return raw

    @staticmethod
    def normalize_url(url: str) -> str:
        """Normalize a URL for dedup and output."""

        if not url:
            return ""
        try:
            parts = urllib.parse.urlsplit(url.strip())
        except ValueError:
            return ""

        scheme = parts.scheme.lower()
        netloc = parts.netloc.lower()
        path = parts.path or "/"

        # Preserve query, drop fragment.
        query = parts.query

        # Strip default ports.
        if netloc.endswith(":80") and scheme == "http":
            netloc = netloc[:-3]
        elif netloc.endswith(":443") and scheme == "https":
            netloc = netloc[:-4]

        # Strip trailing slash on root path only.
        if path == "/":
            path = "/"

        return urllib.parse.urlunsplit((scheme, netloc, path, query, ""))

    @staticmethod
    def filter_urls(
        urls: Iterable[str],
        *,
        blocklist_domains: Iterable[str] = YAHOO_INTERNAL_HOSTS,
        min_host_len: int = 3,
    ) -> List[str]:
        """Drop Yahoo-internal and obviously-bad URLs."""

        blocked = {d.lower().strip(".") for d in blocklist_domains if d}
        out: List[str] = []
        for url in urls:
            host = safe_domain(url)
            if not host or len(host) < min_host_len:
                continue
            if any(host == d or host.endswith("." + d) for d in blocked):
                continue
            out.append(url)
        return out


# ============================================================================
# DEDUP STORE
# ============================================================================


class DedupStore:
    """Async SQLite-backed deduplication store with WAL mode."""

    SCHEMA: ClassVar[str] = (
        "CREATE TABLE IF NOT EXISTS seen ("
        "  h TEXT PRIMARY KEY,"
        "  url TEXT NOT NULL,"
        "  ts INTEGER NOT NULL"
        ")"
    )
    INDEX: ClassVar[str] = "CREATE INDEX IF NOT EXISTS seen_ts ON seen(ts)"

    def __init__(self, db_path: Union[str, Path], *, use_bloom: bool = False) -> None:
        self.db_path = Path(db_path)
        self._conn: Optional[aiosqlite.Connection] = None
        self._lock = asyncio.Lock()
        self._inserted = 0
        self._checked = 0
        self._use_bloom = use_bloom
        self._bloom: Optional["_SimpleBloom"] = None
        if use_bloom:
            self._bloom = _SimpleBloom(capacity=5_000_000, error_rate=0.001)

    async def open(self) -> None:
        """Open the database and configure pragmas."""

        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        conn = await aiosqlite.connect(self.db_path)
        try:
            await conn.execute("PRAGMA journal_mode=WAL")
            await conn.execute("PRAGMA synchronous=NORMAL")
            await conn.execute("PRAGMA temp_store=MEMORY")
            await conn.execute(self.SCHEMA)
            await conn.execute(self.INDEX)
            await conn.commit()
        except Exception:
            await conn.close()
            raise
        self._conn = conn
        LOG.info("Dedup store opened: %s", self.db_path)

    async def close(self) -> None:
        """Close the database connection cleanly."""

        if self._conn is not None:
            with contextlib.suppress(Exception):
                await self._conn.commit()
            with contextlib.suppress(Exception):
                await self._conn.close()
            self._conn = None

    async def is_new(self, url: str) -> bool:
        """Return True if URL was not previously seen, and insert it."""

        if not url:
            return False
        normalized = YahooParser.normalize_url(url)
        if not normalized:
            return False
        digest = sha1_hex(normalized)

        if self._bloom is not None:
            if digest in self._bloom:
                return False
            self._bloom.add(digest)

        async with self._lock:
            if self._conn is None:
                raise DedupError("Dedup store not opened")
            self._checked += 1
            cursor = await self._conn.execute(
                "INSERT OR IGNORE INTO seen (h, url, ts) VALUES (?, ?, ?)",
                (digest, normalized, int(time.time())),
            )
            inserted = cursor.rowcount or 0
            await self._conn.commit()
            if inserted:
                self._inserted += 1
            return bool(inserted)

    async def filter_new(self, urls: Sequence[str]) -> List[str]:
        """Return only URLs that were not previously seen."""

        if not urls:
            return []
        out: List[str] = []
        for url in urls:
            if await self.is_new(url):
                out.append(url)
        return out

    @property
    def inserted(self) -> int:
        return self._inserted

    @property
    def checked(self) -> int:
        return self._checked


class _SimpleBloom:
    """A small, dependency-free bloom filter.

    Not as tight as pybloom-live, but has zero external dependencies and
    is plenty for our false-positive budget when combined with SQLite.
    """

    def __init__(self, *, capacity: int, error_rate: float) -> None:
        capacity = max(1024, int(capacity))
        error_rate = min(max(error_rate, 1e-6), 0.5)
        # Optimal number of bits (m) and hash functions (k).
        m = int(math.ceil(-(capacity * math.log(error_rate)) / (math.log(2) ** 2)))
        k = int(math.ceil((m / capacity) * math.log(2)))
        self.m = m
        self.k = max(1, k)
        self.bits = bytearray((m + 7) // 8)
        self._lock = asyncio.Lock()

    def _hashes(self, key: str) -> Iterator[int]:
        # Double hashing: h_i(x) = h1(x) + i * h2(x)
        h1 = int.from_bytes(hashlib.md5(key.encode()).digest()[:8], "big")
        h2 = int.from_bytes(hashlib.sha1(key.encode()).digest()[:8], "big")
        for i in range(self.k):
            yield (h1 + i * h2) % self.m

    def add(self, key: str) -> None:
        for idx in self._hashes(key):
            self.bits[idx >> 3] |= (1 << (idx & 7))

    def __contains__(self, key: str) -> bool:
        for idx in self._hashes(key):
            if not (self.bits[idx >> 3] & (1 << (idx & 7))):
                return False
        return True


# ============================================================================
# OUTPUT WRITER
# ============================================================================


class OutputWriter:
    """Batched, crash-safe append-only URL writer."""

    def __init__(
        self,
        path: Union[str, Path],
        *,
        batch_size: int = 500,
        flush_interval: float = 2.0,
    ) -> None:
        self.path = Path(path)
        self.batch_size = max(1, int(batch_size))
        self.flush_interval = max(0.1, float(flush_interval))

        self._buffer: List[str] = []
        self._lock = asyncio.Lock()
        self._fh: Optional[io.TextIOBase] = None
        self._written = 0
        self._last_flush = unix_ts()
        self._running = False
        self._flusher_task: Optional[asyncio.Task[Any]] = None

    async def start(self) -> None:
        """Open the output file and start the background flusher."""

        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fh = self.path.open("a", encoding="utf-8", buffering=64 * 1024)
        self._running = True
        self._flusher_task = asyncio.create_task(self._flusher_loop(), name="writer-flusher")
        LOG.info("Output writer opened: %s", self.path)

    async def stop(self) -> None:
        """Flush remaining buffer and close."""

        self._running = False
        if self._flusher_task is not None:
            await cancel_task(self._flusher_task)
            self._flusher_task = None
        async with self._lock:
            self._flush_locked()
            if self._fh is not None:
                with contextlib.suppress(Exception):
                    self._fh.flush()
                    os.fsync(self._fh.fileno())
                    self._fh.close()
                self._fh = None
        LOG.info("Output writer closed (%d lines written)", self._written)

    async def write(self, url: str) -> None:
        """Buffer a URL for output."""

        if not url:
            return
        async with self._lock:
            self._buffer.append(url)
            if len(self._buffer) >= self.batch_size:
                self._flush_locked()

    async def write_many(self, urls: Iterable[str]) -> None:
        """Buffer multiple URLs at once."""

        async with self._lock:
            self._buffer.extend(u for u in urls if u)
            if len(self._buffer) >= self.batch_size:
                self._flush_locked()

    def _flush_locked(self) -> None:
        """Internal: flush while holding the lock."""

        if not self._buffer or self._fh is None:
            return
        try:
            for url in self._buffer:
                self._fh.write(url + "\n")
            self._fh.flush()
            try:
                os.fsync(self._fh.fileno())
            except OSError:
                pass
            self._written += len(self._buffer)
            self._buffer.clear()
            self._last_flush = unix_ts()
        except Exception as exc:  # noqa: BLE001
            LOG.error("Output flush failed: %s", exc)
            raise WriterError(str(exc)) from exc

    async def _flusher_loop(self) -> None:
        """Periodic flusher."""

        while self._running:
            try:
                await asyncio.sleep(self.flush_interval)
                async with self._lock:
                    self._flush_locked()
            except asyncio.CancelledError:
                break
            except Exception as exc:  # noqa: BLE001
                LOG.error("Flusher loop error: %s", exc)

    @property
    def written(self) -> int:
        return self._written


# ============================================================================
# STATS AGGREGATOR
# ============================================================================


class Stats:
    """Rolling counters and rate calculations for the engine."""

    def __init__(self) -> None:
        self.start_time = unix_ts()
        self.req_total = 0
        self.req_ok = 0
        self.req_blocked = 0
        self.req_empty = 0
        self.req_failed = 0
        self.urls_found = 0
        self.urls_new = 0
        self.dorks_done = 0
        self.jobs_requeued = 0
        self.jobs_dropped = 0
        self.workers_alive = 0
        self.workers_spawned = 0
        self.rotations = 0

        self._recent_requests: Deque[Tuple[float, bool]] = deque(maxlen=4096)
        self._recent_blocks: Deque[float] = deque(maxlen=2048)
        self._lock = asyncio.Lock()

    async def record_request(self, *, ok: bool, blocked: bool = False) -> None:
        async with self._lock:
            self.req_total += 1
            if ok:
                self.req_ok += 1
            if blocked:
                self.req_blocked += 1
                self._recent_blocks.append(unix_ts())
            self._recent_requests.append((unix_ts(), ok))

    async def record_urls(self, total: int, new: int) -> None:
        async with self._lock:
            self.urls_found += total
            self.urls_new += new

    async def record_dork_done(self) -> None:
        async with self._lock:
            self.dorks_done += 1

    async def record_requeue(self) -> None:
        async with self._lock:
            self.jobs_requeued += 1

    async def record_drop(self) -> None:
        async with self._lock:
            self.jobs_dropped += 1

    async def record_rotation(self) -> None:
        async with self._lock:
            self.rotations += 1

    def _rate(self, values: Deque[Any], window: float) -> float:
        if not values:
            return 0.0
        now = unix_ts()
        cutoff = now - window
        recent = [v for v in values if (v[0] if isinstance(v, tuple) else v) >= cutoff]
        if not recent:
            return 0.0
        return len(recent) / window

    def requests_per_second(self) -> float:
        return self._rate(self._recent_requests, 10.0)

    def blocks_per_minute(self) -> float:
        return self._rate(self._recent_blocks, 60.0) * 60.0

    def elapsed(self) -> float:
        return unix_ts() - self.start_time

    def snapshot(self) -> Dict[str, Any]:
        return {
            "uptime": self.elapsed(),
            "req_total": self.req_total,
            "req_ok": self.req_ok,
            "req_blocked": self.req_blocked,
            "req_empty": self.req_empty,
            "req_failed": self.req_failed,
            "urls_found": self.urls_found,
            "urls_new": self.urls_new,
            "dorks_done": self.dorks_done,
            "jobs_requeued": self.jobs_requeued,
            "jobs_dropped": self.jobs_dropped,
            "workers_alive": self.workers_alive,
            "workers_spawned": self.workers_spawned,
            "rotations": self.rotations,
            "rps": self.requests_per_second(),
            "bpm": self.blocks_per_minute(),
        }


# ============================================================================
# WORKER
# ============================================================================


class Worker:
    """A single scraping worker with its own identity and lifecycle."""

    def __init__(
        self,
        worker_id: int,
        engine: "Engine",
        *,
        proxy_pool: ProxyPool,
        stats: Stats,
    ) -> None:
        self.worker_id = worker_id
        self.engine = engine
        self.proxy_pool = proxy_pool
        self.stats = stats

        self.session: Optional[AsyncSession] = None
        self.profile: BrowserProfile = pick_profile()
        self.proxy: Optional[Proxy] = None

        self._burst_counter = 0
        self._stop = asyncio.Event()
        self._broken = False
        self._task: Optional[asyncio.Task[Any]] = None

    # ----- lifecycle -----

    async def start(self) -> None:
        """Create the initial HTTP session and proxy binding."""

        self.profile = pick_profile()
        await self._new_session()
        self._task = asyncio.create_task(self._run_loop(), name=f"worker-{self.worker_id}")

    async def stop(self) -> None:
        """Stop the worker and close its session."""

        self._stop.set()
        if self._task is not None:
            await cancel_task(self._task)
            self._task = None
        await self._close_session()

    @property
    def broken(self) -> bool:
        return self._broken

    @property
    def alive(self) -> bool:
        return self._task is not None and not self._task.done() and not self._broken

    # ----- session / identity -----

    async def _new_session(self) -> None:
        """Create a fresh AsyncSession with the current identity."""

        await self._close_session()
        proxy_url = self.proxy.url if self.proxy is not None else None
        proxies = {"http": proxy_url, "https": proxy_url} if proxy_url else None
        headers = self.profile.as_headers()
        # curl_cffi's impersonate= controls TLS fingerprint and default header order.
        # We add only the headers that impersonate doesn't already set consistently.
        session = AsyncSession(
            impersonate=self.profile.impersonate,
            timeout=self.engine.config.scraper.request_timeout,
            proxies=proxies,
            headers=headers,
            default_headers=True,
        )
        self.session = session

    async def _close_session(self) -> None:
        if self.session is not None:
            with contextlib.suppress(Exception):
                await self.session.close()
            self.session = None

    async def _rotate_identity(self) -> None:
        """Full identity reset: new proxy, new profile, new session."""

        # Release current proxy.
        if self.proxy is not None:
            with contextlib.suppress(Exception):
                await self.proxy_pool.report_failure(self.proxy, "identity-rotate")

        # Pick a new one.
        try:
            self.proxy = await self.proxy_pool.acquire()
        except ProxyExhaustedError:
            self.proxy = None

        self.profile = rotate_profile(self.profile)
        await self._new_session()
        await self.stats.record_rotation()

        LOG.debug(
            "worker %d rotated identity: profile=%s proxy=%s",
            self.worker_id,
            self.profile.name,
            self.proxy.key if self.proxy else "none",
        )

    # ----- main loop -----

    async def _run_loop(self) -> None:
        try:
            while not self._stop.is_set():
                if self.engine.paused:
                    await asyncio.sleep(0.5)
                    continue

                job = await self.engine.next_job(timeout=2.0)
                if job is None:
                    if self.engine.queue_empty and not self.engine.running:
                        break
                    continue

                await self._handle_job(job)

        except asyncio.CancelledError:
            pass
        except Exception as exc:  # noqa: BLE001
            self._broken = True
            LOG.exception("worker %d crashed: %s", self.worker_id, exc)

    async def _handle_job(self, job: DorkJob) -> None:
        try:
            await self._burst_breathe()

            # Jitter before every request.
            jitter = random.uniform(
                self.engine.config.scraper.jitter_min,
                self.engine.config.scraper.jitter_max,
            )
            await asyncio.sleep(jitter)

            result = await self._fetch(job.dork, job.page)

            if result.block == BlockType.OK:
                await self._on_ok(job, result)
                return

            if result.block == BlockType.EMPTY:
                self.stats.req_empty += 1
                await self.engine.note_empty_page(job)
                await self.stats.record_request(ok=True)
                return

            if result.block == BlockType.CONSENT:
                # Retry once with consent cookie.
                if job.attempts < self.engine.config.scraper.job_max_attempts:
                    await self._apply_consent_cookie()
                    job.attempts += 1
                    await self.engine.requeue(job)
                    await self.stats.record_requeue()
                    await self.stats.record_request(ok=False, blocked=True)
                    return
                await self.engine.drop(job)
                await self.stats.record_drop()
                return

            # Blocked or failed - requeue once, then drop.
            await self.stats.record_request(ok=False, blocked=True)
            if job.attempts < self.engine.config.scraper.job_max_attempts:
                job.attempts += 1
                await self.engine.requeue(job)
                await self.stats.record_requeue()
            else:
                await self.engine.drop(job)
                await self.stats.record_drop()
                self.stats.req_failed += 1

            await self._rotate_identity()

        except Exception as exc:  # noqa: BLE001
            LOG.warning("worker %d job error: %s", self.worker_id, exc)
            await self.stats.record_request(ok=False)
            self.stats.req_failed += 1

    async def _on_ok(self, job: DorkJob, result: FetchResult) -> None:
        await self.stats.record_request(ok=True)

        if self.proxy is not None:
            with contextlib.suppress(Exception):
                await self.proxy_pool.report_success(self.proxy)

        urls = YahooParser.filter_urls(result.urls)
        if not urls:
            # Page loaded but no extractable URLs - treat as empty for this page.
            await self.engine.note_empty_page(job)
            return

        new_urls = await self.engine.dedup_and_write(urls)
        await self.stats.record_urls(total=len(urls), new=len(new_urls))
        await self.engine.note_ok_page(job)

    async def _burst_breathe(self) -> None:
        self._burst_counter += 1
        if self._burst_counter % self.engine.config.scraper.burst_every == 0:
            sleep_for = random.uniform(
                self.engine.config.scraper.burst_sleep_min,
                self.engine.config.scraper.burst_sleep_max,
            )
            await asyncio.sleep(sleep_for)

    # ----- fetch -----

    async def _fetch(self, dork: str, page: int) -> FetchResult:
        url = YahooClient.build_url(dork, page)

        if self.session is None:
            await self._rotate_identity()
        if self.session is None:
            return FetchResult(url=url, status=0, block=BlockType.NETWORK_ERROR, html="")

        headers: Dict[str, str] = {}
        if page > 1:
            headers["Referer"] = YahooClient.build_url(dork, page - 1)

        start = unix_ts()
        status = 0
        html = ""
        error: Optional[str] = None

        try:
            resp = await self.session.get(url, headers=headers or None)
            status = int(resp.status_code)
            html = resp.text or ""
        except CurlError as exc:
            error = str(exc)
        except asyncio.TimeoutError:
            error = "timeout"
        except Exception as exc:  # noqa: BLE001
            error = str(exc)

        elapsed = unix_ts() - start

        if error:
            block = BlockType.TIMEOUT if error == "timeout" else BlockType.NETWORK_ERROR
            return FetchResult(
                url=url,
                status=status,
                block=block,
                html="",
                proxy_key=self.proxy.key if self.proxy else None,
                elapsed=elapsed,
                error=error,
            )

        block = YahooClient.detect_block(status, html, elapsed=elapsed)

        urls: List[str] = []
        if block == BlockType.OK:
            urls = YahooParser.extract_urls(html)
            if not urls:
                block = BlockType.EMPTY

        return FetchResult(
            url=url,
            status=status,
            block=block,
            html=html,
            urls=urls,
            proxy_key=self.proxy.key if self.proxy else None,
            elapsed=elapsed,
        )

    async def _apply_consent_cookie(self) -> None:
        if self.session is None:
            return
        try:
            for name, value in YahooClient.consent_cookies().items():
                self.session.cookies.set(name, value, domain=".yahoo.com")
        except Exception as exc:  # noqa: BLE001
            LOG.debug("worker %d failed to set consent cookie: %s", self.worker_id, exc)


# ============================================================================
# ENGINE
# ============================================================================


class Engine:
    """Top-level scraper engine coordinating workers, queues, and I/O."""

    def __init__(
        self,
        config: Config,
        *,
        proxy_pool: Optional[ProxyPool] = None,
        dedup: Optional[DedupStore] = None,
        writer: Optional[OutputWriter] = None,
    ) -> None:
        self.config = config
        self.stats = Stats()

        self.proxy_pool = proxy_pool or ProxyPool(
            block_window=config.scraper.proxy_block_window,
            block_threshold=config.scraper.proxy_block_threshold,
            cooldown=config.scraper.proxy_cooldown,
        )
        self.dedup = dedup or DedupStore(config.paths.dedup_db)
        self.writer = writer or OutputWriter(
            config.paths.output,
            batch_size=config.scraper.result_batch_size,
            flush_interval=config.scraper.result_flush_interval,
        )

        self._job_queue: "asyncio.Queue[DorkJob]" = asyncio.Queue()
        self._result_queue: "asyncio.Queue[List[str]]" = asyncio.Queue(maxsize=4096)

        self._workers: List[Worker] = []
        self._worker_tasks: List[asyncio.Task[Any]] = []
        self._result_task: Optional[asyncio.Task[Any]] = None
        self._supervisor_task: Optional[asyncio.Task[Any]] = None
        self._stats_task: Optional[asyncio.Task[Any]] = None

        self.pages_per_dork = config.scraper.default_pages
        self._dorks: List[str] = []
        self._empty_pages: Dict[str, Deque[int]] = defaultdict(lambda: deque(maxlen=16))
        self._dorks_completed: Set[str] = set()
        self._running = False
        self.paused = False
        self._stopping = False

    # ----- properties -----

    @property
    def running(self) -> bool:
        return self._running

    @property
    def queue_empty(self) -> bool:
        return self._job_queue.empty()

    @property
    def queue_size(self) -> int:
        return self._job_queue.qsize()

    @property
    def dorks(self) -> List[str]:
        return list(self._dorks)

    @property
    def dorks_completed(self) -> int:
        return len(self._dorks_completed)

    # ----- dork loading -----

    def load_dorks(self, path: Union[str, Path]) -> int:
        """Read dorks from a file. One per line; '#' starts a comment."""

        path = Path(path)
        if not path.exists():
            LOG.warning("Dork file %s does not exist", path)
            self._dorks = []
            return 0

        dorks: List[str] = []
        seen: Set[str] = set()
        for raw_line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            line = canonicalize_text(raw_line)
            if not line or line.startswith("#"):
                continue
            if line in seen:
                continue
            seen.add(line)
            dorks.append(line)

        self._dorks = dorks
        LOG.info("Loaded %d unique dorks from %s", len(dorks), path)
        return len(dorks)

    # ----- queue seeding -----

    async def seed_queue(self, pages: Optional[int] = None) -> int:
        """Seed the job queue with (dork, page) jobs for all dorks and pages."""

        if pages is None:
            pages = self.pages_per_dork
        pages = int(clamp(pages, 1, self.config.scraper.max_pages))

        count = 0
        # Shuffle a per-dork page order to reduce predictable patterns.
        for dork in self._dorks:
            if dork in self._dorks_completed:
                continue
            page_order = list(range(1, pages + 1))
            random.shuffle(page_order)
            for page in page_order:
                job = DorkJob(dork=dork, page=page)
                await self._job_queue.put(job)
                count += 1
        LOG.info("Seeded %d jobs (%d dorks x %d pages)", count, len(self._dorks), pages)
        return count

    async def next_job(self, *, timeout: float = 2.0) -> Optional[DorkJob]:
        """Pull the next job from the queue, or None on timeout."""

        try:
            return await asyncio.wait_for(self._job_queue.get(), timeout=timeout)
        except asyncio.TimeoutError:
            return None

    async def requeue(self, job: DorkJob) -> None:
        """Push a job back onto the queue."""

        await self._job_queue.put(job)

    async def drop(self, job: DorkJob) -> None:
        """Mark a job as dropped (for stats)."""

        LOG.debug("Dropped job: dork=%r page=%d attempts=%d",
                  job.dork, job.page, job.attempts)

    async def note_empty_page(self, job: DorkJob) -> None:
        """Track empty responses; mark a dork completed after N empties."""

        dq = self._empty_pages[job.dork]
        dq.append(job.page)
        if len(dq) >= self.config.scraper.empty_pages_per_dork:
            if job.dork not in self._dorks_completed:
                self._dorks_completed.add(job.dork)
                await self.stats.record_dork_done()

    async def note_ok_page(self, job: DorkJob) -> None:
        """Reset the empty counter for a dork when we get a good page."""

        self._empty_pages.pop(job.dork, None)

    # ----- dedup + write -----

    async def dedup_and_write(self, urls: Sequence[str]) -> List[str]:
        """Filter URLs through dedup and enqueue for writing."""

        new_urls = await self.dedup.filter_new(urls)
        if new_urls:
            try:
                await self._result_queue.put(new_urls)
            except asyncio.QueueFull:
                # Fall back to a direct write if the queue is backed up.
                await self.writer.write_many(new_urls)
        return new_urls

    # ----- result consumer -----

    async def _result_consumer(self) -> None:
        try:
            while not self._stopping:
                try:
                    batch = await asyncio.wait_for(self._result_queue.get(), timeout=1.0)
                except asyncio.TimeoutError:
                    continue
                await self.writer.write_many(batch)
        except asyncio.CancelledError:
            pass
        except Exception as exc:  # noqa: BLE001
            LOG.exception("result consumer crashed: %s", exc)

    # ----- supervisor -----

    async def _supervisor(self) -> None:
        """Ensure we always have N healthy workers."""

        target = self.config.scraper.workers
        try:
            while not self._stopping:
                await asyncio.sleep(2.0)
                if self.paused:
                    continue

                # Trim dead workers.
                live: List[Worker] = []
                for w in self._workers:
                    if w.alive:
                        live.append(w)
                    else:
                        with contextlib.suppress(Exception):
                            await w.stop()
                self._workers = live

                # Respawn missing ones.
                while len(self._workers) < target and not self._stopping:
                    wid = self.stats.workers_spawned
                    self.stats.workers_spawned += 1
                    worker = Worker(wid, self, proxy_pool=self.proxy_pool, stats=self.stats)
                    await worker.start()
                    self._workers.append(worker)
                    # Small stagger to avoid a thundering herd on startup.
                    await asyncio.sleep(0.02)

                self.stats.workers_alive = len(self._workers)
        except asyncio.CancelledError:
            pass
        except Exception as exc:  # noqa: BLE001
            LOG.exception("supervisor crashed: %s", exc)

    # ----- stats ticker -----

    async def _stats_ticker(self) -> None:
        try:
            while not self._stopping:
                await asyncio.sleep(1.0)
                self.stats.workers_alive = sum(1 for w in self._workers if w.alive)
        except asyncio.CancelledError:
            pass

    # ----- lifecycle -----

    async def start(self) -> None:
        """Bring up dedup, writer, workers, and the result consumer."""

        if self._running:
            LOG.warning("Engine is already running")
            return

        await self.dedup.open()
        await self.writer.start()

        self._running = True
        self._stopping = False

        self._result_task = asyncio.create_task(self._result_consumer(), name="result-consumer")
        self._supervisor_task = asyncio.create_task(self._supervisor(), name="supervisor")
        self._stats_task = asyncio.create_task(self._stats_ticker(), name="stats-ticker")

        if not self._dorks:
            LOG.warning("Engine started with no dorks loaded")

        LOG.info(
            "Engine started: workers=%d, pages_per_dork=%d, dorks=%d",
            self.config.scraper.workers,
            self.pages_per_dork,
            len(self._dorks),
        )

    async def stop(self) -> None:
        """Gracefully stop everything and flush output."""

        if self._stopping:
            return
        self._stopping = True
        self._running = False

        LOG.info("Engine stopping...")

        await cancel_task(self._supervisor_task)
        self._supervisor_task = None

        for worker in self._workers:
            with contextlib.suppress(Exception):
                await worker.stop()
        self._workers.clear()

        await cancel_task(self._stats_task)
        self._stats_task = None

        # Drain remaining results before shutting down the consumer.
        await asyncio.sleep(0.1)
        with contextlib.suppress(Exception):
            while not self._result_queue.empty():
                batch = self._result_queue.get_nowait()
                await self.writer.write_many(batch)

        await cancel_task(self._result_task)
        self._result_task = None

        await self.writer.stop()
        await self.dedup.close()

        LOG.info(
            "Engine stopped. urls_new=%d, req_total=%d, dorks_done=%d, uptime=%s",
            self.stats.urls_new,
            self.stats.req_total,
            self.stats.dorks_done,
            human_duration(self.stats.elapsed()),
        )

    # ----- runtime commands -----

    def set_pages(self, pages: int) -> int:
        """Change the pages-per-dork value. Returns the new clamped value."""

        pages = int(clamp(pages, 1, self.config.scraper.max_pages))
        self.pages_per_dork = pages
        LOG.info("pages_per_dork set to %d", pages)
        return pages

    async def pause(self) -> None:
        self.paused = True

    async def resume(self) -> None:
        self.paused = False

    async def force_rotate(self) -> None:
        for worker in list(self._workers):
            with contextlib.suppress(Exception):
                await worker._rotate_identity()

    async def clear_output(self) -> None:
        """Truncate the output file. Caller is responsible for safety."""

        if self.writer._fh is not None:  # noqa: SLF001
            with contextlib.suppress(Exception):
                self.writer._fh.flush()  # noqa: SLF001
        try:
            self.config.paths.output.write_text("", encoding="utf-8")
            LOG.info("Output file truncated: %s", self.config.paths.output)
        except OSError as exc:
            LOG.error("Failed to truncate output file: %s", exc)

    def snapshot(self) -> Dict[str, Any]:
        """Return a combined snapshot for Telegram reporting."""

        snap = self.stats.snapshot()
        snap["queue_size"] = self.queue_size
        snap["pages_per_dork"] = self.pages_per_dork
        snap["paused"] = self.paused
        snap["dorks_total"] = len(self._dorks)
        snap["dorks_completed"] = len(self._dorks_completed)
        snap["proxy"] = self.proxy_pool.stats()
        snap["writer_written"] = self.writer.written
        snap["dedup_inserted"] = self.dedup.inserted
        snap["dedup_checked"] = self.dedup.checked
        return snap


# ============================================================================
# TELEGRAM: AUTH MIDDLEWARE
# ============================================================================


class AuthMiddleware:
    """Reject messages from unauthorized chat IDs."""

    def __init__(self, allowed_ids: Iterable[int]) -> None:
        self.allowed = set(int(i) for i in allowed_ids)

    async def __call__(self, handler: Callable[..., Awaitable[Any]],
                       event: Any, data: Dict[str, Any]) -> Any:
        chat = None
        if hasattr(event, "chat") and event.chat is not None:
            chat = event.chat
        elif hasattr(event, "message") and event.message is not None:
            chat = event.message.chat
        if chat is None:
            return await handler(event, data)
        if self.allowed and chat.id not in self.allowed:
            LOG.warning("Rejected message from unauthorized chat_id=%s", chat.id)
            with contextlib.suppress(Exception):
                if isinstance(event, Message):
                    await event.reply("Unauthorized.")
                elif isinstance(event, CallbackQuery):
                    await event.answer("Unauthorized.", show_alert=True)
            return None
        return await handler(event, data)


# ============================================================================
# TELEGRAM: TELEMETRY
# ============================================================================


class TelemetryReporter:
    """Edits a live status message with engine stats."""

    def __init__(self, bot: Bot, engine: Engine, chat_id: int, interval: float = 10.0) -> None:
        self.bot = bot
        self.engine = engine
        self.chat_id = chat_id
        self.interval = max(1.0, float(interval))

        self._message_id: Optional[int] = None
        self._task: Optional[asyncio.Task[Any]] = None
        self._stop = asyncio.Event()

    async def start(self) -> None:
        """Post the initial status message and start the updater loop."""

        if self._task is not None:
            return
        self._stop.clear()
        try:
            msg = await self.bot.send_message(
                self.chat_id,
                self._render(),
                parse_mode=ParseMode.HTML,
            )
            self._message_id = msg.message_id
        except TelegramAPIError as exc:
            LOG.error("Telemetry: failed to post initial message: %s", exc)
            self._message_id = None
        self._task = asyncio.create_task(self._loop(), name="telemetry")

    async def stop(self) -> None:
        self._stop.set()
        if self._task is not None:
            await cancel_task(self._task)
            self._task = None

    async def _loop(self) -> None:
        try:
            while not self._stop.is_set():
                await asyncio.sleep(self.interval)
                if self._message_id is None:
                    continue
                try:
                    await self.bot.edit_message_text(
                        chat_id=self.chat_id,
                        message_id=self._message_id,
                        text=self._render(),
                        parse_mode=ParseMode.HTML,
                    )
                except TelegramAPIError as exc:
                    LOG.debug("Telemetry edit failed: %s", exc)
        except asyncio.CancelledError:
            pass

    def _render(self) -> str:
        snap = self.engine.snapshot()
        state = "paused" if snap["paused"] else ("running" if self.engine.running else "idle")
        lines = [
            f"<b>yahoo-dork-parser</b> — <code>{state}</code>",
            f"uptime      : {human_duration(snap['uptime'])}",
            f"workers     : {snap['workers_alive']}/{self.engine.config.scraper.workers}",
            f"queue       : {human_count(snap['queue_size'])} jobs",
            f"pages/dork  : {snap['pages_per_dork']}",
            f"req total   : {human_count(snap['req_total'])} "
            f"({snap['rps']:.1f}/s)",
            f"req ok      : {human_count(snap['req_ok'])}",
            f"blocked     : {human_count(snap['req_blocked'])} "
            f"({snap['bpm']:.1f}/min)",
            f"urls found  : {human_count(snap['urls_found'])}",
            f"urls new    : {human_count(snap['urls_new'])}",
            f"dorks done  : {snap['dorks_completed']}/{snap['dorks_total']}",
            f"proxies     : {snap['proxy']['alive']}/{snap['proxy']['total']} alive, "
            f"{snap['proxy']['cooldown']} cooldown",
            f"rotations   : {human_count(snap['rotations'])}",
        ]
        return "\n".join(lines)


# ============================================================================
# TELEGRAM: HANDLERS
# ============================================================================


class BotContext:
    """Shared state container for Telegram handlers."""

    def __init__(self, *, config: Config, engine: Engine, bot: Bot) -> None:
        self.config = config
        self.engine = engine
        self.bot = bot
        self.telemetry: Optional[TelemetryReporter] = None
        self.pending_clear: Set[int] = set()


def build_router(ctx: BotContext) -> Router:
    """Build the aiogram Router with all command handlers."""

    router = Router(name="yahoo-dork-parser")

    # ----- /start -----

    @router.message(CommandStart())
    async def on_start(message: Message) -> None:
        if message.from_user is None:
            return
        dorks = len(ctx.engine.dorks)
        await message.answer(
            "<b>yahoo-dork-parser ready.</b>\n"
            f"loaded dorks: <code>{dorks}</code>\n"
            f"workers: <code>{ctx.config.scraper.workers}</code>\n\n"
            "Send a <code>.txt</code> of dorks, then <code>/run</code>.",
            parse_mode=ParseMode.HTML,
        )

    # ----- /status -----

    @router.message(Command("status"))
    async def on_status(message: Message) -> None:
        snap = ctx.engine.snapshot()
        state = "paused" if snap["paused"] else ("running" if ctx.engine.running else "idle")
        text = (
            f"<b>status</b>: <code>{state}</code>\n"
            f"uptime: <code>{human_duration(snap['uptime'])}</code>\n"
            f"workers: <code>{snap['workers_alive']}/{ctx.config.scraper.workers}</code>\n"
            f"queue: <code>{snap['queue_size']}</code>\n"
            f"req total: <code>{human_count(snap['req_total'])}</code> "
            f"(<code>{snap['rps']:.1f}/s</code>)\n"
            f"blocked: <code>{human_count(snap['req_blocked'])}</code> "
            f"(<code>{snap['bpm']:.1f}/min</code>)\n"
            f"urls new: <code>{human_count(snap['urls_new'])}</code>\n"
            f"dorks done: <code>{snap['dorks_completed']}/{snap['dorks_total']}</code>"
        )
        await message.answer(text, parse_mode=ParseMode.HTML)

    # ----- /stats -----

    @router.message(Command("stats"))
    async def on_stats(message: Message) -> None:
        snap = ctx.engine.snapshot()
        text = (
            "<b>detailed stats</b>\n"
            f"uptime          : <code>{human_duration(snap['uptime'])}</code>\n"
            f"req total       : <code>{human_count(snap['req_total'])}</code>\n"
            f"req ok          : <code>{human_count(snap['req_ok'])}</code>\n"
            f"req blocked     : <code>{human_count(snap['req_blocked'])}</code>\n"
            f"req empty       : <code>{human_count(snap['req_empty'])}</code>\n"
            f"req failed      : <code>{human_count(snap['req_failed'])}</code>\n"
            f"urls found      : <code>{human_count(snap['urls_found'])}</code>\n"
            f"urls new        : <code>{human_count(snap['urls_new'])}</code>\n"
            f"jobs requeued   : <code>{human_count(snap['jobs_requeued'])}</code>\n"
            f"jobs dropped    : <code>{human_count(snap['jobs_dropped'])}</code>\n"
            f"rotations       : <code>{human_count(snap['rotations'])}</code>\n"
            f"writer written  : <code>{human_count(snap['writer_written'])}</code>\n"
            f"dedup inserted  : <code>{human_count(snap['dedup_inserted'])}</code>\n"
            f"dedup checked   : <code>{human_count(snap['dedup_checked'])}</code>"
        )
        await message.answer(text, parse_mode=ParseMode.HTML)

    # ----- /proxies -----

    @router.message(Command("proxies"))
    async def on_proxies(message: Message) -> None:
        s = ctx.engine.proxy_pool.stats()
        text = (
            "<b>proxy pool</b>\n"
            f"total     : <code>{s['total']}</code>\n"
            f"alive     : <code>{s['alive']}</code>\n"
            f"cooldown  : <code>{s['cooldown']}</code>\n"
            f"acquired  : <code>{human_count(s['acquired'])}</code>\n"
            f"successes : <code>{human_count(s['successes'])}</code>\n"
            f"failures  : <code>{human_count(s['failures'])}</code>\n"
            f"blocks    : <code>{human_count(s['blocks'])}</code>"
        )
        await message.answer(text, parse_mode=ParseMode.HTML)

    # ----- /pages -----

    @router.message(Command("pages"))
    async def on_pages(message: Message, command: CommandObject) -> None:
        arg = (command.args or "").strip()
        if not arg:
            await message.answer(
                f"usage: <code>/pages 1-{ctx.config.scraper.max_pages}</code>",
                parse_mode=ParseMode.HTML,
            )
            return
        try:
            pages = int(arg)
        except ValueError:
            await message.answer("pages must be an integer")
            return
        clamped = ctx.engine.set_pages(pages)
        await message.answer(
            f"pages_per_dork set to <code>{clamped}</code>",
            parse_mode=ParseMode.HTML,
        )

    # ----- /dorks -----

    @router.message(Command("dorks"))
    async def on_dorks(message: Message) -> None:
        dorks = ctx.engine.dorks
        if not dorks:
            await message.answer("No dorks loaded.")
            return
        sample = dorks[:20]
        lines = "\n".join(f"• <code>{_escape_html(d)}</code>" for d in sample)
        more = "" if len(dorks) <= 20 else f"\n… and {len(dorks) - 20} more"
        await message.answer(
            f"<b>loaded dorks</b> ({len(dorks)}):\n{lines}{more}",
            parse_mode=ParseMode.HTML,
        )

    # ----- /clear -----

    @router.message(Command("clear"))
    async def on_clear(message: Message) -> None:
        kb = InlineKeyboardBuilder()
        kb.button(text="confirm", callback_data="clear:yes")
        kb.button(text="cancel", callback_data="clear:no")
        kb.adjust(2)
        await message.answer(
            "This will truncate the output file. Continue?",
            reply_markup=kb.as_markup(),
        )

    @router.callback_query(F.data.startswith("clear:"))
    async def on_clear_cb(cb: CallbackQuery) -> None:
        action = cb.data.split(":", 1)[1]
        if action != "yes":
            with contextlib.suppress(Exception):
                await cb.message.edit_text("cancelled.")  # type: ignore[union-attr]
            await cb.answer()
            return
        await ctx.engine.clear_output()
        with contextlib.suppress(Exception):
            await cb.message.edit_text("output cleared.")  # type: ignore[union-attr]
        await cb.answer()

    # ----- /export -----

    @router.message(Command("export"))
    async def on_export(message: Message) -> None:
        path = ctx.config.paths.output
        if not path.exists() or path.stat().st_size == 0:
            await message.answer("Output is empty.")
            return
        size = path.stat().st_size
        limit = 45 * 1024 * 1024  # keep under Telegram's 50MB bot limit
        if size <= limit:
            with path.open("rb") as fh:
                data = fh.read()
            await message.answer_document(
                BufferedInputFile(data, filename=path.name),
                caption=f"{size} bytes",
            )
            return
        # Split into parts.
        await message.answer(f"Output is {pretty_bytes(size)}; splitting into parts.")
        part_index = 0
        with path.open("rb") as fh:
            while True:
                chunk = fh.read(limit)
                if not chunk:
                    break
                part_index += 1
                await message.answer_document(
                    BufferedInputFile(chunk, filename=f"{path.stem}.part{part_index}.txt"),
                    caption=f"part {part_index}",
                )

    # ----- /rotate -----

    @router.message(Command("rotate"))
    async def on_rotate(message: Message) -> None:
        await ctx.engine.force_rotate()
        await message.answer("identity rotation forced on all workers.")

    # ----- /pause /resume -----

    @router.message(Command("pause"))
    async def on_pause(message: Message) -> None:
        await ctx.engine.pause()
        await message.answer("paused.")

    @router.message(Command("resume"))
    async def on_resume(message: Message) -> None:
        await ctx.engine.resume()
        await message.answer("resumed.")

    # ----- /run -----

    @router.message(Command("run"))
    async def on_run(message: Message) -> None:
        if ctx.engine.running:
            await message.answer("already running.")
            return
        if not ctx.engine.dorks:
            await message.answer("no dorks loaded. send a .txt first.")
            return
        # Start engine.
        await ctx.engine.start()
        await ctx.engine.seed_queue()
        # Start telemetry.
        chat_id = message.chat.id
        if ctx.telemetry is not None:
            await ctx.telemetry.stop()
        ctx.telemetry = TelemetryReporter(
            ctx.bot, ctx.engine, chat_id, interval=ctx.config.scraper.telemetry_interval
        )
        await ctx.telemetry.start()
        await message.answer("run started.")

    # ----- /stop -----

    @router.message(Command("stop"))
    async def on_stop(message: Message) -> None:
        if not ctx.engine.running:
            await message.answer("not running.")
            return
        if ctx.telemetry is not None:
            await ctx.telemetry.stop()
            ctx.telemetry = None
        await ctx.engine.stop()
        await message.answer("stopped. output flushed.")

    # ----- /upload (document) -----

    @router.message(F.document)
    async def on_document(message: Message) -> None:
        doc: Document = message.document  # type: ignore[assignment]
        if not doc.file_name or not doc.file_name.lower().endswith(".txt"):
            await message.answer("send a .txt file (one dork per line).")
            return
        try:
            assert ctx.bot is not None
            file = await ctx.bot.get_file(doc.file_id)
            buf = io.BytesIO()
            await ctx.bot.download_file(file.file_path, buf)
        except TelegramAPIError as exc:
            await message.answer(f"download failed: {exc}")
            return

        target = ctx.config.paths.dorks
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("wb") as fh:
            fh.write(buf.getvalue())

        count = ctx.engine.load_dorks(target)
        await message.answer(
            f"loaded <code>{count}</code> dorks. send <code>/run</code> to start.",
            parse_mode=ParseMode.HTML,
        )

    return router


def _escape_html(text: str) -> str:
    """Escape a string for HTML parse mode."""

    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )


# ============================================================================
# MAIN ENTRYPOINT
# ============================================================================


async def _run_app(config: Config) -> None:
    """Wire everything together and run until signalled."""

    engine = Engine(config)
    engine.load_dorks(config.paths.dorks)

    # Proxy pool: load + health check.
    loaded = engine.proxy_pool.load_from_file(config.paths.proxies)
    if loaded:
        LOG.info("Health-checking %d proxies...", loaded)
        await engine.proxy_pool.health_check(
            concurrency=config.scraper.proxy_health_concurrency,
            timeout=config.scraper.proxy_health_timeout,
        )
    else:
        LOG.warning(
            "No proxies loaded. Scraping will run without proxies — expect fast blocks."
        )

    # Bot construction.
    if not config.telegram.token:
        raise ConfigError("Telegram token is required to start the bot.")

    bot = Bot(
        token=config.telegram.token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()

    ctx = BotContext(config=config, engine=engine, bot=bot)

    # Auth middleware.
    if config.telegram.allowed_chat_ids:
        auth = AuthMiddleware(config.telegram.allowed_chat_ids)
        dp.message.middleware(auth)
        dp.callback_query.middleware(auth)
    else:
        LOG.warning("No allowed_chat_ids configured; bot will accept any chat.")

    dp.include_router(build_router(ctx))

    # Shutdown hook.
    stop_event = asyncio.Event()

    def _signal_handler(*_: Any) -> None:
        stop_event.set()

    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        with contextlib.suppress(NotImplementedError):
            loop.add_signal_handler(sig, _signal_handler)

    polling_task = asyncio.create_task(dp.start_polling(bot), name="bot-polling")
    stop_task = asyncio.create_task(stop_event.wait(), name="stop-event")

    LOG.info("ready.")

    try:
        await asyncio.wait(
            {polling_task, stop_task},
            return_when=asyncio.FIRST_COMPLETED,
        )
    finally:
        LOG.info("shutdown requested")

        # Stop telemetry.
        if ctx.telemetry is not None:
            with contextlib.suppress(Exception):
                await ctx.telemetry.stop()

        # Stop polling.
        with contextlib.suppress(Exception):
            await dp.stop_polling()
        await cancel_task(polling_task)
        await cancel_task(stop_task)

        # Stop engine.
        with contextlib.suppress(Exception):
            await engine.stop()

        # Close bot.
        with contextlib.suppress(Exception):
            await bot.session.close()

        LOG.info("goodbye.")


def _parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="yahoo-dork-parser",
        description="Mass Yahoo dork parser with Telegram control.",
    )
    parser.add_argument("-c", "--config", default=DEFAULT_CONFIG_PATH,
                        help="Path to YAML config.")
    parser.add_argument("--log-level", default=None,
                        help="Override log level (DEBUG/INFO/WARNING/ERROR).")
    parser.add_argument("--json-logs", action="store_true",
                        help="Emit structured JSON logs.")
    parser.add_argument("--version", action="version",
                        version=f"%(prog)s {__version__}")
    return parser.parse_args(argv)


async def _async_main(argv: Optional[Sequence[str]] = None) -> int:
    args = _parse_args(argv)

    # Initial logging (before config load, so config errors are visible).
    setup_logging(args.log_level or "INFO", json_mode=args.json_logs)

    try:
        config = load_config(args.config)
    except ConfigError as exc:
        LOG.error("config error: %s", exc)
        return 2

    # Reconfigure logging per config.
    setup_logging(
        args.log_level or config.logging.level,
        json_mode=args.json_logs or config.logging.json_mode,
        log_file=config.paths.log_file,
    )

    try:
        await _run_app(config)
    except KeyboardInterrupt:
        LOG.info("interrupted")
    except Exception as exc:  # noqa: BLE001
        LOG.exception("fatal: %s", exc)
        return 1
    return 0


def main() -> int:
    """Synchronous entry point."""

    try:
        return asyncio.run(_async_main())
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
