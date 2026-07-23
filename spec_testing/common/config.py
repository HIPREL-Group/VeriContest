"""Config loading. Single source of truth: spec_testing/config.toml.

Every module reads knobs from here; nothing hard-codes a default that also lives
in config.toml. Python 3.11+ has tomllib in the stdlib.
"""
from __future__ import annotations

import tomllib
from functools import lru_cache
from pathlib import Path
from typing import Any

# spec_testing/ dir and repo root, resolved from this file's location.
SPEC_TESTING_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = SPEC_TESTING_DIR.parent
CONFIG_PATH = SPEC_TESTING_DIR / "config.toml"


@lru_cache(maxsize=1)
def load_config() -> dict[str, Any]:
    """Parse config.toml once and cache it."""
    with open(CONFIG_PATH, "rb") as fh:
        return tomllib.load(fh)


def get(section: str, key: str, default: Any = None) -> Any:
    cfg = load_config()
    return cfg.get(section, {}).get(key, default)
