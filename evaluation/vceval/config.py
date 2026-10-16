"""Pinned evaluation settings shared by the scorer and the Model-track runner.

Changing any value here changes scores. Treat such a change like a benchmark
release: publish a new evaluator revision and protocol (see RELEASING.md).
"""
from __future__ import annotations

import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BENCH_ROOT = REPO_ROOT / "benchmark"
PROMPT_DIR = REPO_ROOT / "evaluation" / "prompts"
VERUS_BIN = REPO_ROOT / "verus" / "verus"
RELEASE_JSON = REPO_ROOT / "leaderboard" / "release.json"

FAMILIES = ("leetcode", "codeforces")
CHECK_KEYS = ("code_tests", "verus", "spec_tests")

# (task, input_mode) -> prompt template, placeholder -> benchmark file,
# extraction rule, compile policy, and the checks the scorer runs.
TASKS = {
    ("SpecGen", "nl"): {
        "prompt": "nl2spec.md",
        "inputs": {"problem_description": "description.md"},
        "extract": "first", "compile": None,
        "checks": ("spec_tests",),           # Verus parse + typecheck; then human review
    },
    ("CodeGen", "nl"): {
        "prompt": "nl2code.md",
        "inputs": {"problem_description": "description.md"},
        "extract": "first", "compile": "rustc",
        "checks": ("code_tests",),
    },
    ("CodeGen", "spec"): {
        "prompt": "spec2code.md",
        "inputs": {"verus_spec": "spec.rs"},
        "extract": "last", "compile": "auto",
        "checks": ("code_tests",),
    },
    ("CodeGen", "nl_spec"): {
        "prompt": "nl_spec2code.md",
        "inputs": {"problem_description": "description.md", "verus_spec": "spec.rs"},
        "extract": "last", "compile": "auto",
        "checks": ("code_tests",),
    },
    ("ProofGen", "code_spec"): {
        "prompt": "spec_code2proof.md",
        "inputs": {"verus_program": "code_spec.rs"},
        "extract": "first", "compile": None,
        "checks": ("verus",),                 # lynette: code/spec unchanged; then verify
    },
    ("End2End", "nl"): {
        "prompt": "end2end.md",
        "inputs": {"problem_description": "description.md"},
        "extract": "last", "compile": "auto",
        "checks": ("code_tests", "verus", "spec_tests"),  # spec_tests: human review
    },
}

# Verus verification flags.
VERUS_FLAGS = ["--no-cheating", "--rlimit", "100000"]

# Model-track generation settings (single shot, no feedback).
GENERATION = {
    "temperature": None,  # Omit by default; an explicit value is model-specific.
    "max_output_tokens": None,  # Model-specific; required only by some backends.
    "samples_per_problem": 1,
    # Transport errors (rate limits, 5xx, timeouts) are retried; a returned
    # response is never resampled.
    "max_transport_retries": 8,
}

# Scoring limits.
LIMITS = {
    "verify_timeout_sec": 600,
    "typecheck_timeout_sec": 120,
    "compile_timeout_sec": 120,
    "case_timeout_sec": 1.0,  # wall-clock limit per test case
    "compare_timeout_sec": 30,
    "spec_generate_timeout_sec": 120,  # post2exe lowering of one specification
    "spec_compile_timeout_sec": 300,   # post2exe checker (rustc, or verus for its macro backend)
    "spec_test_timeout_sec": 600,      # one checker run over a test file
}


def release_info() -> dict:
    release = json.loads(RELEASE_JSON.read_text())
    return {"id": release["id"], "benchmark_revision": release["benchmark_revision"],
            "verus_version": release["verus"]["version"]}
