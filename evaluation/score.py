#!/usr/bin/env python3
"""Score final programs. Run ``python3 evaluation/score.py --help``."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from vceval.score import main  # noqa: E402

main()
