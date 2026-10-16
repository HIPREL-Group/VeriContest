#!/usr/bin/env python3
"""Run the Model-track generation. Run ``python3 evaluation/generate.py --help``."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from vceval.generate import main  # noqa: E402

main()
