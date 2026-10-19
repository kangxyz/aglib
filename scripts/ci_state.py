"""Compatibility import for the reusable native-check evidence implementation."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'ci'))
from lean_ci import state as _implementation

sys.modules[__name__] = _implementation
