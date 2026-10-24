"""Read original extraction sources with exact provenance; never rewrite them."""
from pathlib import Path
import hashlib
import re
import subprocess
from .source import module_path



def source_path(module: str, *, source_root: Path) -> Path:
    """Resolve an explicit Lean-source directory containing Quillen/ or R5Lab/."""
    if not re.fullmatch(r"(?:Quillen|R5Lab)(?:\.[^\W\d]\w*)+", module):
        raise ValueError("Expected an original Quillen or R5Lab module identity")
    root = Path(source_root).resolve()
    path = root / module_path(module)
    if not path.resolve().is_relative_to(root):
        raise ValueError("Selected source path escapes its explicit source root")
    return path


def read_source(module: str, *, source_root: Path, expected_revision: str,
                expected_sha256: str) -> tuple[str, dict]:
    """Read a caller-selected source only after exact revision and byte-hash guards.

    source_root is the directory containing the original module tree; its
    enclosing Git checkout supplies the revision. No destination is written.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", expected_revision):
        raise ValueError("An exact Git revision is required")
    if not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
        raise ValueError("An exact source SHA-256 is required")
    path = source_path(module, source_root=source_root)
    result = subprocess.run(['git', '-C', str(Path(source_root).resolve()),
                             'rev-parse', 'HEAD'], capture_output=True, text=True, check=True)
    actual_revision = result.stdout.strip()
    if actual_revision != expected_revision:
        raise ValueError("Selected source revision does not match expected_revision")
    original = path.read_bytes()
    actual_sha256 = hashlib.sha256(original).hexdigest()
    if actual_sha256 != expected_sha256:
        raise ValueError("Selected source bytes do not match expected_sha256")
    return original.decode('utf-8'), {
        "source_module": module,
        "source_repository": "quillen-k-theory" if module.startswith("Quillen.") else "r5-lab",
        "source_revision": actual_revision,
        "source_sha256": actual_sha256,
    }


def write_source(module: str, *, source: str | None = None,
                 destination: str | None = None) -> dict:
    """Retired compatibility entry point; redesigned module writes are forbidden."""
    raise RuntimeError("Initial extraction writing is retired; use the current assigned author pipeline")


def record(group: str, entries: list[dict]) -> None:
    """Retired compatibility entry point; immutable provenance is never rewritten."""
    raise RuntimeError("Initial extraction recording is retired; provenance writes require their owner")
