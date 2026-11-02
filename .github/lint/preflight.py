"""Recognize the pinned adapter before Lean imports its dependency API.

Unknown configurations retain the configured native lint command. Path dependencies
are accepted only with the same exact pinned source bytes, allowing tiny fixtures.
"""
import hashlib
import json
from pathlib import Path
import sys
import tomllib

PIN = "f2effa3d803fda822b1f97b806c47cf2adfbcbc2"
SOURCES = {
    "lakefile.toml": "acadcd8beb13a53a4ac9399e6706c829309d2380f338d13b037886666f978015",
    "scripts/runLinter.lean": "24ee54cb7f38734970b970406ad75baf7aae7a8889b939d13f7b5a8c5f20556a",
    "Batteries/Tactic/Lint.lean": "70cdcc284aaa3b637fecbbdc91316ad0d0c59c4766637f3e8c38d3f686bd30e8",
    "Batteries/Tactic/Lint/Basic.lean": "a6df6a54285448c19a3a4a721011f36a8735e027707fa3225c718380f14081e3",
    "Batteries/Tactic/Lint/Frontend.lean": "c220e1431d89e12fbe9ba483e0f1eceebb7f5fe811ffaea9049104266f1a105a",
    "Batteries/Tactic/Lint/Misc.lean": "ac46c3ae1d9716d6da0c2bd9991dbb30975276c3bfac4fd0c14c72f1f3039fe7",
    "Batteries/Tactic/Lint/Simp.lean": "9ffde5ad73dc5a72dd09c31f59cbccf648a272250c53597073c9dded7ee5a0f0",
    "Batteries/Tactic/Lint/TypeClass.lean": "30a23854f7607f887b443101771a6934d5137f581761ed204c8c6e0687a8aa3a",
}


def provider_directory(root=Path.cwd()):
    try:
        # Lake prefers lakefile.lean when both files exist; a TOML selector cannot
        # establish that active configuration's driver or arguments.
        if (root / "lakefile.lean").exists():
            return False
        if (root / ".lake/package-overrides.json").exists():
            return False
        config = tomllib.loads((root / "lakefile.toml").read_text())
        if config.get("packagesDir", ".lake/packages") != ".lake/packages":
            return False
        args = config["lintDriverArgs"]
        if (config.get("lintDriver") != "batteries/runLinter"
                or config.get("builtinLint") is not True or not isinstance(args, list)):
            return False
        if not args or not all(isinstance(a, str) and a and
                (not a.startswith("-") or a in {"--no-build", "--trace", "-v"}) for a in args):
            return False
        if not any(not a.startswith("-") for a in args):
            return False
        if "--no-build" not in args:
            return False
        manifest = json.loads((root / "lake-manifest.json").read_text())
        if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
            return False
        package, = [p for p in manifest["packages"] if p["name"] == "batteries"]
        if (package.get("configFile", "lakefile.toml") != "lakefile.toml"
                or package.get("manifestFile", "lake-manifest.json") != "lake-manifest.json"
                or package.get("subDir") is not None):
            return False
        if package["type"] == "git":
            if package.get("rev") != PIN:
                return False
            directory = root / manifest.get("packagesDir", ".lake/packages") / "batteries"
        elif package["type"] == "path":
            directory = root / package["dir"]
        else:
            return False
        if (directory / "lakefile.lean").exists():
            return False
        if all(hashlib.sha256((directory / name).read_bytes()).hexdigest() == expected
               for name, expected in SOURCES.items()):
            return directory.resolve()
        return False
    except (OSError, ValueError, KeyError, TypeError):
        return False


def supported(root=Path.cwd()):
    return bool(provider_directory(root))


if __name__ == "__main__":
    directory = provider_directory()
    if directory and sys.argv[1:] == ["--batteries-dir"]:
        print(directory)
    if directory and sys.argv[1:] == ["--driver-args"]:
        config = tomllib.loads(Path("lakefile.toml").read_text())
        print(json.dumps([*config["lintDriverArgs"], "--trace"]))
    sys.exit(0 if directory else 1)
