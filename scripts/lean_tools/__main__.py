"""The installed module and selected-checkout file use the same entry point."""
if __package__:
    from .cli import main
else:
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from lean_tools.cli import main

raise SystemExit(main())
