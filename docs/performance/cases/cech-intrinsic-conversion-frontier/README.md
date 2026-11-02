# Čech intrinsic comparison: fixed diagnostic support

This capsule supports [the case](../../cech-intrinsic-conversion-frontier.md).
[manifest.json](manifest.json) binds every retained file and authoritative external
log to its actual source locator, byte count and SHA256. `source/` contains the
nine accepted implementation sources; `diagnostic/source.lean` is the exact
profiled Scheme Comparison a9ff. Sources are evidence, not package modules.

`packets/` retains implementation results and the four fixed source vectors;
`review/` retains the existing source-review report without issuing a new verdict.
`analysis/` retains both request revisions, the extraction script, fixed result
and complete structured projection of 16,792 timed frames (including 38 Kernel
frames). The original structured frame messages are compact projections;
the sorted result extractor caps its messages at 500 characters. Full
messages remain in the raw trace. No exact expression-pair certificate
is implied. Original packet wording about a pending diagnostic is historical;
`analysis/result.json` supplies the completed diagnostic only.

`diagnostic/` retains the reconstructed setup, preparation/runtime metadata,
source and empty stderr logs. `native/` retains the exact broker receipt, build
log and frontend events. `excerpts/` contains exact unnumbered raw-trace line
ranges, including the complete 179–1130 conversion interval and the 71175–71220
zero-dictionary interval; the filenames and manifest provide original line
numbers. The declaration and timing tables use the full structured projection.

The 66,793,397-byte authoritative raw stdout remains in
`migration/incremental-compiler/diagnostics/cech-profile-6536a791/profile.stdout.log`
under the research workspace (`migration/` is a sibling of `aglib/`). Its absolute locator and
SHA256, the full-package source archive, normal native receipts/logs/events and
the setup stdout are in the manifest. These external records must be retained
alongside this capsule; this is deliberately not a standalone copy of the full
raw trace or full dependency tree. Binary diagnostic outputs are not needed by
this writing product and remain in the broker's `outputs/` directory.

To reproduce the existing extraction only, run `python3 analysis/analyze.py`
from this directory. Its preserved fallback reads the authoritative workspace
trace and rewrites `analysis/result.json`; it invokes no compiler. The fixed
`analysis/frames.json` is the original complete structured projection and is
retained verbatim. A relocated workspace needs the original trace locator
restored or an explicitly adapted analysis copy. No profile rerun is authorized
by this documentation. Document validation uses the separate delivery script.
