# Native raw-chart equation: bounded performance case

## Question and scope

This case records compiler behavior for the raw-chart equation in `Aglib/AlgebraicGeometry/Picard/AssociatedBundle.lean`. It binds observed results to the source sequence and exact retained run receipts. It is a factual performance record, not a proof judgment.

The source series begins at the failed v3 source (`2083f9a1…`). The case includes that one baseline snapshot and four consecutive full patches, v4 through v7, with before/after SHA-256 bindings in [`source-capsule.json`](source-capsule.json). This avoids duplicating adjacent full snapshots. The 8129 full SOURCE archive is retained at the R locator recorded in that capsule; it is not copied here.

## Recorded sequence

- **08756 / v3 / 2083**: the whole request failed. AssociatedBundle reported a deterministic `whnf` heartbeat timeout at line 199 (maximum 200,000), then a kernel unknown-constant error for `sectionFamily_natural` at line 709. It had no OOM or forced kill. The 1037.996 seconds is whole-run elapsed time.
- **664a / v4 / d555**: the request failed with timeout diagnostics at lines 207 and 230 and a later missing-constant diagnostic at line 720.
- **8340 / corrected probe on v3**: the no-build probe reached formation, body, and intro, then timed out at its line 221 before later markers. It ended after diagnostics with exit 143. This was not a production build or successful timing. The exact probe, request, emitted log, and route notes are in `evidence/probe3fd/`.
- **1504 / v5 / 844a**: failure involved private `ChartComposition` access, field notation, and cascades.
- **f2e4 / v6 / 1ce**: the two-target request failed on private equation-head access.
- **8129 / v7 / 6fde**: the closed request had two module frontends and overall exit 1. `AssociatedBundle` passed in 140 seconds. `PowerDescent` failed only empty-line style diagnostics at original lines 419 and 686. The case records the AssociatedBundle file pass and request-level failure separately.

The 56a9 probe passed `-t4`, a valid Lean trust-level flag mistakenly supplied as though it selected threads. An unwrapped Lean frontend ran for about 390 seconds before root terminated its exact PID. Its receipt's zero wrapper-event count is not evidence that no compiler ran. This attempt used unintended settings and contributes no standard-profile acceptance or timing comparison. The separate b85 attempt was rejected by Lake's option parser for unknown `-t` before any Lean frontend.

## Effective repair and retained mathematics

The source series preserves the same mathematical objects and maps. The effective equation uses one regular proposition head `ChartComposition (f) (t) (g) := f ≫ t = g`, shared by `ChartRelationOn` and the variable-category cancellation step. In the final source, the existing `hview` is combined with the generic cancellation equation and identities established from the existing data: `hunit` follows from `P.map_id_apply` and `hu`; `htransition` uses `congrArg` and `transition_self_one`; and `hid` is pinned by the original `pullHom_id`. These are source-supported repair facts, not a new mathematical status judgment.

The route does not add a model, site, cover, global frame, or desired-naturality premise. The existing positive-transporter convention and maps/worlds remain in place. The v4 change removed the eager construction, but its concrete `simpa` still timed out at line 230; v5/v6's private-head formulations were invalid for their public consumers. v7 makes the regular equation head available to the public definition, which is required by that use.

## Source and environment identity

Lean 4.34.1; Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`; standard native profile: 8 jobs, 4 threads, 12,800 MiB frontend limit, 110,592 MiB aggregate limit, default trust, and default 200,000 heartbeat budget. The selected source snapshots and consecutive patch hashes are in the capsule. Its direct-import dependency hashes are bounded source bindings, not a full per-run manifest. The corrected 8340 probe used `-j4` and `-M12800`.

The 8129 full SOURCE archive is root-owned at the exact R locator and SHA-256 recorded by the capsule. Its archived content SHA is recorded there as well.

## Limits

These runs do not support a matched speedup, per-file RSS, exact reduction-pair, or universal compiler-cause claim. Requests and source revisions differ, and resource measurements are whole-request observations. The final 8129 request was not wholly successful because the PowerDescent style diagnostics failed.

A later root-reported native770 observation says the whitespace-only PowerDescent revision passed in 137 seconds, while its four-target graph was still running. No closed receipt or source archive for that graph is included here; it is not used as closure evidence.

Compiler results, lint, tests, and axiom-audit coverage are limited to the observations explicitly listed in [`case.json`](case.json). This packet makes no theorem-validity or mathematical-status claim.

## Evidence map

- [`case.json`](case.json): exact run IDs, source bindings, evidence file hashes, scope, and limits.
- [`source-capsule.json`](source-capsule.json): reconstruction chain, selected source hashes, direct import hashes, and full SOURCE archive locator.
- `sources/` and `patches/`: one v3 baseline plus exact consecutive changes through v7.
- `evidence/runs/`: retained receipts and build logs for 08756, 664a, 8340, 1504, f2e4, 56a9, b85, and 8129.
- `evidence/probe3fd/`: corrected 8340 probe inputs and diagnostics.

The recorded 8129 AssociatedBundle file result is closed on its supplied source and request.
