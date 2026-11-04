# Scalar extension of the original root-valued Weil pairing

The scalar-extension law compares the same original Weil pairing on the native
primal and dual multiplication kernels with the pairing after field extension.
The target is the original roots equalizer. The proof composes with its monic
inclusion, then uses the bundled Cartier square, evaluation naturality,
evaluation base change, and the naturality of the native tensor comparison.

## Conversion boundary

The first native conditional core passed at 200000 heartbeats. Its caller
exhausted that budget when it tried to identify the concrete evaluation
naturality equation with the underlying-scheme premise. The revised proof
projects the Cartier equation over variable group objects and handles both
evaluation laws there. Literal unfolding of `Functor.mapGrp` exposes the same
pulled scheme as `F.obj`; the scalar-extension evaluation check has its own
small caller.

The concrete specialization passes the dual comparisons and the pullback of the
Cartier map as explicitly typed local arrows. Their identifying equations are
`rfl`. Staging these arguments with restricted reducibility let Lean form the
original roots pairings before it reached the Cartier proof. The wrapper
supplies that already introduced proof directly to the matching premise,
following the existing kernel-checked local-proof method.
[Stalk comparison case](../../../original-stalk-comparison-instance-lets-and-proof-irrelevance.md)

## Declaration-local budget

The two instrumented wrapper candidates below have identical bytes after
removing the scoped setting and its explanatory comment from the capped
candidate. Both used the same native setup on sealed source
`1d158bf5e194e8e8040b95eb1469d14055a89b70c736cddc196b7a165e7ceffb`.
The 200000 run reached the original pairings and timed out at the local
proof attachment. The 500000 run reached the complete proof and reported only
unused diagnostic traces. Removing those traces left a line-length diagnostic
in the clean conditional probe. The installed source wraps that binding and
keeps the 500000 allowance on the private concrete specialization.

The public theorem `weilPairingMorphism_fieldBaseChange` takes the Cartier
square from the checked native supplier. The ordinary package run used
checkout HEAD `367929e8a6c427ceb10a3e685c9a6bd796754752`, source
`7eea634421125ea1c0a67218497b90804f12478514fb2457fef3cb45bd665426`,
and Lean 4.34.1. It passed with ten fresh frontends. The roots producer took
139 s and its axiom mirror took 4.5 s. The mirror checks `propext`,
`Classical.choice`, and `Quot.sound`.
[Cartier supplier](../cartier-field/remote-89c789ece5bc485c9e2f976f6d32e808/CartierFieldBaseChange.lean.txt)

## Evidence

Each run directory contains its source, native log, receipt, and compiler
events. Scratch logs identify the exact candidate and setup hashes. The
[manifest](SHA256_MANIFEST.json) records the SHA-256 digest of every retained
file. The [probe driver](probe_root_field.py.txt) records how the scratch
frontends received the original module setup.

| Check | Observed result | Record |
|---|---|---|
| Original conditional core | Producer passed at the default budget | [80dc2ca](remote-80dc2ca4c5f94c2f9c4bc91bf0a9834b/build.log) |
| Original concrete caller | Timed out at the normalized evaluation-naturality premise | [e70b2d8](remote-e70b2d8b1e5e46b7af522f13e5b3ff51/build.log) |
| Variable-group paste | Evaluation naturality attached and scalar-extension evaluation timed out | [2f2bb57](remote-2f2bb576abf64bd48a2d42cbc3b1ddf1/build.log) |
| Split variable-group paste | Only temporary trace lint remained | [900dc49](remote-900dc49ccbc645f58e47528e6341f6bc/build.log) |
| Staged native arguments | All original arrows formed before Cartier proof attachment timed out | [c675b72](remote-c675b72db1d34b7f9b6d024fa47e8560/build.log) |
| Local proof attachment at 200000 | Timed out at the tactic supplying the local proof | [12f6c3b](remote-12f6c3b0c92a451dbfc0a30fd39fb0f9/build.log) |
| Same instrumented proof at 500000 | Complete proof with only temporary trace lint | [b96f3a5](remote-b96f3a59ea614da3aecaa90e19dfd36a/build.log) |
| Trace-free conditional proof | Only line-length lint remained | [6bd4dae](remote-6bd4dae1744e441b97fafba358c48097/build.log) |
| Ordinary package graph | Roots producer, axiom mirror, and selected consumers passed | [a3ff7e6](remote-a3ff7e60ecad40529c249f0859b3ff40/build.log) |

The paired scratch runs record closure under the two heartbeat settings.
The package timing describes the final source and import graph.
