# Original coherent H1: measured specialization cost

This case records the final native specialization of the accepted graded
coalgebra dimension bound. The mathematical consumer is
[Group/H1.lean](../../../../Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean):
for a proper, smooth, geometrically integral group over any field, the
dimension of the original coherent H1 is at most the dimension of the
cotangent space at its identity. The fixed environment is Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Original construction and diagnostic boundary

The selected cohomology is still `Sheaf.H` with its structural
`Module.compHom` field action. The coproduct is the original multiplication
pullback followed by the inverse of the same total Kunneth comparison.
Its unit, signed multiplication and degree-one support laws already compiled.
The private DirectSum adapter retains the given ring, algebra, grading and
coalgebra. It needs only the function view of the original signed source
equivalence, identified pointwise with that same selected equivalence.
This is no second cohomology realization or choice of inverse.

At a 400000-heartbeat allowance, the complete native theorem timed out at
`whnf`. A staged probe formed the source function, and a separate t-only
probe formed the generic adapter with the exact named native structures and
that function. The remaining measured boundary was conversion of the closed
original multiplication proof into the adapter's first hypothesis.

The retained isolated probe raised only its local allowance to 1000000. It
reported 945541 remaining heartbeats before that argument and 386241 after:
the conversion completed, consuming 559300 heartbeats. The logging tactic
then triggered a linter error. That diagnostic therefore proves neither
the later argument conversions nor a full H1 module pass.

## Retained executions

| Run | Source and outcome |
| --- | --- |
| `remote-ec77f579a84d435ba48c3f4ff0e170e7` | Full candidate `036ab22b...`, local 400000: native H1 failed at `whnf`. |
| `remote-5b5fc8bb764f45edb0b9e05470e4b65e` | Isolated diagnostic `dfef97b7...`, local 1000000: multiplication-proof conversion completed, then a logging-linter failure; not a full pass. |
| `remote-4d4518db3ddd4c598a14a4d01bba9e85` | Full candidate `c8eb3b35...`, local 1000000: one fresh H1 frontend passed in 228 seconds, with cached parents, exit 0, closed group and no input drift. |

The full successful source SHA is
`c8eb3b35cf3e44b2320c94963377084d71c85e44c101aeca305256152fe7c6ef`;
its source-content digest is
`9f50aee1d9e978fec856aa552bd8401f5946e8be1f01949e21f9677b6c85e33e`.
The earlier full source SHA is
`036ab22b37ef44b790d3e17625fd45cf2b4d8bf1b54cf837bedd1de9a0086b04`.
The complete source diff changes only the public declaration's 400000 cap to
1000000 and its adjacent explanation. The theorem, body, chosen structures,
source function, maps, scalar action and inverse remain unchanged. The package
default remains 200000; neither an unlimited nor a global cap is used.

Between these runs main advanced from `7545acd8` to `58f0a8a2` through CI/lint
tooling changes only. Mathematical sources and pins were compared bytewise
across that fast-forward. The successful native source is on `58f0a8a2`.
The actual compiler-event arguments record `-j4 -M49152`; nominal Lake trace
text can still display the package's weaker memory flag. These observations
do not show that H1 itself requires that memory limit.

## Evidence and limits

[The evidence index](evidence/INDEX.md) and
[SHA-256 manifest](evidence/SHA256_MANIFEST.json) retain byte-exact source
snapshots, receipts, build logs and short compiler-event files for all three
listed runs. Separate request files and setup JSON contents were unavailable
in the selected local run directories. The observed native setup paths and
arguments remain recorded; missing setup identities were not reconstructed.

The result establishes that 400000 was insufficient for this source and
1000000 was sufficient for the complete native theorem. It does not prove
that 1000000 is the smallest sufficient allowance, isolate a unique kernel
reduction cause, or compare the function-view adapter with every prior
representation at matched limits. No controlled speedup is claimed.
This record supplies native compilation evidence, not the final production
axiom audit or the separate canonical principal-polarization consumer.

## Proof aliases and final naming checks

Three prerequisite equalities use inferred proof-valued abbreviations:
`structureExternalAlgebraMap_tensor`, `structureExternalLinearMap_signed`,
and `structureExternalAlgebraMap_linear`. Their lemma-style names describe
the proved equations. Their abbreviation form preserves the inferred native
propositions at the measured specialization boundary. The standard
[`scripts/nolints.json`](../../../../scripts/nolints.json) records only their
three declaration-specific `defsWithUnderscore` exceptions. All other naming
checks retain their configured scope.

The specialized augmentation inclusion-zero theorem remains available as a
named equation. Its redundant simp registration was removed: the existing
general augmentation formula and homogeneous-component inclusion rule already
normalize the same expression. Its statement and proof are unchanged.
