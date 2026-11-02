# Prove whole laws on the actual original comparisons

## Fixed question and evidence basis

This case applies the existing whole-statement and original-value method at
two native coefficient-square kernel boundaries. The
[fixed performance packet](author/fixed-performance-manifest.json) has SHA256
`ba08a493809dde15185eaced652ef4881237fee07f6bd1ea7677daa48ca52b38`;
the [final author result](author/FINAL-RESULT.json) has SHA256
`2a4807058057ddee2e1749808dbd6e227e6bd85eb68fe00e11bdbac70fdcb1cd`.
The separately supplied [current v10 review](review/continuity-coefficient-squares.md)
is an additional fixed input, not a rewrite of that packet. Its MD hash is
`6f91e912f6ebfd74ca94381bbfc4dcbb054b79e039bf5d28e5cf41b5bdcdc954`;
its [JSON](review/continuity-coefficient-squares.json) hash is
`26f3cd18cff71cb069663035b044438029f4cfb86b65c1592d807330ac9f5ecc`.

Native HEAD is `54d6974ace11bf7d197aa925cb8cade86db8a24f`, Lean 4.34.1,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The
[source capsule](source-capsule.json) binds complete small failed/original/final
sources, exact deltas, manifests, review records and unmodified closed native
receipts/logs/events. Large SOURCE manifests remain at their durable R paths,
full hashes and content keys supplied in the capsule. Absolute paths inside
historical packets are provenance; case links are relative.

The scope is generic `CoefficientSquares` and eight native square, triangle,
section, unit, transport and adjunct modules. This production record adds no
mathematical verdict and makes no claim about the unresolved R4 same-field
candidate.

## Two separate native failures

Horizontal inverse source [701e](sources/failed/DiagramSquareCoefficients.lean)
failed at 102:6 with `(kernel) deterministic timeout` in
[remote-aeb4b524](evidence/remote-aeb4b5240d16454d8407596071bc75cc/receipt.json),
SOURCE `b8000ae60996cea8cf925ec1ee6d9c2cf26b897ee236f56bca75d70c93c40b1f`.
Its [log](evidence/remote-aeb4b5240d16454d8407596071bc75cc/build.log)
reports 126s for the whole failed frontend. Repaired native 265 later passed
in [remote-86af6b33](evidence/remote-86af6b33e48a4416acba01690e53a39e/receipt.json),
SOURCE `fae614f1597cba0a32ef575b6c56e0d91449bbbbe081baf4fe452b49134d8c44`:
6.2s for that frontend, with generic b3b18252 separately passing at 4.7s.
The shared request still exited 1. The [exact source delta](deltas/horizontal-701-to-265.diff)
and intermediate generic snapshots retain this transition.

The independent triangle source [5e45](sources/failed/DiagramPullbackTriangle.lean)
failed at 19:6 with `(kernel) deterministic timeout` in
[remote-ac3fc2af](evidence/remote-ac3fc2af6a114bbda6fef1ea760b2383/receipt.json),
SOURCE `fab4502b6e105f1b65e14458f0da76dea52eba92f5dddd180d6e416c661ea917`.
Its [log](evidence/remote-ac3fc2af6a114bbda6fef1ea760b2383/build.log)
reports a 167s failed whole frontend and the subsequent module-private-only
diagnostic. Actual repaired triangle c606 passed at 3.7s in
[remote-b3a29780](evidence/remote-b3a2978033524fe39a1d72c73d5478a3/receipt.json),
SOURCE `335dcd514f9a63d1dccb6b47296b628e3d810c2749bdb19b68f60f3a64c24b6d`.
The [triangle delta](versions/v9/DiagramPullbackTriangle.diff) records this
separate repair. Neither failure's duration is a per-tactic cost, and neither
old/new pair is a matched speedup experiment or a unique kernel-reduction-pair
diagnosis.

## Whole laws on the original data before evaluation

The common owner derives complete horizontal, vertical, unit, transport and
triangle equations from the existing `D.Coherent`/`AdjunctionData`.
`squareIso_hComp_whole_of_eq` receives the actual original compositors and
three square isomorphisms, together with independently proved identities to
the corresponding comparisons of that same coherent D. It eliminates those
identities and uses the coherence-derived whole equation, before choosing
any coefficient object F or morphism.

The native horizontal wrapper proves those whole identities for the original
`inverseImageComp` and `inverseImageSquareIso` values. Raw variable-category
inverse and coefficient evaluators then consume the whole law at exactly
those same heads, using inverse cancellation and naturality. They keep six
independent category/Hom worlds. The whole-law proof parameter is explicitly
retained through `include h`; a failed intermediate omission is not retained
as an unconditional theorem. Native callers derive this parameter from
coherence and proved comparison identities, rather than assuming their desired
coefficient conclusion.

For triangles, `WholeTriangleSquareEquation` names the actual composite
natural transformations. The D theorem derives it from whole vertical pasting,
original triangle transports and associators. Its actual-comparison interface
again accepts identities of the five original isos. The native wrapper supplies
those comparisons and proofs before any F; the raw evaluator then evaluates
the whole equation and applies naturality to the arbitrary coefficient morphism.
The [generic v9 delta](versions/v9/CoefficientSquares.diff) and
[complete final generic source](sources/v10/Aglib/CategoryTheory/Sites/SheafCohomology/Continuity/InjectiveDiagram/CoefficientSquares.lean)
retain both layers. Unit evaluators follow the same pattern with the original
unit, square and triangle comparisons.

There is one shared actual coefficient constructor,
`Adjunction.CoefficientSquares.coefficientMap`. Both D and native wrappers use
it. Native `squareCoefficientMap_eq_original` proves the whole original map
value by `rfl`: the same square inverse at F followed by the same mapped
coefficient arrow. The [native source](sources/v10/Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramSquareCoefficients.lean)
retains that equation. These are original comparison identities and values,
not arbitrary isomorphisms with the same endpoints, another coefficient model,
or a record assuming the desired laws.

## Final native adjunction boundary and correspondence

After seven current passes in b3a, `SquareCoefficientAdjoint` still had its
own specialization errors at 49/83; the final triangle adjunct consumer was
unreached. The [v10 repair](versions/v10/SquareCoefficientAdjoint.diff) freezes
the original natural-Iso factors and actual adjunction endpoints. Typed
`congrArg` and equality transitivity remove the double inverse. It proves
whole left/right square identities independently, then transports the same
generic D conjugacy at the original native adjunctions. No new adjunction or
comparison is selected.

The arbitrary-second-leg and nested original Hom formulas retain the actual
inverse/direct-image adjunctions, square/triangle comparisons and equality
transports. Original section constructors, coefficient arrows and independent
base/index/category/Hom worlds remain. There is no new geometry, cartesian,
Ext, exactness, injectivity or enough-points premise.

The [v10 header record](versions/v10/PUBLIC-HEADER-CORRESPONDENCE.json) retains
all 20 original public declaration headers. Eight original native snapshots
are in `sources/original/`, and final nine sources in `sources/v10/`.
The [applied v10 manifest](versions/v10/READY-applied.json), SHA256
`cb00fe20864f80f41b72cea62e92ce2c292a7b446440879e096e7ba7890b006f`,
binds the exact final vector. Historical READY/pending wording retains its
original phase; later compiler outcomes are recorded separately.

## Matching nine-file native coverage

The [combined compiler record](versions/v10/compiler-result-all9.json) and
[retained-seven record](versions/v9/compiler-result-partial.json) bind the
current source hashes. Seven passes come from mixed closed b3a; the final two
come from closed successful 5c98. Commands, profiles, logs and wrapper events
for all five requests are in `evidence/`. All groups are closed and have no
input drift.

| Current module suffix | SHA256 prefix | Actual pass request | Whole frontend seconds | Shared exit |
| --- | --- | --- | --- | --- |
| InjectiveDiagram.CoefficientSquares | `c4192e75` | `b3a29780` | 5.1 | 1 |
| DiagramPullbackTriangle | `c6069656` | `b3a29780` | 3.7 | 1 |
| DiagramSquareCoefficients | `265ebda4` | `b3a29780` | 5.0 | 1 |
| DiagramSquareIdentity | `36f8ce5f` | `b3a29780` | 20.0 | 1 |
| DiagramSquareSections | `09ce2f1d` | `b3a29780` | 3.6 | 1 |
| DiagramSquareTopIdentity | `51c04405` | `b3a29780` | 3.4 | 1 |
| DiagramSquareTransport | `ffb0329d` | `b3a29780` | 3.4 | 1 |
| SquareCoefficientAdjoint | `bfeae121` | `5c98a3a0` | 5.5 | 0 |
| TriangleSquareAdjoint | `72c7d2c0` | `5c98a3a0` | 3.7 | 0 |

Seven b3a successes do not turn its shared exit1 into a successful request.
Its separate adjunct and finite-group failures retain their actual inputs.
The [final request](evidence/remote-5c98a3a074d248fa923c002d3e10ea07/receipt.json)
closes only the previously failed/unreached last two square roots for this
case; its independently owned finite-colimit roots do not enlarge the scope.
The earlier 265 pass at 6.2s and later matching 265 pass at 5.0s are separate
frontend observations, not interchangeable timing records.

Profiles used threads 4 and 12800 MiB/frontend throughout, without CPU
oversubscription. The aeb/86af/ac3fc requests used jobs 2 and 32768 MiB/run;
b3a used jobs 4 and 49152 MiB/run; final 5c98 used jobs 2 and 32768 MiB/run.
Standard 200000 budgets, native trust and pins remain; no source flags,
suppressions, new axioms or proof gaps were introduced by these repairs.
Different snapshots, root cohorts, cache frontiers and profiles prevent a
controlled wall/RSS/energy or whole-library performance inference.

## Review, reproduction and limits

The separately captured current ordinary review reports the exact v10 vector
mathematically/source-correspondence sound, covering the v9 actual-comparison
and triangle/unit derivations and narrow v10 native adjunction hunk. It checks
the 20 original headers and whole native constructor value. That verdict
belongs to its reviewer and supplied version; production checks here do not
create mathematical acceptance or established status. Earlier review history
remains verbatim in the companions with its historical scope.

For source inspection, compare the saved complete failed and final native
sources using the horizontal and triangle deltas. Two mechanical generic
deltas bind v5→v7 and v7→final snapshots, with before/after hashes in the
capsule. Existing v9/v10 diffs retain native/unit/adjunction changes. Full
original native sources allow direct public-header and whole-map inspection.
Source reconstruction uses a disposable copy matching a diff's header paths
and `patch -p0`; it is not another acceptance or compiler run.

The final recorded command was `lake --rehash build
Aglib.Algebra.Category.Grp.FiniteColimits
Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Values
Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SquareCoefficientAdjoint
Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.TriangleSquareAdjoint`, on
matching prepared dependencies. Exact earlier invocations and executable
identities remain in the receipts. Current operating guides own future commands.

Assigned square9 source/compiler scope is complete. No matched speedup,
per-tactic cost, unique conversion pair, exact kernel-cause verdict, global
performance improvement, whole-étale/library closure, independent R4 resolution,
or standalone lint/test/audit/replay/downstream-check result is claimed.
No new compile, profile, benchmark, source inventory or check chain was run
to produce this record.
