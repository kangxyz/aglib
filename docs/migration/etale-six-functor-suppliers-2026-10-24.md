# Etale coefficient, finiteness and exceptional-image suppliers

This integration combines completed source families from two independent
deliveries on the existing Aglib carriers. It does not assert general proper
base change, full smooth base change, general constructible finiteness, or a
choice-independent exceptional-image calculus.

## Source identity and selection

The integration base is Aglib
`5a691fa737de8c1f9e78188acf2bb8fa4928a206`, including the earlier local-comparison
cut `227d2d2`. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` are unchanged.

The finiteness/smooth archive has SHA-256
`2b3455087a1bf637b0d39507b61eef19c5a6036f734672287185992084de7a00`;
the exceptional-image archive has SHA-256
`ff02d785e7c1d61c4bfa805051d9bc720eecc91651aca0c9cd2d58163fee3d06`.
Their respective source baselines and author compilation claims are distinct
from this integration base. The archive notes are provenance and mathematical
input, not instructions to replace repository policy or tool configuration.

The follow-up archives have hashes
`eee1e31418d03d00907b0024b7f8e13367ae4c84b1f38a96828f11763bb00cc5`
and `08cf329b0f0762b389dbc95539147c3571c8ffa72fce8000686e6ee38520edd2`.
Their completed delta adds 16 C and nine D modules. Selection therefore adds
251 C-family and 201 D-family Lean modules. Sixty-eight paths
from the C delivery were already byte-identical upstream, including 59
production modules and nine tests, and are skipped. Existing mathematical
leaves have no content conflicts. Archived generated roots, tests, caches,
compiler logs, CI/tooling changes and chronological task notes are excluded.
Native import generation owns the selected union's root.

Eight C sources are excluded: the unfinished
`CategoryTheory/Sites/SectionsAdditive`, the superseded long-path generic
`ResolutionRepresentativeSections`, `Stalk/ChartCycleSections`, and the five
`Stalk/BaseChangeChart{Sections,Germs,Relative,Coefficient,RelativeGerms}`
consumers. The follow-up D delivery completes the formerly excluded
`Exceptional/Coefficients/UnderlyingComposition` and
`Exceptional/Derived/UnderlyingBaseChange`, with their actual original
comparison maps. These are now admitted together with genuine-module finite
D+ base change. The remaining C draft packets stay separate; no admitted
source imports them.

## Constructible module coefficients and finite maps

`Constructible/Modules` uses actual module-valued sheaves over a commutative
ring with independent scalar universe. Local values are finite modules;
their additive groups need not be finite. It supplies arbitrary inverse
image, Zariski and jointly surjective etale descent, finite categorical
sums/products, finite-etale image constructibility, and actual generic/dense
finite-Galois trivializations. Kernel/cokernel/extension closure uses a
Noetherian coefficient ring and retains the weak-Serre scope. Positive ZMod
comparison keeps the original finite-abelian coefficients and handles empty
charts.

The finite module trace and direct-image cohomology comparison preserve the
original scalar action, unit/rank equation and original comparison map.
General finite-image constructibility and descent of finite coefficient
objects, arrows and equations to Noetherian models are not consequences of
these theorems.

## Vanishing and finiteness

`Vanishing/DimensionZero` uses actual finite morphisms for proper maps with
zero-dimensional fibres; its positive higher-image vanishing allows arbitrary
abelian coefficients. Uniform geometric fibre-dimension bounds and the
allowed-annihilator/Postnikov reductions are separate suppliers. They do not
prove the positive-dimensional all-torsion bound.

Characteristic-primary proper cohomology is finite in every degree at the
displayed original constant and module coefficients. The finite-Galois
module-sheaf endpoint uses a proper scheme over a separably closed field of
characteristic p, a Noetherian coefficient ring, and an actual finite-Galois
trivialization by a finite p-killed module. No assertion that every local
system has such a global trivialization is inserted.

The curve chain proves original roots/cyclic H1 finiteness for smooth proper
geometrically connected curves over separably closed, possibly imperfect
fields, with positive order invertible in the field. No chosen rational
point or general PBC premise remains in that endpoint. The scalar/tensor
consumer supplies finite H1 for finite modules killed by an invertible prime
over an arbitrary commutative coefficient ring, retaining the native
universe/colimit conditions. The follow-up extends constant H1 to every finite
torsion module over a Noetherian coefficient ring, with the original action.
It also proves all-degree finite cohomology for constructible module
coefficients on proper zero-dimensional schemes over separably closed fields
over arbitrary commutative coefficient rings, and supplies the original
R-linear connecting maps and adjacent exact finite-generation consequences. H2, arbitrary constructible-coefficient proper
finiteness and compact-support finiteness remain open.

## Original exchange and smooth comparison

Etale higher and D+ exchange are unconditional at arbitrary abelian
coefficients and independent derived models. Smooth comparison is reduced
to an actual all-degree affine-line comparison at positive modulus with
order invertible on the entire base; that affine-line theorem is not supplied.

`Stalk/BaseChangeGlobalSections` and `BaseChangeGlobalGerms` identify the
defined original exchange on original global classes in every degree.
`GlobalSectionsField` proves bijectivity of the same edge over a separably
closed target field. Arbitrary-neighborhood exchange/germ normalization
still needs its literal-chart consumer. The accepted chart-cycle suppliers
are retained, while their unfinished final consumers are excluded.
No equality of higher-image sections with arbitrary-base neighbourhood
cohomology, or injectivity of the general-base edge, is inferred.

## Genuine module lower shriek, localization and derived existence

D's coefficient category is genuine modules over the associated constant
ring sheaf, for arbitrary rings in value universe u+1. C's module-valued
category has a commutative ring and an independent scalar universe. Preserve
their explicit equivalence and original unit comparisons; these carriers
are not definitionally interchangeable and neither should be narrowed to
erase the difference.

The ordinary module lower shriek is constructed for etale morphisms; open
immersions additionally give full faithfulness. Finite and closed module
direct image is exact. Open/closed localization uses the actual counit and
closed inverse-image unit for a complementary open/closed pair. The D+
triangle retains the original connecting arrow.

Compactification refinement geometry retains schematic density and produces
actual common refinements, normalized base changes and composition towers.
Native Nagata supplies nonemptiness under its separated finite-type/qcqs
hypotheses. The derived refinement transformation satisfies identity and
composition coherence. Its invertibility, compactification independence and
the full exceptional composition/base-change calculus remain additional
proper-exchange obligations.

The unbounded foundation constructs a functorial K-injective replacement in
the displayed Grothendieck setting, with a natural monic quasi-isomorphism.
The geometric unbounded ordinary image/open image and localization consumer
uses that construction, not an assumed replacement. Finite-relative-
cohomological-dimension computation and unbounded proper exchange are not
provided. The follow-up proves the full scalar-forgetting square for the original
module and abelian D+ exchanges, with all eight derived universes independent.
Conservativity then gives finite-morphism base change for that same original
genuine-module exchange over arbitrary rings. General proper exchange is
still an additional theorem.

## Duplication and validation boundaries

The selected C and D ordinary source paths are disjoint. Their common
mathematical dependencies are reused at their existing paths. Their two
unit-to-mate lemmas had the same declaration name: D allows an arbitrary
right natural transformation, whereas C supplies an isomorphism. The general
theorem is named `mateEquiv_inv_natTrans_eq_of_unit`; C's existing
`mateEquiv_inv_eq_of_unit` interface is a short specialization of that single
proof. The genuine-module comparison uses the general form. The incoming
C cocycle theorem shares a declaration name with an older, unintegrated
private integer-cocycle draft; that private draft is parked and is not part
of this union. The principal's natural-cycle/source-single proof does not
import it.

Local instance declarations in the admitted leaves have explicit names where
automatic names collided at the aggregate entry. Their original types,
values and local scope are preserved. Independent leaf success does not
detect a declaration-name collision between otherwise disjoint import graphs;
the actual generated-entry build supplies that coverage.

The helper definitions below use native definition naming. Consumers of the
source archives should update these identifiers; their mathematical
constructions and universe parameters are retained.

| Archive identifier | Integrated identifier |
| --- | --- |
| `acyclicStages_limitIso` | `acyclicStagesLimitIso` |
| `smallAcyclicTests_zeroIso` | `smallAcyclicTestsZeroIso` |
| `smallAcyclicTests_shiftIso` | `smallAcyclicTestsShiftIso` |
| `replacementIndex_orderBot` | `replacementIndexOrderBot` |
| `rightDerivedFunctorOfKInjectiveReplacement_commShift` | `rightDerivedFunctorOfKInjectiveReplacementCommShift` |
| `denseFiniteEtaleTrivialization_of_isAffine` | `denseFiniteEtaleTrivializationOfIsAffine` |

Redundant or non-normal simp attributes are removed from the reported
identities, which remain available for explicit rewriting. Structure fields
are documented. The refinement exchange uses the etaleness of j; a separate
etaleness parameter for i is unnecessary. The Galois finiteness theorem also
omits a redundant connectedness dictionary for its supplied Galois cover.

Validation uses one coherent incremental remote build over maximal selected
consumers, then native entry, source/style, declaration-lint and production
axiom checks. Matching individual module successes are retained even when
another module fails in the same batch. No AglibTest run, downstream/client
check, kernel replay, pin change or additional certification chain is added.
Compiler coverage verifies the Lean statements with their actual premises;
it does not remove the mathematical boundaries above.
