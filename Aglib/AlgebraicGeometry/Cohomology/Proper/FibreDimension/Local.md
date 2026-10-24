# Proper coherent vanishing over a Noetherian local base

`subsingleton_moduleCohomology_of_local_of_dim_firstThickening` proves
vanishing of the original cohomology above the dimension of the actual
closed fibre. Its exact inputs are a Noetherian local commutative ring A,
an actual proper f:X→Spec A, an actual coefficient M satisfying
`affineLocallyFiniteType X M`, and natural numbers d<q with

`topologicalKrullDim (idealThickeningSpace f (maximalIdeal A)) ≤ d`.

The conclusion is
`Subsingleton (Sheaf.H.{u+1} (moduleAddSheaf X M) q)`.
The accompanying `isZero_moduleCohomology_of_local_of_dim_firstThickening`
states the same conclusion for the native module-valued cohomology object
with structural scalar `idealThickeningBaseScalar f`.

There is no completeness assumption on A. The theorem also requires no
domain or normality assumption on A, no integrality or regularity of X,
no coefficient flatness, and no projectivity or field/trait presentation.

## Actual thickenings and compatible families

For every positive integer n+1, the actual closed immersion
`idealThickeningι f (m^(n+1))` has range f⁻¹(V(m^(n+1))). The native
zero-locus-of-powers equality identifies this range with f⁻¹(V(m)).
The two original closed embeddings therefore give a homeomorphism of
underlying spaces with the first thickening. No scheme isomorphism is
asserted between these generally different nonreduced schemes.

Each actual thickening is Noetherian: it is proper over the Noetherian
affine base. The native Noetherian sheaf-cohomology vanishing theorem
therefore kills degree q of the literal pulled coefficient on every
positive thickening. This gives a zero module in each positive coordinate
of the original proper thickening tower.

A compatible family has zero coordinate zero as well, since the native
transition from coordinate one determines it. Thus the original sections
submodule of the whole tower is zero. No surjectivity of this transition
is assumed or needed.

## Original finite cohomology and its completion

Let H be the actual object
`(moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M`.
Its underlying group is the original Sheaf.H in the statement.
Proper coherent finiteness gives Module.Finite A H for that same structural
action. General `moduleCohomologyFormalFunctionsThickeningEquiv` identifies
AdicCompletion(m,H) with the original tower sections, without completeness
of A. On each original class its coordinates are the original geometric
pullbacks, by the existing formal-functions normalization theorem.

The native local Krull-intersection instance gives `IsHausdorff m H`
from Noetherian local A and finite H. Consequently the original linear
map `AdicCompletion.of m H` is injective. Its composite with the original
formal-functions equivalence injects H into the zero compatible-family
module. Hence H itself is zero.

This is completion of the original finite cohomology module. The proof
does not complete or replace the base scheme, source, coefficient, or
cohomology representation. The previous complete-base FibreDimension
provider and its private helpers remain unchanged; this leaf uses the
lower general formal-functions interfaces directly.

A rational-blowup application uses d=1 and q=2 after supplying the actual
closed-fibre dimension bound from its own source-dimension calculation.
That geometric input and the broader rational-blowup conclusion remain
separate from this general vanishing theorem.
