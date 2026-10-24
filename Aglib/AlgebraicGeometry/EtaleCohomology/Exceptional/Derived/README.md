# Native module-derived suppliers

`DirectImage` specializes the existing large-value module-sheaf Grothendieck
structure and native bounded-below derived adjunction to the actual constant
ring sheaf on the small-etale site. It retains the original localization unit
factorization. This is the ordinary image supplier for exceptional-image
comparisons, not a new derived model, a proper-base-change result, or an
exceptional-image independence theorem. Compilation evidence is recorded
separately; a source file alone is not a completed proof.

`Open` derives the genuine exact module lower-shriek adjunction and retains
both original localization factorization equations. The actual open/closed
triangles and original proper-refinement comparison are supplied by the
separate `Localization` and `Exceptional.Refinement` consumers; invertibility
of a proper-refinement comparison remains a proper-base-change obligation.

`OpenFullyFaithful` identifies invertibility of the original derived unit
using its native localization equation and proves full faithfulness, rather
than assuming an independently chosen equivalence on the essential image.

`TorsionRange` uses the original internal local-annihilator predicate on the
actual native homology module sheaves. Its bounded-below range imposes no
uniform annihilator. A torsion ring implies the property for every native
derived object; this range fact does not construct unbounded exceptional
images or assert proper-base-change invertibility.

`UnboundedDirectImage` uses the actual Grothendieck module-sheaf category and
the constructed K-injective replacement to define the native unbounded direct
image. The original exact inverse image supplies its native left adjoint.
The unit, counit, and computation on a specified K-injective resolution retain
the original complex maps. Its canonical direct- and inverse-image comparisons
with `DirectImage` retain the original bounded-below localization units. The
functors inherit native shift compatibility and triangulatedness. No torsion,
Noetherian, base-invertibility, or supplied-replacement premise is needed.

This unbounded ordinary-image construction does not prove finite-cohomological-
dimension computation, proper exchange, compactification independence, or the
unbounded exceptional calculus. Those remain separate mathematical obligations.

`UnboundedOpen` localizes the genuine exact module lower shriek and its original
adjunction with the same exact inverse image used by `UnboundedDirectImage`.
Its unit and counit retain the original cochain maps and exact localization
factors. The canonical comparison with `Open` retains the bounded-below unit.
The construction works for etale morphisms and, in particular, open immersions;
it does not require proper base change. The separate
`EtaleCohomology.Localization.Unbounded` consumer identifies the original
short-exact-complex triangle with these installed derived composites and their
original unit and counit, retaining the native connecting map on every
unbounded derived object.

`Composition` supplies the original bounded-below module inverse- and
direct-image identity and composition comparisons. The inverse-image
comparisons use exactness; the direct-image composition comparison uses
preservation of injectives. Their actual conjugacy equations refer to the
installed derived adjunctions and comparisons, with independent derived
universes. `Exceptional.Refinement.Coherence` consumes these equations for
the original refinement transformation, without a proper-base-change premise.

`BaseChange` constructs the genuine module `D+` exchange as the mate of the
original inverse-image square, and retains the original underived exchange
in its complex-unit equation. It does not assert exchange invertibility.

`UnderlyingAcyclic` proves that forgetting scalars sends module injectives to
objects acyclic for every original abelian direct image, using represented
Ext vanishing. It does not assert that the underlying sheaf is injective.
`Underlying` uses this acyclicity to construct the original direct-image
comparison with abelian sheaves; exactness supplies the inverse-image
comparison. Both comparisons retain their original composite-unit equations,
and all four derived-category universes remain independent.

`UnderlyingAdjunction` proves that these same specified comparisons are mates
under the original native derived adjunctions. Its exact inverse-image square
and normalized direct-image equation retain the original complex units. Only
exact forgetting comparisons are cancelled; the nonexact direct-image unit
is handled by the native right-derived universal property.

`UnderlyingBaseChange` proves the original scalar-forgetting exchange square
for the existing module and abelian `D+` base-change transformations. Its
`moduleDerivedBaseChangeMap_underlying` theorem specializes the literal
`HorizontalMateCubeEquation` to the six specified original transformations;
that ordinary definition is the comparison equality for every derived object,
not a new hypothesis or class. The proof consumes the actual whole ordinary
source cube, the six exact-comparison equations, and the original adjunction
mate identifications. All eight derived universes remain independent. Neither
properness nor torsion nor exchange invertibility is assumed or concluded.

General torsion proper base change is still an external mathematical supplier.
The forgetting square identifies the original maps but does not itself prove
that either exchange, or a proper-refinement comparison, is invertible.

`FiniteBaseChange` combines that same forgetting square with exact
conservativity and the proved finite abelian exchange. It proves invertibility
of the original genuine-module D+ exchange for finite morphisms over arbitrary
rings, retaining the eight independent derived universes. This finite case
does not require general torsion proper base change.
