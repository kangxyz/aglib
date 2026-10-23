# Conservative geometric points closed in their fibres

The root is
`Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed`.
Declarations live in
`AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed`.

For arbitrary schemes `T,S : Scheme.{u}` and a locally finite type morphism
`p : T ⟶ S`, `IsFibrewiseClosed p x` means literally that the singleton at
`x` is closed in the subspace `p ⁻¹' {p x}`. The native scheme-theoretic fibre
is connected to this condition by `fiberHomeo` and
`isFibrewiseClosed_of_fibre`.

For each such point `x`, `pointField x` is the actual algebraic closure of
its residue field, in universe `u`. `geometricPoint x` is the original map
from its spectrum to `T`, and its underlying point is proved equal to `x`.

`ofArrows_mem_iff_geometricLifts` detects covering families on every object
of the actual small etale site of `T`. Its tests are genuine field-valued
lifts through the displayed arrows. If a family fails to cover, its union
of images is open. The nonempty closed complement meets a closed point on
an actual pullback to a residue-field fibre. Jacobson fibres and the native
closed-point image theorem give a point closed in the corresponding fibre
of `T`. Its selected algebraically closed geometric point lifts to the test
scheme and witnesses failure of the geometric lifting test.

The point and coefficient universes are explicit. `largePoint` is an actual
native `Point.{u+1}` whose fibre is exactly the original geometric Hom-fibre
functor composed with `uliftFunctor.{u+1}`. Finite-limit preservation proves
its elements cofiltered; their actual `u+1` size supplies initial smallness.
The covering-lift property is inherited from the original geometric point.

`pointFamily_isConservative` verifies the native all-sieve criterion at this
larger universe. `jointlyReflectIsomorphisms` and `isIso_of_geometricStalks`
then apply to arbitrary actual `AbelianSheaf.{u,u+1} T` objects. The stalk is
the native `largePoint.sheafFiber`; the original geometric map is retained.
`isIso_of_all_fibrewiseClosed_geometricStalks` states the consumer directly
using all actual algebraically closed `Ω : Type u` and geometric maps whose
underlying points satisfy the literal fibre condition.

The only geometric hypothesis is `LocallyOfFiniteType p`. There is no
Noetherian, constructibility, compactness, separatedness, perfection, or
strict-henselization premise. No Ext assumption is needed. Coefficient
universes beyond the declared standard `u+1` universe are not asserted here.

## Canonical comparison with original small-etale stalks

[StalkUniverse](../StalkUniverse.lean) identifies the native larger-point sheaf
fibre with the original `pointSmallEtale` sheaf fibre for every actual
`AbelianSheaf.{u,u+1}`. Its forward germ formula sends the lift `ULift.up x`
to the same original geometric Hom witness `x`; the natural isomorphism is
natural in every coefficient morphism. This comparison requires no FLC, Ext,
or `LocallyOfFiniteType` premise.

The original-stalk isomorphism-detection consumer
`isIso_of_original_geometricStalks` uses `[LocallyOfFiniteType p]`, exactly at
that detection statement. This adds no full proper-base-change theorem. General
inverse-image `stalkUnit` bijectivity remains open.
