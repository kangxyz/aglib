# Actual adjunction hom-equivalences

[MateHomEquiv](MateHomEquiv.lean), imported as `Aglib.CategoryTheory.Adjunction.MateHomEquiv`, gives `CategoryTheory.homEquiv_conjugate` and `homEquiv_to_identity`. They compare the actual adjunction hom-equivalences through a supplied natural transformation between left adjoints, retaining the original unit/counit maps. That transformation need not be invertible.

These generic categorical equations support scheme tensor/pushforward and projection-formula mates. They contain no scheme, flatness, finiteness or cohomology assumption; those belong to the geometric consumers of the comparison.

[MateHomEquiv/Composition](MateHomEquiv/Composition.lean) supplies
`Adjunction.homEquiv_leftAdjointCompIso_inv_map`, which transposes the native composite
left-adjoint comparison and an arbitrary coefficient arrow through the same
three adjunctions. It retains the original unit and right-adjoint comparison.
The etale abelian `H1/DegreeZeroPullback` and module
`Constructible/Modules/ConstantPullbackSections` consumers share this proof,
with their independent coefficient and Ext universes preserved.

[MonicProducts](MonicProducts.lean) constructs the original tuple of adjunction
transposes followed by the supplied component isomorphisms. Its projections
identify it with the transpose of the whole product map and the actual
right-adjoint product comparison. If the whole input map is monic and the left
adjoint reflects monomorphisms, the tuple is monic; individual components need
not be monic. The affine finite-cogenerator consumer supplies its original
direct-image composition isomorphisms.

[Mates](Mates.lean) adds the actual four-adjunction comparison/unit identity and conjugate/mate whiskering transport, with independent category universes and explicit isomorphism conditions preserved.

[Unit](Unit.lean): `Adjunction.bijective_map_of_isIso_unit_app`: if the unit of `adj : F ⊣ G` is an
isomorphism at `N'`, then `F` is bijective on morphisms `N ⟶ N'`, for every `N` (the pointwise form
of Mathlib's `Adjunction.fullyFaithfulLOfIsIsoUnit`). Consumer:
`Picard/Comparison/LocallyTrivial.lean` (`q_T^*` on morphisms into trivial line bundles).


[UnderlyingMate](UnderlyingMate.lean) proves
`mateEquiv_inv_natTrans_eq_of_unit`: the original unit equation identifies
the actual mate for a specified right natural transformation, without an
invertibility premise on that transformation. The
`Mates/ScalarForgetting` isomorphism-valued theorem delegates to this more
general result and retains its API. The genuine module/abelian coefficient
comparison consumes the transformation-valued form.

[UnderlyingHomEquiv](UnderlyingHomEquiv.lean) carries that same actual mate through
its unit and naturality to the underlying adjunct value. Its preimage formula
requires the actual underlying functor to be full and faithful and retains the
given right comparison inverse. The Proper ZMod reduction consumes these laws
with its original module/abelian adjunctions and scalar action.

[Mates/OriginalExchange](Mates/OriginalExchange.lean) constructs original
exchange transport and identifies it through the actual adjunction unit.
[Mates/SelectedCoherence](Mates/SelectedCoherence.lean) identifies selected
composition and identity comparisons by their original conjugates, then
transports the existing right-adjoint laws.
[Mates/SelectedUnitValues](Mates/SelectedUnitValues.lean) retains their unit
and counit values. [Mates/SourceChange](Mates/SourceChange.lean) constructs
literal source comparison, original source-unit pasting and the adjusted
exchange with its identity and composition laws. The module image and
compactification-refinement consumers use the same maps; these results do
not assert a chosen exceptional associativity or six-operation calculus.
