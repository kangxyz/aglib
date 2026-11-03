# Original tilde pullback composition at raw scalar maps

Source: [TildePullback.lean](TildePullback.lean).

For arbitrary original ring objects R, S and T in `CommRingCat`,
`tildePullbackIso_ringHom_comp_hom` proves the complete natural-transformation
composition square for raw maps f : R →+* S and g : S →+* T. The scalar
associator is the native `ModuleCat.extendScalarsComp f g`; the composite
geometric map is `Spec.map (CommRingCat.ofHom (g.comp f))`. Both individual
pullbacks, the equality comparison and the inverse pullback-composition map
are the original constructors. There is no flatness, quasicoherence or
finiteness hypothesis and no replacement scalar ring or sheaf model.

The single proof uses the original scalar and geometric adjunctions and native
conjugate-equivalence laws. It reduces the complete square to the original
right-adjoint sections calculation. The low affine `Sections` owner supplies the
original Γ-map/top-section function identity, derived from the single pointwise
implementation moved from the tensor-section consumer. This exposes the original
outer Γ-map without replacing the concrete goal or its inner comparison factors.
It is proved before specializing a coefficient sheaf or its `fromTildeΓ`
presentation, and does not assume the
square as a premise.

`tildePullbackIso_comp_hom` retains its original bundled-arrow statement as a
thin specialization through native `CommRingCat.hom_comp` and
`CommRingCat.ofHom_hom`. The raw component APIs
`tildePullbackIso_ringHom_comp_hom_app_aux` and
`tildePullbackIso_ringHom_comp_hom_app` evaluate the same natural law through one
variable-functor component lemma and its identity-removal form. The derivation
uses native `congr_app`, whisker and associator component laws before specializing
the original rings and sheaves; all six object and six hom universes are independent.
The raw specialization retains the original explicitly typed Spec triangle for
`CommRingCat.ofHom (g.comp f)`. The existing bundled component APIs retain their
original statements and use the same derivation with the retained bundled natural
law. Both raw and bundled forms retain an arbitrary proof of the same original
Spec triangle. The single native natural-law producer now accepts the given
original triangle proof directly. Its canonical public API specializes this producer
at the original `Spec.map_comp` proof without changing its statement. The arbitrary-proof
raw component supplies the same given proof to both the original pullback comparison
and that producer, then uses the existing complete generic clean component helper.
It does not transport a separately inferred canonical component equation or use an
additional whole-natural-law proof-choice wrapper. The generic clean helper still
removes identity components through its one variable-category morphism lemma.
The obsolete private proof-choice lemma has no callers and is removed. There is no
copied raw/bundled component or mates backend and no desired-square premise.

This lower law supplies the original associated-sheaf comparison used in affine
composition and descent. Its raw interface does not by itself establish the
higher coefficient-transfer factory, fixed-resolution homology overlap,
canonical gluing or arbitrary-field canonical generation; those consumers
must derive their own original-map compatibility equations.

Direct consumers: [AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafComposition](../../../Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafComposition.lean), [AlgebraicGeometry/Descent/FinitePresentation/Modules/Affine](../../../Descent/FinitePresentation/Modules/Affine.lean), [AlgebraicGeometry/Descent/Modules/Fppf/AffineStack](../../../Descent/Modules/Fppf/AffineStack.lean).
