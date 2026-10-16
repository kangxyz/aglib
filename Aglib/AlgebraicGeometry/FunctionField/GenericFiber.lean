/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# The actual generic fibre of a finite dominant morphism

For finite dominant maps of integral schemes, the canonical lift from the
source generic stalk is an isomorphism. No Noetherian, normality, separability
or dimension hypothesis occurs.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteDominantGenericFibre.lean`, frozen R5
integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`db35a618b42d1bd3404dc897b068b6a36419cdc609d87fe80019d0b443e460de`. Selected original ranges: [[24,
91]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The canonical pullback lift of the generic-point inclusion and induced function-field map. -/
def genericFibreMap (f : X ⟶ Y) [IsDominant f] : Spec X.functionField ⟶ pullback f
  ((Y.fromSpecStalk (genericPoint Y))) :=
  pullback.lift ((X.fromSpecStalk (genericPoint X)))
    (Spec.map (CommRingCat.ofHom (functionFieldMap f))) (fromSpecStalk_genericPoint_naturality f)


private theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) :
    Flat (X.fromSpecStalk x) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp [IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

private theorem reduced_of_flat_preimmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [AlgebraicGeometry.IsReduced Y] :
    AlgebraicGeometry.IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let g := (f.stalkMap x).hom
    let := g.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom g)
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hg : Function.Injective g := FaithfulSMul.algebraMap_injective _ _
    let e := RingEquiv.ofBijective g ⟨hg, f.stalkMap_surjective x⟩
    exact _root_.isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk X

/-- The original lift from the actual generic-point stalk is an isomorphism. -/
theorem genericFibreMap_isIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] : IsIso (genericFibreMap f) := by
  let P := pullback f ((Y.fromSpecStalk (genericPoint Y)))
  let p : P ⟶ X := pullback.fst f ((Y.fromSpecStalk (genericPoint Y)))
  let q : P ⟶ Spec Y.functionField := pullback.snd f ((Y.fromSpecStalk (genericPoint Y)))
  have : IsPreimmersion ((Y.fromSpecStalk (genericPoint Y))) :=
    inferInstanceAs (IsPreimmersion (Y.fromSpecStalk (genericPoint Y)))
  have : Flat ((Y.fromSpecStalk (genericPoint Y))) := flat_fromSpecStalk Y (genericPoint Y)
  have : IsPreimmersion p :=
    inferInstanceAs (IsPreimmersion (pullback.fst f ((Y.fromSpecStalk (genericPoint Y)))))
  have : Flat p := inferInstanceAs (Flat (pullback.fst f ((Y.fromSpecStalk (genericPoint Y)))))
  have : IsFinite q :=
    inferInstanceAs (IsFinite (pullback.snd f ((Y.fromSpecStalk (genericPoint Y)))))
  have : IsLocallyArtinian P := IsLocallyArtinian.of_locallyQuasiFinite q
  have : DiscreteTopology P := inferInstance
  have hp : ∀ x : P, p x = genericPoint X := by
    intro x
    obtain ⟨z, hzx, hz⟩ := (Flat.generalizingMap p)
      ((genericPoint_spec X).specializes (show p x ∈ Set.univ from trivial))
    have : z = x := hzx.eq
    simpa [this] using hz
  have : Subsingleton P :=
    ⟨fun x y => p.isEmbedding.injective ((hp x).trans (hp y).symm)⟩
  have : AlgebraicGeometry.IsReduced P := reduced_of_flat_preimmersion p
  have : IsPreimmersion (genericFibreMap f ≫ p) := by
    have h : genericFibreMap f ≫ p = (X.fromSpecStalk (genericPoint X)) := by
      dsimp only [genericFibreMap, p]
      exact pullback.lift_fst _ _ _
    rw [h]
    exact inferInstanceAs (IsPreimmersion (X.fromSpecStalk (genericPoint X)))
  have : IsPreimmersion (genericFibreMap f) := IsPreimmersion.of_comp _ p
  have : IsClosedImmersion (genericFibreMap f) :=
    IsClosedImmersion.of_isPreimmersion _ (isClosed_discrete _)
  have : Surjective (genericFibreMap f) := ⟨fun x =>
    ⟨IsLocalRing.closedPoint X.functionField, Subsingleton.elim _ _⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective (genericFibreMap f)

end AlgebraicGeometry.Scheme
