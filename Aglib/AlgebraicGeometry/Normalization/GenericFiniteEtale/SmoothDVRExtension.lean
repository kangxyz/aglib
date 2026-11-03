/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDVRPurity
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisExtension
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SourceGeometry

/-! # Original pointed Galois extension over a smooth DVR base

The actual normalization is finite etale and Galois, with exactly the original
deck-group order. Its unchanged open-recovery isomorphism identifies the
restriction with the supplied generic cover, and the unique section retains
its original base and generic triangles. No replacement extension is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The original generic pointed tame Galois cover extends to the same native
normalization as a pointed finite-etale Galois cover, with unchanged deck order. -/
theorem exists_smoothDVR_galoisExtension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 (Spec (.of R)))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R)) :
    letI : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
      @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_of_smooth p (regularStalks_spec R) x)
    let K := (Spec (.of R)).functionField
    letI : Algebra R K := instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : IsFractionRing R K := functionField_isFractionRing_of_affine (.of R)
    letI : IsOpenImmersion (Spec.algebraMap R K) := LocalRing.GenericFiber.baseMap_openImmersion
    let U := pullback p (Spec.algebraMap R K)
    let j := pullback.fst p (Spec.algebraMap R K)
    letI : IsIntegral U := GeometricallyIntegral.geometrically_isIntegral
      (Spec.algebraMap R K) j (pullback.snd p (Spec.algebraMap R K)) (.of_hasPullback _ _)
    ∀ (Y : FiniteEtale U) [CategoryTheory.PreGaloisCategory.IsGalois Y],
    Nat.card (Aut Y) ∣ N →
    ∀ (a : Spec K ⟶ Y.obj.left),
    a ≫ Y.obj.hom ≫ j = (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s →
    ∃ h : Etale (genericMap j Y.obj.hom).fromNormalization,
      letI := h
      IsGalois (normalizationFiniteEtale j Y) ∧
      Nat.card (Aut (normalizationFiniteEtale j Y)) = Nat.card (Aut Y) ∧
      ∃ l : Spec (.of R) ⟶ (normalizationFiniteEtale j Y).obj.left,
        l ≫ (normalizationFiniteEtale j Y).obj.hom = s ∧
        (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l =
          a ≫ (normalizationFiniteEtaleRestrictionIso j Y).hom.hom.left ≫
            pullback.fst (normalizationFiniteEtale j Y).obj.hom j ∧
        (∀ l' : Spec (.of R) ⟶ (normalizationFiniteEtale j Y).obj.left,
          l' ≫ (normalizationFiniteEtale j Y).obj.hom = s →
          (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l' =
            a ≫ (normalizationFiniteEtaleRestrictionIso j Y).hom.hom.left ≫
              pullback.fst (normalizationFiniteEtale j Y).obj.hom j → l' = l) := by
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
    @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
      (regularStalks_of_smooth p (regularStalks_spec R) x)
  let K := (Spec (.of R)).functionField
  let : Algebra R K := instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R K := functionField_isFractionRing_of_affine (.of R)
  let : IsOpenImmersion (Spec.algebraMap R K) := LocalRing.GenericFiber.baseMap_openImmersion
  let U := pullback p (Spec.algebraMap R K)
  let j := pullback.fst p (Spec.algebraMap R K)
  let : IsIntegral U := GeometricallyIntegral.geometrically_isIntegral
    (Spec.algebraMap R K) j (pullback.snd p (Spec.algebraMap R K)) (.of_hasPullback _ _)
  dsimp only
  intro Y hG hcard a ha
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  let : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (Spec.algebraMap R K))
  let : IsIntegral Y.obj.left := Lifting.isIntegral Y
    (smoothFieldRegularity K U (pullback.snd p (Spec.algebraMap R K)) inferInstance)
  have h := etale_normalization_of_smoothDVR_genericSection R p s hs N hN hunit
    Y hcard a ha
  obtain ⟨het, l, hl, hgeneric, huniq, _⟩ := h
  let := het
  refine ⟨het, normalizationFiniteEtale_isGalois j Y,
    normalizationFiniteEtale_card_aut j Y, l, hl, ?_, ?_⟩
  · exact hgeneric
  · intro l' hl' hg'
    exact huniq l' hl' hg'

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
