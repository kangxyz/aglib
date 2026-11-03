/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.TransverseGenericLift
public import Aglib.AlgebraicGeometry.Spec.SmoothDVRSection
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Smooth
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RegularBase
public import Aglib.AlgebraicGeometry.Morphisms.Flat.DVRBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The original smooth DVR section is transverse to generic normalization

Smoothness and geometric connectedness supply integrality, regularity and
normality of the original target. The section itself supplies every local
parameter condition and the original complement square. The original generic
cover point therefore extends uniquely and the unchanged normalization is
etale at its actual closed-point image. Global purity remains a separate step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- A generic point over the original smooth DVR section extends uniquely to
an etale point of the original normalization. No regularity, local complement
comparison, geometric residue field, or whole extension is supplied as input. -/
theorem exists_smoothDVR_transverseGenericLift
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
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left] [CategoryTheory.PreGaloisCategory.IsGalois Y],
    Nat.card (Aut Y) ∣ N →
    ∀ (a : Spec K ⟶ Y.obj.left),
    a ≫ Y.obj.hom ≫ j = (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s →
    ∃ l : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization,
      l ≫ (genericMap j Y.obj.hom).fromNormalization = s ∧
      (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l =
        a ≫ inclusion j Y.obj.hom ∧
      (∀ l' : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization,
        l' ≫ (genericMap j Y.obj.hom).fromNormalization = s →
        (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l' =
          a ≫ inclusion j Y.obj.hom → l' = l) ∧
      (genericMap j Y.obj.hom).fromNormalization.etaleAt (l (IsLocalRing.closedPoint R)) := by
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
  intro Y hY hG hcard a ha
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdata := exists_smoothDVRSection_transverseData R K p s hs t ht
  obtain ⟨hf, hreg, hquot, htrans, g, H, _⟩ := hdata
  let x := s (IsLocalRing.closedPoint R)
  let A := X.presheaf.stalk x
  let f := p.stalkScalar x t
  let : IsRegularLocalRing (A ⧸ Ideal.span {f}) := hquot
  let Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  let : Algebra A Ω := ((algebraMap (IsLocalRing.ResidueField A) Ω).comp
    (IsLocalRing.residue A)).toAlgebra
  let : IsLocalHom (algebraMap A Ω) :=
    inferInstanceAs (IsLocalHom ((algebraMap (IsLocalRing.ResidueField A) Ω).comp
      (IsLocalRing.residue A)))
  have hunitA : IsUnit (N : A) := by
    simpa only [map_natCast] using hunit.map (p.stalkScalar x)
  exact exists_transverseGenericLift_etaleAt j R s Ω f hf hreg g H Y N hN hunitA hcard
    htrans a ha

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
