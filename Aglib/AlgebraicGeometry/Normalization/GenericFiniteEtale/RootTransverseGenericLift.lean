/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootEtalePresentation
public import Aglib.AlgebraicGeometry.Spec.RootTransverseEtalePresentation
public import Aglib.AlgebraicGeometry.Morphisms.Integral.GenericSection

/-! # The original transverse generic lift and its exponent-one presentation

The generic point of the original cover extends through the actual integral
normalization by the existing unique-extension theorem. Transversality is the
original principal-ideal equality with the reduced closed point, not an assumed
equality with a chosen uniformizer. The pointed chart and actual transverse
pullback then produce exponent one, with both original extension triangles and
uniqueness retained. Pointwise etale descent remains a separate lower step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- The actual transverse generic lift constructs its unique whole extension
and an exponent-one etale presentation at its original closed-point image. -/
theorem exists_transverseGenericLift_rootOnePresentation
    (R Ω D : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field Ω] [IsSepClosed Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra R D] [IsLocalHom (algebraMap R D)]
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})]
    (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)
    (htrans : Ideal.span {algebraMap R D f} = IsLocalRing.maximalIdeal D) :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    let U := Localization.Away f
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : ∀ t : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk t) :=
      fun t => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec R t)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    let q := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
    ∀ (g : Spec (Spec (.of D)).functionField ⟶ Y.obj.left),
    g ≫ Y.obj.hom ≫ Spec.algebraMap R U =
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ Spec.algebraMap R D →
    ∀ _X₀ : GeometricEtaleNeighborhood R Ω,
    ∃ s : Spec (.of D) ⟶ q.normalization,
      s ≫ q.fromNormalization = Spec.algebraMap R D ∧
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ s =
        g ≫ OpenRecovery.inclusion (Spec.algebraMap R U) Y.obj.hom ∧
      (∀ s' : Spec (.of D) ⟶ q.normalization,
        s' ≫ q.fromNormalization = Spec.algebraMap R D →
        (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ s' =
          g ≫ OpenRecovery.inclusion (Spec.algebraMap R U) Y.obj.hom → s' = s) ∧
      ∃ (A : CommRingCat.{u}) (aRA : Algebra R A),
      letI : Algebra R A := aRA
      Algebra.Etale R A ∧
      ∃ η : Spec (.of (RootAlgebra 1 (algebraMap R A f))) ⟶ q.normalization,
        Etale η ∧ Etale (η ≫ q.fromNormalization) ∧
        η ≫ q.fromNormalization =
          Spec.algebraMap A (RootAlgebra 1 (algebraMap R A f)) ≫ Spec.algebraMap R A ∧
        ∃ w : Spec (.of (RootAlgebra 1 (algebraMap R A f))),
          η w = s (IsLocalRing.closedPoint D) := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : ∀ t : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk t) := by
    intro t
    let : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk t) := regularStalks_spec R t
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  dsimp only
  intro Y hY hG hunit hcard g hg X₀
  let q := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
  let : IsFinite q.fromNormalization := OpenRecovery.fromNormalization_isFinite _ _
  have hnormal : NormalStalks (Spec (.of D)) := fun d =>
    ⟨(isIntegrallyClosed_and_isDomain_stalk_Spec D d).2,
      (isIntegrallyClosed_and_isDomain_stalk_Spec D d).1⟩
  have hg' : (g ≫ OpenRecovery.inclusion (Spec.algebraMap R U) Y.obj.hom) ≫
      q.fromNormalization =
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ Spec.algebraMap R D := by
    rw [Category.assoc, OpenRecovery.inclusion_over]
    exact hg
  have hext := existsUnique_integralGenericLift (Spec (.of D)) hnormal
    (Spec.algebraMap R D) q.fromNormalization
    (g ≫ OpenRecovery.inclusion (Spec.algebraMap R U) Y.obj.hom) hg'
  obtain ⟨s, hs, huniq⟩ := hext
  have hx : q.fromNormalization (s (IsLocalRing.closedPoint D)) = IsLocalRing.closedPoint R := by
    have h := congrArg (fun t : Spec (.of D) ⟶ Spec (.of R) =>
      t (IsLocalRing.closedPoint D)) hs.1
    exact h.trans AlgebraicGeometry.Spec_closedPoint
  have hpresentation := exists_etaleRootPresentation_at R Ω f hf N hN hreg
    Y hunit hcard (s (IsLocalRing.closedPoint D)) hx X₀
  obtain ⟨A, aRA, hA, n, hn, hnN, hnunit, η, hη, hbase, w, hw⟩ := hpresentation
  let : Algebra R A := aRA
  let : Algebra.Etale R A := hA
  let : Etale η := hη
  have hirr : Irreducible (algebraMap R D f) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr htrans.symm
  have hcancel := Scheme.Kummer.exponent_eq_one_of_pointedEtalePresentation R A D
    n f hirr η q.fromNormalization hbase s hs.1 w hw
  obtain ⟨rfl, hetale⟩ := hcancel
  refine ⟨s, hs.1, hs.2, ?_, A, aRA, hA, η, hη, hetale, hbase, w, hw⟩
  intro s' hs' hg'
  exact huniq s' ⟨hs', hg'⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
