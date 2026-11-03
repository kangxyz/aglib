/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.StalkBaseChange
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootEtalePresentation
public import Aglib.AlgebraicGeometry.Spec.RootTransverseEtalePresentation
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseSource
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseBaseChange

/-! # Transverse sections at the original target stalk

The original normalization is compared with its actual target-stalk pullback.
The given whole section determines the local section. Its reduced parameter
pullback forces exponent one in the internally constructed pointed root chart.
Pointwise descent through the original flat preimmersion concludes etaleness
of the original normalization, not merely of a local replacement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- A transverse whole section detects etaleness of the original normalization
at its actual closed-point image. The local parameter and complement square
are on the original target stalk. -/
theorem etaleAt_of_transverseStalkSection
    {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] (x : X)
    (Ω D : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra (X.presheaf.stalk x) Ω] [IsLocalHom (algebraMap (X.presheaf.stalk x) Ω)]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra (X.presheaf.stalk x) D] [IsLocalHom (algebraMap (X.presheaf.stalk x) D)]
    (f : X.presheaf.stalk x) (hf : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    [IsRegularLocalRing ((X.presheaf.stalk x) ⧸ Ideal.span {f})]
    (hreg : IsSMulRegular (X.presheaf.stalk x) f)
    (g : Spec (.of (Localization.Away f)) ⟶ U)
    (H : IsPullback g (Spec.algebraMap (X.presheaf.stalk x) (Localization.Away f))
      j (X.fromSpecStalk x))
    (Y : FiniteEtale U) [IsIntegral Y.obj.left]
    [CategoryTheory.PreGaloisCategory.IsGalois Y]
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : X.presheaf.stalk x))
    (hcard : Nat.card (Aut Y) ∣ N)
    (htrans : Ideal.span {algebraMap (X.presheaf.stalk x) D f} = IsLocalRing.maximalIdeal D)
    (s : Spec (.of D) ⟶ (genericMap j Y.obj.hom).normalization)
    (hs : s ≫ (genericMap j Y.obj.hom).fromNormalization =
      Spec.algebraMap (X.presheaf.stalk x) D ≫ X.fromSpecStalk x)
    (X₀ : GeometricEtaleNeighborhood (X.presheaf.stalk x) Ω) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt (s (IsLocalRing.closedPoint D)) := by
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let V := Localization.Away f
  let : IsDomain V := Localization.Away.isDomain (RootCancellation.parameter_ne_zero R f hreg)
  let : ∀ t : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk t) :=
    fun t => (isIntegrallyClosed_and_isDomain_stalk_Spec R t).1
  let jR := Spec.algebraMap R V
  let q := genericMap j Y.obj.hom
  let YR := (FiniteEtale.baseChange g).obj Y
  let : IsIntegral YR.obj.left := stalkBaseChange_cover_isIntegral j x jR g H Y
  have hG := stalkBaseChange_galois_card j x jR g H Y
  let : CategoryTheory.PreGaloisCategory.IsGalois YR := hG.1
  have hcardR : Nat.card (Aut YR) ∣ N := by rw [hG.2]; exact hcard
  let qR := genericMap jR YR.obj.hom
  have hsection := exists_stalkBaseChangeSection j x jR g H Y s (Spec.algebraMap R D) hs
  obtain ⟨sR, hsR, _, hpoint⟩ := hsection
  have hxR : qR.fromNormalization (sR (IsLocalRing.closedPoint D)) =
      IsLocalRing.closedPoint R := by
    have h := congrArg (fun k : Spec (.of D) ⟶ Spec (.of R) =>
      k (IsLocalRing.closedPoint D)) hsR
    exact h.trans AlgebraicGeometry.Spec_closedPoint
  have hpresentation := RootCancellation.exists_etaleRootPresentation_at R Ω f hf N hN hreg
    YR hunit hcardR (sR (IsLocalRing.closedPoint D)) hxR X₀
  obtain ⟨A, aRA, hA, n, _, _, _, η, hη, hbase, w, hw⟩ := hpresentation
  let : Algebra R A := aRA
  let : Algebra.Etale R A := hA
  let : Etale η := hη
  have hirr : Irreducible (algebraMap R D f) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr htrans.symm
  have hcancel := Scheme.Kummer.exponent_eq_one_of_pointedEtalePresentation R A D
    n f hirr η qR.fromNormalization hbase sR hsR w hw
  let : Etale (η ≫ qR.fromNormalization) := hcancel.2
  let : IsFinite qR.fromNormalization := fromNormalization_isFinite jR YR.obj.hom
  have hlocal := Scheme.Hom.etaleAt_of_etale_source_of_noetherian η qR.fromNormalization w
  rw [hw] at hlocal
  let e := stalkBaseChangeIso j x jR g H Y
  have hover : e.hom ≫ pullback.snd q.fromNormalization (X.fromSpecStalk x) =
      qR.fromNormalization := stalkBaseChangeIso_hom_over j x jR g H Y
  have hcart : IsPullback
      (e.hom ≫ pullback.fst q.fromNormalization (X.fromSpecStalk x))
      qR.fromNormalization q.fromNormalization (X.fromSpecStalk x) := by
    apply IsPullback.of_iso_pullback _ e rfl hover
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover]
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let : IsFinite q.fromNormalization := fromNormalization_isFinite j Y.obj.hom
  exact Scheme.Hom.etaleAt_of_isPullback_of_flat_of_preimmersion hcart
    (sR (IsLocalRing.closedPoint D)) (s (IsLocalRing.closedPoint D)) hpoint hlocal

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
