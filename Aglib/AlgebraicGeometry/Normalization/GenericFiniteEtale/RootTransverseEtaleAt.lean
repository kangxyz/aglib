/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootTransverseGenericLift
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseSource

/-! # Pointwise etaleness at the original transverse generic lift

The original unique integral extension and exponent-one presentation are
constructed internally. Pointwise source descent concludes etaleness of the
original normalization map at the actual closed-point image of that extension.
No presentation, extension, or final comparison is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- Transversality of the original parameter ideal forces the original
normalization to be etale at its unique extended generic point. -/
theorem exists_transverseGenericLift_etaleAt
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
      q.fromNormalization.etaleAt (s (IsLocalRing.closedPoint D)) := by
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
  have hdata := exists_transverseGenericLift_rootOnePresentation R Ω D f hf N hN hreg
    htrans Y hunit hcard g hg X₀
  obtain ⟨s, hs, hgeneric, huniq, A, aRA, hA, η, hη, htotal, hbase, w, hw⟩ := hdata
  let : Algebra R A := aRA
  let : Etale η := hη
  let : Etale (η ≫ q.fromNormalization) := htotal
  have he := Scheme.Hom.etaleAt_of_etale_source_of_noetherian η q.fromNormalization w
  rw [hw] at he
  exact ⟨s, hs, hgeneric, huniq, he⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
