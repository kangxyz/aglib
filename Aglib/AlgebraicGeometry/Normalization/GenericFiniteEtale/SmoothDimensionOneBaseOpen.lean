/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDVRBaseOpen
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.NormalStalks
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne

/-! # The field and DVR cases for the original smooth base-open normalization

The original normal Noetherian local base of dimension at most one is either
a field or a DVR. The field case is original full-open recovery; the other
case uses the unchanged accepted DVR purity argument through its base-open wrapper.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The unchanged normalization is globally etale in base dimension at most one. -/
theorem etale_normalization_of_smooth_dimLE_one_baseOpen_section
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A ≤ 1)
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) :
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y], Nat.card (Aut Y) ∣ N →
      ∀ (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization),
        a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
        Etale (genericMap j Y.obj.hom).fromNormalization := by
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  intro Y hY hG hcard a ha
  by_cases hfield : IsField A
  · let : Field A := hfield.toField
    let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
      (normalStalks_of_smooth_normalBase A p x).2
    apply fromNormalization_etale_of_surjective_open j Y.obj.hom
    obtain ⟨w⟩ := ‹Nonempty W›
    intro x
    have hx : x ∈ Set.range j := by
      rw [hj]
      change p x ∈ W
      have he : p x = w.val := Subsingleton.elim _ _
      exact he.symm ▸ w.property
    exact hx
  · let : IsDiscreteValuationRing A :=
      IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one A hdim hfield
    exact etale_normalization_of_smoothDVR_baseOpen_section A p s hs W j hj
      N hN hunit Y hcard a ha

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
