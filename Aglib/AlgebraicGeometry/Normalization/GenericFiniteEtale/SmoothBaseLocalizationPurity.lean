/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalSectionPurityDimension
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.BaseLocalizationSection
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FlatPreimmersionEtale
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.BaseOpen

/-! # The original selected section point under base-dimension localization

The induction hypothesis is applied to the native localization pullback,
with its original cover and section. All localized geometric inputs and deck
order are derived; the same comparison returns etaleness to the original point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The exact lower-dimensional induction statement gives etaleness at the
original selected section point over the specified original base prime.
The original base need not be local. -/
theorem etaleAt_section_of_baseLocalization_dimension
    (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Y : FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y] (hcard : Nat.card (Aut Y) ∣ N)
    (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization)
    (ha : a ≫ (genericMap j Y.obj.hom).fromNormalization = s)
    (q : PrimeSpectrum A) (d : ℕ)
    (hd : ringKrullDim (Localization.AtPrime q.asIdeal) = (d : ℕ))
    (Hdim : SmoothLocalSectionPurityAtDimension.{u} d) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt (a q) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  let : IsDominant p := by
    let : IsDominant (s ≫ p) := by rw [hs]; infer_instance
    exact IsDominant.of_comp s p
  let L := Localization.AtPrime q.asIdeal
  let : IsIntegrallyClosed L := isIntegrallyClosed_of_isLocalization L
    q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  let l := Spec.algebraMap A L
  let : Flat l := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat L q.asIdeal.primeCompl))
  let : IsPreimmersion l := IsPreimmersion.of_isLocalization q.asIdeal.primeCompl
  let T := pullback p l
  let b : T ⟶ X := pullback.fst p l
  let pT : T ⟶ Spec (.of L) := pullback.snd p l
  let V := pullback j b
  let jT : V ⟶ T := pullback.snd j b
  let g : V ⟶ U := pullback.fst j b
  let : IsIntegral T := baseLocalization_integral A p q
  let : IsIntegral V := baseLocalization_openIntegral A p q j
  let Wq := l ⁻¹ᵁ W
  have hg : genericPoint X ∈ Set.range b := baseLocalization_generic_mem_range A p q
  let : Nonempty Wq := by
    obtain ⟨t, ht⟩ := genericPoint_mem_range_localization A L q.asIdeal.primeCompl
      q.asIdeal.primeCompl_le_nonZeroDivisors
    have hW : genericPoint (Spec (.of A)) ∈ W :=
      ((genericPoint_spec (Spec (.of A))).mem_open_set_iff W.isOpen).mpr
        (by simpa using ‹Nonempty W›)
    refine ⟨⟨t, ?_⟩⟩
    change l t ∈ W
    exact ht.symm ▸ hW
  have hjT : Set.range jT = pT ⁻¹' (Wq : Set (Spec (.of L))) :=
    Hom.range_pullback_of_baseOpen p l j W hj
  let Yq := (FiniteEtale.baseChange g).obj Y
  let : IsIntegral Yq.obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jT g (.of_hasPullback j b) Y
  have hG := baseLocalization_galois_card A p q j Y
  let : IsGalois Yq := hG.1
  have hcardq : Nat.card (Aut Yq) ∣ N := by
    change Nat.card (Aut ((FiniteEtale.baseChange g).obj Y)) ∣ N
    rw [hG.2]
    exact hcard
  let r := baseLocalizationSection A p q s hs
  have hr : r ≫ pT = 𝟙 _ := baseLocalizationSection_snd A p q s hs
  obtain ⟨aR, hR, _, hpoint⟩ :=
    exists_baseLocalizationNormalizationSection A p q j Y s hs a ha
  have hunitL : IsUnit (N : L) := by
    simpa only [map_natCast] using hunit.map (algebraMap A L)
  have het := Hdim L hd pT r hr Wq jT hjT N hN hunitL Yq hcardq aR hR
  exact etaleAt_of_flatPreimmersionBaseChange j b hg jT g (.of_hasPullback j b) Y
    (aR (IsLocalRing.closedPoint L)) (a q) hpoint het

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
