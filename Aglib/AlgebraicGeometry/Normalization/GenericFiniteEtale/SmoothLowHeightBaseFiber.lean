/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDimensionOneBaseOpen
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.BaseLocalizationSection
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FlatPreimmersionEtale
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.BaseOpen

/-! # Whole fibres over base primes of height at most one

The original normalization is etale above every point of a smooth fibre whose
base prime has height at most one. The bound is on the base prime, not on the
target point. The actual field/DVR localization and original normalization
comparison provide the entire fibre, with the unchanged lifted section.

This is the low-height fibre input to relative purity, not relative purity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Every original normalization point over a fibre with base height at most
one is etale. No coheight bound is imposed on its target point. -/
theorem etaleAt_of_smooth_baseOpen_baseHeight_le_one
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
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
    (x : X) (hx : (p x).asIdeal.height ≤ 1)
    (y : (genericMap j Y.obj.hom).normalization)
    (hy : (genericMap j Y.obj.hom).fromNormalization y = x) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
  let q : PrimeSpectrum A := p x
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
  obtain ⟨aR, hR, _, _⟩ :=
    exists_baseLocalizationNormalizationSection A p q j Y s hs a ha
  have hunitL : IsUnit (N : L) := by
    simpa only [map_natCast] using hunit.map (algebraMap A L)
  have hheight : q.asIdeal.height ≤ 1 := hx
  have hdimL : ringKrullDim L ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal L]
    exact_mod_cast hheight
  let : Etale (genericMap jT Yq.obj.hom).fromNormalization :=
    etale_normalization_of_smooth_dimLE_one_baseOpen_section L hdimL pT r hr Wq jT hjT
      N hN hunitL Yq hcardq aR hR
  have hl : l (IsLocalRing.closedPoint L) = q := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  obtain ⟨t, ht, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p) (g := l) x (IsLocalRing.closedPoint L) hl.symm
  let f := (genericMap j Y.obj.hom).fromNormalization
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := b) y t (hy.trans ht.symm)
  let e := baseLocalizationIso A p q j Y
  have he : e.inv ≫ (e.hom ≫ pullback.fst f b) = pullback.fst f b := by
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hpoint' : (e.hom ≫ pullback.fst f b) (e.inv z) = y :=
    (congrArg (fun k : pullback f b ⟶ _ => k z) he).trans hz
  have het : (genericMap jT Yq.obj.hom).fromNormalization.etaleAt (e.inv z) :=
    ⟨⊤, trivial, inferInstance⟩
  exact etaleAt_of_flatPreimmersionBaseChange j b hg jT g (.of_hasPullback j b) Y
    (e.inv z) y hpoint' het

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
