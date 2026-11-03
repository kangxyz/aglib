/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothBaseLocalizationPurity
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothCodimensionOnePurity
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothSectionPurityStep
public import Aglib.RingTheory.KrullDimension.LocalDrop

/-! # Original pointed relative purity over a normal local base

Strong induction on the actual finite local dimension uses the original
field/DVR case in codimension one, the same localization cover and section
at smaller-dimensional base primes, and the actual Hartogs target-open step.
The conclusion concerns the unchanged normalization along its original section.
It does not assert etaleness on the whole smooth target in higher dimension.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The exact original selected-section purity statement holds in every finite dimension. -/
theorem smoothLocalSectionPurityAtDimension (d : ℕ) :
    SmoothLocalSectionPurityAtDimension.{u} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d ≤ 1
    · exact smoothLocalSectionPurityAtDimension_of_le_one d hd
    intro A _ _ _ _ _ hdim X U p _ _ s hs W _ j _ hj N hN hunit
    let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    let : IsIntegral U := isIntegral_of_isOpenImmersion j
    dsimp only
    intro Y _ _ hcard a ha
    have htwo : 2 ≤ ringKrullDim A := by
      rw [hdim]
      have hd' : 2 ≤ d := by omega
      exact_mod_cast hd'
    have hheight : ∀ x : X, Order.coheight x = 1 →
        ∀ y : (genericMap j Y.obj.hom).normalization,
          (genericMap j Y.obj.hom).fromNormalization y = x →
          (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
      intro x hx y hy
      exact etaleAt_of_smooth_baseOpen_codimensionOne A p s hs W j hj N hN hunit
        Y hcard a ha x hx y hy
    have hpuncture : ∀ q : Spec (.of A), q ∈ puncturedSpecOpen A →
        (genericMap j Y.obj.hom).fromNormalization.etaleAt (a q) := by
      intro q hq
      have hqmax : q.asIdeal ≠ IsLocalRing.maximalIdeal A := by
        intro he
        apply hq
        exact PrimeSpectrum.ext he
      obtain ⟨n, hn, hdimn⟩ :=
        IsLocalRing.exists_ringKrullDim_localization_lt d hdim q hqmax
      exact etaleAt_section_of_baseLocalization_dimension A p s hs W j hj N hN hunit
        Y hcard a ha q n hdimn (ih n hn)
    obtain ⟨Z, hZ, het⟩ :=
      exists_smoothSection_etaleNeighborhood_of_codimensionOne_of_puncturedSection
        A p j Y s hs a ha htwo hheight hpuncture
    let f := (genericMap j Y.obj.hom).fromNormalization
    let : Etale (f ∣_ Z) := het
    have hsource : Etale ((f ⁻¹ᵁ Z).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    refine ⟨f ⁻¹ᵁ Z, ?_, hsource⟩
    have he : f (a (IsLocalRing.closedPoint A)) = s (IsLocalRing.closedPoint A) :=
      congrArg (fun g : Spec (.of A) ⟶ X => g (IsLocalRing.closedPoint A)) ha
    change f (a (IsLocalRing.closedPoint A)) ∈ Z
    exact he.symm ▸ hZ ⟨IsLocalRing.closedPoint A, rfl⟩

/-- A normal Noetherian local base needs no supplied dimension bound or
codimension-one/effacement premise for the original selected-section conclusion. -/
theorem etaleAt_smoothLocal_baseOpen_section
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
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
        (genericMap j Y.obj.hom).fromNormalization.etaleAt (a (IsLocalRing.closedPoint A)) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((IsLocalRing.maximalIdeal A).height_ne_top Ideal.IsPrime.ne_top')
  have hdim : ringKrullDim A = (d : ℕ) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
    rfl
  exact (smoothLocalSectionPurityAtDimension d) A hdim p s hs W j hj N hN hunit

/-- The original normalization is etale on an actual target open containing
the entire prescribed local section. Higher-dimensional global etaleness is not asserted. -/
theorem exists_smoothLocal_baseOpen_etaleNeighborhood
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
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
        ∃ Z : X.Opens, Set.range s ⊆ Z ∧
          Etale ((genericMap j Y.obj.hom).fromNormalization ∣_ Z) := by
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  dsimp only
  intro Y _ _ hcard a ha
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  have het := etaleAt_smoothLocal_baseOpen_section A p s hs W j hj N hN hunit Y hcard a ha
  exact ⟨f.etaleTargetOpen f.isClosedMap,
    range_subset_etaleTargetOpen_of_section_etaleAt j Y s a ha het,
    f.etale_restrict_etaleTargetOpen f.isClosedMap⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
