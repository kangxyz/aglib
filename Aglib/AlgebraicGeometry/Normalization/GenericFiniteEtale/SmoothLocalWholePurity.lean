/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLowHeightBaseFiber
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalSectionPurity
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RelativePurityStep

/-! # Whole-target purity for the original local normalization

The induction is on the finite dimension of the original Noetherian local
base. Its punctured fibres are supplied by the exact smaller-dimensional
whole-normalization statement, transported through the existing localization
comparison. The already proved original-section result supplies the section
inside the canonical etale target open. The relative-purity step then applies
to the same normalization, with no new model or global dimension bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The entire original normalization is etale in the specified local base dimension. -/
def SmoothLocalWholePurityAtDimension (d : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A], ringKrullDim A = (d : ℕ) →
    ∀ {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
      (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _),
      ∀ (W : (Spec (.of A)).Opens) [Nonempty W]
        (j : U ⟶ X) [IsOpenImmersion j]
        (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A)))),
        ∀ (N : ℕ), 0 < N → IsUnit (N : A) →
          letI : GeometricallyIntegral p :=
            geometricallyIntegral_of_smooth_of_geometricallyConnected p
          letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
          letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
          letI : IsIntegral U := isIntegral_of_isOpenImmersion j
          ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left]
            [CategoryTheory.PreGaloisCategory.IsGalois Y], Nat.card (Aut Y) ∣ N →
            ∀ (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization),
              a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
              Etale (genericMap j Y.obj.hom).fromNormalization

/-- The exact smaller-dimensional whole-normalization statement gives
etaleness at every original source point above the specified base prime.
The original base need not be local. -/
theorem etaleAt_of_baseLocalization_whole_dimension
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
    (Hdim : SmoothLocalWholePurityAtDimension.{u} d)
    (x : X) (hx : p x = q)
    (y : (genericMap j Y.obj.hom).normalization)
    (hy : (genericMap j Y.obj.hom).fromNormalization y = x) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
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
  let : Etale (genericMap jT Yq.obj.hom).fromNormalization :=
    Hdim L hd pT r hr Wq jT hjT N hN hunitL Yq hcardq aR hR
  have hl : l (IsLocalRing.closedPoint L) = q := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  obtain ⟨t, ht, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p) (g := l) x (IsLocalRing.closedPoint L) (hx.trans hl.symm)
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


/-- The whole-normalization statement in every finite local base dimension. -/
theorem smoothLocalWholePurityAtDimension (d : ℕ) :
    SmoothLocalWholePurityAtDimension.{u} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A _ _ _ _ _ hdim X U p _ _ s hs W _ j _ hj N hN hunit
    let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    let : IsIntegral U := isIntegral_of_isOpenImmersion j
    intro Y _ _ hcard a ha
    by_cases hd : d ≤ 1
    · have hdim' : ringKrullDim A ≤ 1 := by
        rw [hdim]
        exact_mod_cast hd
      exact etale_normalization_of_smooth_dimLE_one_baseOpen_section A hdim'
        p s hs W j hj N hN hunit Y hcard a ha
    have htwo : 2 ≤ ringKrullDim A := by
      rw [hdim]
      have hd' : 2 ≤ d := by omega
      exact_mod_cast hd'
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
      (normalStalks_of_smooth_normalBase A p x).2
    let q := genericMap j Y.obj.hom
    let f := q.fromNormalization
    let : IsIntegral (genericCover j Y.obj.hom).obj.left :=
      IsIntegral.of_isIso (originalFieldSpectrumIso j Y).hom
    let : IsIntegral q.normalization := inferInstance
    let (y : q.normalization) : IsIntegrallyClosed (q.normalization.presheaf.stalk y) :=
      (genericMap_normalStalks j Y.obj.hom y).2
    let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
    let : IsDominant Y.obj.hom := GenericGalois.dominant Y
    let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
    let : IsDominant q := by
      let : IsDominant ((originalFieldSpectrumIso j Y).hom ≫ q) := by
        rw [originalFieldSpectrumIso_hom_genericMap]
        infer_instance
      exact IsDominant.of_comp (originalFieldSpectrumIso j Y).hom q
    let : IsDominant f := by
      let : IsDominant (q.toNormalization ≫ f) := by
        change IsDominant (q.toNormalization ≫ q.fromNormalization)
        rw [Hom.toNormalization_fromNormalization]
        infer_instance
      exact IsDominant.of_comp q.toNormalization f
    have hsE : Set.range s ⊆ f.etaleTargetOpen f.isClosedMap :=
      range_subset_etaleTargetOpen_of_section_etaleAt j Y s a ha
        (etaleAt_smoothLocal_baseOpen_section A p s hs W j hj N hN hunit Y hcard a ha)
    have hpE : p ⁻¹ᵁ puncturedSpecOpen A ≤ f.etaleTargetOpen f.isClosedMap := by
      intro x hx
      have hqmax : (p x).asIdeal ≠ IsLocalRing.maximalIdeal A := by
        intro he
        apply hx
        exact PrimeSpectrum.ext he
      obtain ⟨n, hn, hdimn⟩ :=
        IsLocalRing.exists_ringKrullDim_localization_lt d hdim (p x) hqmax
      rintro ⟨y, hy, hxy⟩
      exact hy (etaleAt_of_baseLocalization_whole_dimension A p s hs W j hj N hN hunit
        Y hcard a ha (p x) n hdimn (ih n hn) x rfl y hxy)
    exact Hom.etale_of_puncture_and_section A p f s hs htwo hsE hpE

/-- The original tame pointed Galois normalization is etale on the whole
smooth target over a normal Noetherian local base. No supplied dimension
bound, excellence, Nagata or extra invertibility premise is introduced. -/
theorem etale_normalization_of_smooth_local_baseOpen_section
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
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y], Nat.card (Aut Y) ∣ N →
      ∀ (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization),
        a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
          Etale (genericMap j Y.obj.hom).fromNormalization := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((IsLocalRing.maximalIdeal A).height_ne_top Ideal.IsPrime.ne_top')
  have hdim : ringKrullDim A = (d : ℕ) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
    rfl
  exact (smoothLocalWholePurityAtDimension d) A hdim p s hs W j hj N hN hunit

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
