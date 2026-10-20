/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.ChartData
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Constants
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Coordinate maps for finite projective embeddings

The coordinate family contains the mixed monomials `Xₖ^(d-1) * Xₗ` and the
original chart coefficients. In the `Xᵢ^d` chart it therefore recovers every
original ratio `Xₗ / Xᵢ`, as well as the module generators.
-/




@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

variable {R : Type u} [CommRing R] {ι : Type u} {Y : Scheme.{u}}
  (f : Y ⟶ ProjectiveSpace R ι) (D : ChartData f)

/-- The additional coordinates and all mixed degree-`d` base monomials. -/
abbrev Coordinate := (ι × ι) ⊕ D.J

/-- The target chart corresponding to the original chart `i`. -/
def distinguished (i : ι) : Coordinate f D := Sum.inl (i, i)

/-- Pullback of the actual native degree-zero chart ring by the original morphism. -/
def sourceChartRingHom (i : ι) : coordinateRing R ι i →+* Γ(Y, sourceOpen f i) :=
  (f.app (coordinateOpen R ι i)).hom.comp
    (Proj.awayToSection (homogeneousSubmodule ι R) (X i)).hom

/-- The original coordinate ratio pulled back to the original inverse-image chart. -/
def sourceRatio (i k : ι) : Γ(Y, sourceOpen f i) :=
  sourceChartRingHom f i (coordinateRatio R ι i k)

@[simp]
theorem sourceRatio_self (i : ι) : sourceRatio f i i = 1 := by
  simp [sourceRatio]

/-- The original base-ring coefficient map on the inverse-image chart. -/
def sourceCoefficient (i : ι) : R →+* Γ(Y, sourceOpen f i) :=
  (sourceChartRingHom f i).comp (coordinateRingCoefficient R ι i)

/-- The normalized homogeneous coordinates on the original inverse-image chart. -/
def chartValue (i : ι) : Coordinate f D → Γ(Y, sourceOpen f i)
  | Sum.inl (k, l) => sourceRatio f i k ^ (D.d - 1) * sourceRatio f i l
  | Sum.inr a => D.b i a

@[simp]
theorem chartValue_distinguished (i : ι) : chartValue f D i (distinguished f D i) = 1 := by
  simp [chartValue, distinguished]

@[simp]
theorem chartValue_mixed (i l : ι) :
    chartValue f D i (Sum.inl (i, l)) = sourceRatio f i l := by
  simp [chartValue]

/-- Evaluation on the actual homogeneous-localization ring of the target chart. -/
def chartRingHom (i : ι) :
    coordinateRing R (Coordinate f D) (distinguished f D i) →+* Γ(Y, sourceOpen f i) :=
  (eval₂Hom (sourceCoefficient f i) (fun a => chartValue f D i a.1)).comp
    (coordinateRingToPolynomial R (Coordinate f D) (distinguished f D i))

@[simp]
theorem chartRingHom_coefficient (i : ι) (r : R) :
    chartRingHom f D i
        (coordinateRingCoefficient R (Coordinate f D) (distinguished f D i) r) =
      sourceCoefficient f i r := by
  simp [chartRingHom]

@[simp]
theorem chartRingHom_ratio (i : ι) (a : Coordinate f D) :
    chartRingHom f D i
        (coordinateRatio R (Coordinate f D) (distinguished f D i) a) =
      chartValue f D i a := by
  classical
  by_cases ha : a = distinguished f D i
  · subst a
    simp
  · change (eval₂Hom (sourceCoefficient f i) (fun a => chartValue f D i a.1))
      (coordinateRingToPolynomial R (Coordinate f D) (distinguished f D i)
        (coordinateRatio R (Coordinate f D) (distinguished f D i) (⟨a, ha⟩ :
          {a : Coordinate f D // a ≠ distinguished f D i}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X']

private theorem coordinateRing_hom_ext {A : Type u} [CommRing A] (i : ι)
    {φ ψ : coordinateRing R ι i →+* A}
    (hc : ∀ r, φ (coordinateRingCoefficient R ι i r) =
      ψ (coordinateRingCoefficient R ι i r))
    (hx : ∀ k, φ (coordinateRatio R ι i k) = ψ (coordinateRatio R ι i k)) : φ = ψ := by
  have h : φ.comp (polynomialToCoordinateRing R ι i) =
      ψ.comp (polynomialToCoordinateRing R ι i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using hc r
    · intro k
      simpa using hx k.1
  have h' := congrArg (fun g => g.comp (coordinateRingToPolynomial R ι i)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

/-- The original base-chart variables occur among the mixed target coordinates. -/
def baseChartLift (i : ι) : coordinateRing R ι i →+*
    coordinateRing R (Coordinate f D) (distinguished f D i) :=
  (eval₂Hom (coordinateRingCoefficient R (Coordinate f D) (distinguished f D i))
    (fun k => coordinateRatio R (Coordinate f D) (distinguished f D i)
      (Sum.inl (i, k.1)))).comp (coordinateRingToPolynomial R ι i)

@[simp]
theorem baseChartLift_coefficient (i : ι) (r : R) :
    baseChartLift f D i (coordinateRingCoefficient R ι i r) =
      coordinateRingCoefficient R (Coordinate f D) (distinguished f D i) r := by
  simp [baseChartLift]

@[simp]
theorem baseChartLift_ratio (i k : ι) :
    baseChartLift f D i (coordinateRatio R ι i k) =
      coordinateRatio R (Coordinate f D) (distinguished f D i) (Sum.inl (i, k)) := by
  classical
  by_cases hk : k = i
  · subst k
    change baseChartLift f D i (coordinateRatio R ι i i) =
      coordinateRatio R (Coordinate f D) (distinguished f D i) (distinguished f D i)
    rw [coordinateRatio_self, map_one, coordinateRatio_self]
  · change (eval₂Hom _ _)
      (coordinateRingToPolynomial R ι i
        (coordinateRatio R ι i (⟨k, hk⟩ : {k : ι // k ≠ i}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X']

/-- The original chart-ring pullback factors through the new chart presentation. -/
theorem chartRingHom_comp_baseChartLift (i : ι) :
    (chartRingHom f D i).comp (baseChartLift f D i) = sourceChartRingHom f i := by
  apply coordinateRing_hom_ext
  · intro r
    simp [sourceCoefficient]
  · intro k
    simp [sourceRatio]

/-- The target chart presentation is surjective because it contains the original base
coordinates and the original module generators. -/
theorem chartRingHom_surjective (i : ι) : Function.Surjective (chartRingHom f D i) := by
  let := preimageSectionsAlgebra f (coordinateOpen R ι i)
  have hscalar (r : Γ(ProjectiveSpace R ι, coordinateOpen R ι i)) :
      ∃ z, chartRingHom f D i z = (f.app (coordinateOpen R ι i)) r := by
    obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (homogeneousSubmodule ι R) (X i)
        (isHomogeneous_X R i) Nat.zero_lt_one).hom).2 r
    refine ⟨baseChartLift f D i q, ?_⟩
    change ((chartRingHom f D i).comp (baseChartLift f D i)) q = _
    rw [chartRingHom_comp_baseChartLift]
    exact congrArg (fun t => (f.app (coordinateOpen R ι i)) t) hq
  intro y
  have hy : y ∈ Submodule.span Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
      (Set.range (D.b i)) := by rw [D.span_b]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨coordinateRatio R (Coordinate f D) (distinguished f D i) (Sum.inr a),
      chartRingHom_ratio f D i (Sum.inr a)⟩
  | zero => exact ⟨0, map_zero _⟩
  | add y z hy hz hy' hz' =>
    obtain ⟨y', rfl⟩ := hy'
    obtain ⟨z', rfl⟩ := hz'
    exact ⟨y' + z', map_add _ _ _⟩
  | smul r y hy hy' =>
    obtain ⟨r', hr'⟩ := hscalar r
    obtain ⟨y', hy'⟩ := hy'
    refine ⟨r' * y', ?_⟩
    rw [map_mul, hr', hy']
    rfl

/-- The actual local map into the corresponding native standard projective chart. -/
def chartMap (i : ι) : (sourceOpen f i).toScheme ⟶
    (coordinateOpen R (Coordinate f D) (distinguished f D i)).toScheme :=
  (sourceOpen f i).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRingHom f D i)) ≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule (Coordinate f D) R)
      (X (distinguished f D i)) (isHomogeneous_X R (distinguished f D i))
      Nat.zero_lt_one).inv

/-- The actual local map into the original target projective scheme. -/
def localMap (i : ι) : (sourceOpen f i).toScheme ⟶ ProjectiveSpace R (Coordinate f D) :=
  chartMap f D i ≫ (coordinateOpen R (Coordinate f D) (distinguished f D i)).ι

theorem localMap_eq (i : ι) :
    localMap f D i = (sourceOpen f i).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (chartRingHom f D i)) ≫
      Proj.awayι (homogeneousSubmodule (Coordinate f D) R) (X (distinguished f D i))
        (isHomogeneous_X R (distinguished f D i)) Nat.zero_lt_one := by
  rfl

/-- Finiteness of the original map makes the original source charts affine; the new
chart maps are closed immersions. -/
theorem chartMap_isClosedImmersion [IsFinite f] (i : ι) :
    IsClosedImmersion (chartMap f D i) := by
  let hU := (isAffineOpen_coordinateOpen R ι i).preimage f
  let : IsIso (sourceOpen f i).toSpecΓ := by
    change IsIso hU.isoSpec.hom
    infer_instance
  let := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (chartRingHom f D i)) (chartRingHom_surjective f D i)
  unfold chartMap
  infer_instance

/-- The same construction with only the original coordinate ratios is the original map. -/
theorem sourceChartRingHom_map (i : ι) :
    (sourceOpen f i).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sourceChartRingHom f i)) ≫
      Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) Nat.zero_lt_one =
        (sourceOpen f i).ι ≫ f := by
  change (sourceOpen f i).toSpecΓ ≫
    Spec.map (Proj.awayToSection (homogeneousSubmodule ι R) (X i) ≫
      f.app (coordinateOpen R ι i)) ≫ _ = _
  rw [Spec.map_comp]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_naturality f (coordinateOpen R ι i)]
  simp only [Category.assoc]
  change (f ∣_ coordinateOpen R ι i) ≫
    ((Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
      (isHomogeneous_X R i) Nat.zero_lt_one).hom ≫
        (Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
          (isHomogeneous_X R i) Nat.zero_lt_one).inv ≫ (coordinateOpen R ι i).ι) = _
  simp

/-- The original structural morphism is preserved on each original source chart. -/
@[reassoc]
theorem localMap_toSpec (i : ι) :
    localMap f D i ≫ toSpec R (Coordinate f D) = (sourceOpen f i).ι ≫ f ≫ toSpec R ι := by
  rw [localMap_eq, Category.assoc, Category.assoc, coordinateChart_toSpec,
    ← Spec.map_comp]
  conv_rhs => rw [← Category.assoc, ← sourceChartRingHom_map f i]
  rw [Category.assoc, Category.assoc,
    coordinateChart_toSpec, ← Spec.map_comp]
  congr 2
  ext r
  exact chartRingHom_coefficient f D i r

@[simp]
theorem chartValue_selected (i j : ι) :
    chartValue f D i (distinguished f D j) = sourceRatio f i j ^ D.d := by
  change sourceRatio f i j ^ (D.d - 1) * sourceRatio f i j = _
  rw [← pow_succ, Nat.sub_add_cancel D.one_le_d]

/-- Distinguished target coordinates cut out exactly the original source-chart overlaps. -/
theorem localMap_preimage_selected (i j : ι) :
    localMap f D i ⁻¹ᵁ coordinateOpen R (Coordinate f D) (distinguished f D j) =
      (sourceOpen f i).ι ⁻¹ᵁ sourceOpen f j := by
  rw [localMap_eq, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    coordinateChart_preimage_coordinateOpen, SpecMap_preimage_basicOpen]
  change (sourceOpen f i).toSpecΓ ⁻¹ᵁ
    PrimeSpectrum.basicOpen
      (chartRingHom f D i (coordinateRatio R (Coordinate f D)
        (distinguished f D i) (distinguished f D j))) = _
  rw [chartRingHom_ratio, chartValue_selected, Scheme.Opens.toSpecΓ_preimage_basicOpen,
    Y.basicOpen_pow _ (by have := D.one_le_d; omega)]
  change (sourceOpen f i).ι ⁻¹ᵁ Y.basicOpen
    ((f.app (coordinateOpen R ι i)) (coordinateRatioSection R ι i j)) = _
  rw [← Scheme.preimage_basicOpen, basicOpen_coordinateRatioSection,
    Scheme.Hom.preimage_inf]
  rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

private def overlapLeft (i j : ι) : coordinateRing R ι i →+* coordinateOverlapRing R ι i j :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R j) rfl

private def overlapRight (i j : ι) : coordinateRing R ι j →+* coordinateOverlapRing R ι i j :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R i) (by ring)

private theorem overlap_coefficient (i j : ι) (r : R) :
    overlapRight (R := R) i j (coordinateRingCoefficient R ι j r) =
      overlapLeft (R := R) i j (coordinateRingCoefficient R ι i r) := by
  simp only [overlapRight, overlapLeft, coordinateRingCoefficient, RingHom.comp_apply,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

private theorem overlap_ratio (i j k : ι) :
    overlapLeft (R := R) i j (coordinateRatio R ι i j) *
        overlapRight (R := R) i j (coordinateRatio R ι j k) =
      overlapLeft (R := R) i j (coordinateRatio R ι i k) := by
  apply HomogeneousLocalization.val_injective
  simp only [overlapLeft, overlapRight, coordinateRatio,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one]
  ring

/-- Compatible normalized chart coordinates define the same morphism to the native
projective scheme. This statement has no finite-morphism or Noetherian hypothesis. -/
theorem chart_maps_eq_of_rescaling {A : Type u} [CommRing A] (i j : ι)
    (φ : coordinateRing R ι i →+* A) (ψ : coordinateRing R ι j →+* A)
    (hc : ∀ r, φ (coordinateRingCoefficient R ι i r) =
      ψ (coordinateRingCoefficient R ι j r))
    (hu : IsUnit (φ (coordinateRatio R ι i j)))
    (ht : ∀ k, φ (coordinateRatio R ι i k) =
      φ (coordinateRatio R ι i j) * ψ (coordinateRatio R ι j k)) :
    Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) Nat.zero_lt_one =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Proj.awayι (homogeneousSubmodule ι R) (X j) (isHomogeneous_X R j) Nat.zero_lt_one := by
  let := (overlapLeft (R := R) i j).toAlgebra
  let : IsLocalization.Away (coordinateRatio R ι i j) (coordinateOverlapRing R ι i j) := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one, coordinateRatio,
      overlapLeft] using
      HomogeneousLocalization.Away.isLocalization_mul (𝒜 := homogeneousSubmodule ι R)
        (f := X i) (g := X j) (x := X i * X j) (d := 1) (e := 1)
        (isHomogeneous_X R i) (isHomogeneous_X R j) rfl (by decide)
  let ℓ : coordinateOverlapRing R ι i j →+* A :=
    IsLocalization.Away.lift (coordinateRatio R ι i j) hu
  have hLift : ℓ.comp (overlapLeft (R := R) i j) = φ :=
    IsLocalization.Away.lift_comp (coordinateRatio R ι i j) hu
  have hLift_apply (z : coordinateRing R ι i) : ℓ (overlapLeft (R := R) i j z) = φ z :=
    RingHom.congr_fun hLift z
  have hLiftRight : ℓ.comp (overlapRight (R := R) i j) = ψ := by
    apply coordinateRing_hom_ext
    · intro r
      change ℓ (overlapRight (R := R) i j (coordinateRingCoefficient R ι j r)) = _
      rw [overlap_coefficient]
      exact (RingHom.congr_fun hLift _).trans (hc r)
    · intro k
      apply hu.mul_left_cancel
      change φ (coordinateRatio R ι i j) *
        ℓ (overlapRight (R := R) i j (coordinateRatio R ι j k)) = _
      calc
        _ = ℓ (overlapLeft (R := R) i j (coordinateRatio R ι i j) *
            overlapRight (R := R) i j (coordinateRatio R ι j k)) := by
          rw [map_mul, hLift_apply]
        _ = ℓ (overlapLeft (R := R) i j (coordinateRatio R ι i k)) :=
          congrArg ℓ (overlap_ratio i j k)
        _ = φ (coordinateRatio R ι i k) := hLift_apply _
        _ = _ := ht k
  calc
    _ = Spec.map (CommRingCat.ofHom ℓ) ≫
        Spec.map (CommRingCat.ofHom (overlapLeft (R := R) i j)) ≫
          Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
            Nat.zero_lt_one := by
      rw [← Spec.map_comp_assoc]
      change _ = Spec.map (CommRingCat.ofHom (ℓ.comp (overlapLeft (R := R) i j))) ≫ _
      rw [hLift]
    _ = Spec.map (CommRingCat.ofHom ℓ) ≫
        Proj.awayι (homogeneousSubmodule ι R) (X i * X j)
          ((isHomogeneous_X R i).mul (isHomogeneous_X R j)) (by decide) := by
      rw [overlapLeft, Proj.SpecMap_awayMap_awayι]
    _ = Spec.map (CommRingCat.ofHom ℓ) ≫
        Spec.map (CommRingCat.ofHom (overlapRight (R := R) i j)) ≫
          Proj.awayι (homogeneousSubmodule ι R) (X j) (isHomogeneous_X R j)
            Nat.zero_lt_one := by
      rw [overlapRight, Proj.SpecMap_awayMap_awayι]
    _ = _ := by
      rw [← Spec.map_comp_assoc]
      change Spec.map (CommRingCat.ofHom (ℓ.comp (overlapRight (R := R) i j))) ≫ _ = _
      rw [hLiftRight]

theorem restrictPreimage_app {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W)
    (s : Γ(ProjectiveSpace R ι, W)) :
    restrictPreimageSections f h ((f.app W) s) =
      (f.app V) (sectionRestrict (ProjectiveSpace R ι) h s) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) s).symm

private theorem coefficientSections_agree (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) (r : R) :
    sectionRestrict (ProjectiveSpace R ι) hi
        ((Proj.awayToSection (homogeneousSubmodule ι R) (X i))
          (coordinateRingCoefficient R ι i r)) =
      sectionRestrict (ProjectiveSpace R ι) hj
        ((Proj.awayToSection (homogeneousSubmodule ι R) (X j))
          (coordinateRingCoefficient R ι j r)) := by
  dsimp only [coordinateOpen] at hi hj ⊢
  let c : Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop ((Scheme.ΓSpecIso (.of R)).inv r)
  have hi' : sectionRestrict (ProjectiveSpace R ι) le_top c =
      (Proj.awayToSection (homogeneousSubmodule ι R) (X i))
        (coordinateRingCoefficient R ι i r) :=
    constant_restriction R ι (X i) (isHomogeneous_X R i) Nat.zero_lt_one r
  have hj' : sectionRestrict (ProjectiveSpace R ι) le_top c =
      (Proj.awayToSection (homogeneousSubmodule ι R) (X j))
        (coordinateRingCoefficient R ι j r) :=
    constant_restriction R ι (X j) (isHomogeneous_X R j) Nat.zero_lt_one r
  rw [← hi', ← hj', sectionRestrict_comp, sectionRestrict_comp]

/-- Original structural coefficients agree under the actual restriction maps. -/
theorem sourceCoefficient_agree (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) (r : R) :
    restrictPreimageSections f hi (sourceCoefficient f i r) =
      restrictPreimageSections f hj (sourceCoefficient f j r) := by
  change restrictPreimageSections f hi ((f.app _)
    ((Proj.awayToSection (homogeneousSubmodule ι R) (X i))
      (coordinateRingCoefficient R ι i r))) =
      restrictPreimageSections f hj ((f.app _)
        ((Proj.awayToSection (homogeneousSubmodule ι R) (X j))
          (coordinateRingCoefficient R ι j r)))
  rw [restrictPreimage_app, restrictPreimage_app, coefficientSections_agree i j hi hj]

/-- Original pulled-back coordinate ratios obey the native projective transition equation. -/
theorem sourceRatio_transition (i j k : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    restrictPreimageSections f hj (sourceRatio f j k) =
      (f.app V) (coordinateTransitionOn R ι i j hi hj).val *
        restrictPreimageSections f hi (sourceRatio f i k) := by
  change restrictPreimageSections f hj ((f.app _) (coordinateRatioSection R ι j k)) =
    (f.app V) (coordinateTransitionOn R ι i j hi hj).val *
      restrictPreimageSections f hi ((f.app _) (coordinateRatioSection R ι i k))
  rw [restrictPreimage_app, restrictPreimage_app,
    coordinateRatioSection_transition_mul R ι k i j hi hj, map_mul]

/-- Every normalized target coordinate has the same degree-`d` transition, including
the mixed monomials and the supplied coefficient family. -/
theorem chartValue_transition (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j)
    (a : Coordinate f D) :
    restrictPreimageSections f hj (chartValue f D j a) =
      (f.app V) ((coordinateTransitionOn R ι i j hi hj) ^ D.d).val *
        restrictPreimageSections f hi (chartValue f D i a) := by
  rcases a with ⟨k, l⟩ | a
  · simp only [chartValue, map_mul, map_pow, Units.val_pow_eq_pow_val]
    rw [sourceRatio_transition f i j k hi hj, sourceRatio_transition f i j l hi hj,
      mul_pow]
    calc
      _ = (((f.app V) (coordinateTransitionOn R ι i j hi hj).val) ^ (D.d - 1) *
          (f.app V) (coordinateTransitionOn R ι i j hi hj).val) *
          (restrictPreimageSections f hi (sourceRatio f i k) ^ (D.d - 1) *
            restrictPreimageSections f hi (sourceRatio f i l)) := by ring
      _ = _ := by rw [← pow_succ, Nat.sub_add_cancel D.one_le_d]
  · exact D.transition i j V hi hj a

/-- Restricting a local map evaluates the same coordinate functions on the actual
smaller source open. -/
theorem localMap_restrict (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    Y.homOfLE (f.preimage_mono hi) ≫ localMap f D i =
      (f ⁻¹ᵁ V).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ((restrictPreimageSections f hi).comp (chartRingHom f D i))) ≫
          Proj.awayι (homogeneousSubmodule (Coordinate f D) R) (X (distinguished f D i))
            (isHomogeneous_X R (distinguished f D i)) Nat.zero_lt_one := by
  rw [localMap_eq]
  simp only [← Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc]
  rfl

/-- The actual local projective maps agree on every common base subopen. -/
theorem localMap_agree (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    Y.homOfLE (f.preimage_mono hi) ≫ localMap f D i =
      Y.homOfLE (f.preimage_mono hj) ≫ localMap f D j := by
  let φ := (restrictPreimageSections f hi).comp (chartRingHom f D i)
  let ψ := (restrictPreimageSections f hj).comp (chartRingHom f D j)
  let t : Γ(Y, f ⁻¹ᵁ V) :=
    (f.app V) ((coordinateTransitionOn R ι i j hi hj) ^ D.d).val
  have htrans (a : Coordinate f D) :
      ψ (coordinateRatio R (Coordinate f D) (distinguished f D j) a) =
        t * φ (coordinateRatio R (Coordinate f D) (distinguished f D i) a) := by
    dsimp only [φ, ψ, RingHom.comp_apply]
    rw [chartRingHom_ratio, chartRingHom_ratio]
    exact chartValue_transition f D i j hi hj a
  have hinv :
      φ (coordinateRatio R (Coordinate f D) (distinguished f D i) (distinguished f D j)) *
        t = 1 := by
    rw [mul_comm]
    simpa only [coordinateRatio_self, map_one] using (htrans (distinguished f D j)).symm
  have hu : IsUnit
      (φ (coordinateRatio R (Coordinate f D) (distinguished f D i) (distinguished f D j))) :=
    isUnit_iff_exists_inv.mpr ⟨t, hinv⟩
  have ht (a : Coordinate f D) :
      φ (coordinateRatio R (Coordinate f D) (distinguished f D i) a) =
        φ (coordinateRatio R (Coordinate f D) (distinguished f D i) (distinguished f D j)) *
          ψ (coordinateRatio R (Coordinate f D) (distinguished f D j) a) := by
    rw [htrans, ← mul_assoc, hinv, one_mul]
  have hc (r : R) :
      φ (coordinateRingCoefficient R (Coordinate f D) (distinguished f D i) r) =
        ψ (coordinateRingCoefficient R (Coordinate f D) (distinguished f D j) r) := by
    dsimp only [φ, ψ, RingHom.comp_apply]
    rw [chartRingHom_coefficient, chartRingHom_coefficient]
    exact sourceCoefficient_agree f i j hi hj r
  rw [localMap_restrict f D i hi, localMap_restrict f D j hj]
  exact congrArg (fun q => (f ⁻¹ᵁ V).toSpecΓ ≫ q)
    (chart_maps_eq_of_rescaling (distinguished f D i) (distinguished f D j) φ ψ hc hu ht)

/-- The original inverse-image coordinate charts cover the original source scheme. -/
theorem iSup_sourceOpen_eq_top : (⨆ i, sourceOpen f i) = ⊤ := by
  rw [show (⨆ i, sourceOpen f i) = f ⁻¹ᵁ (⨆ i, coordinateOpen R ι i) from
    (f.preimage_iSup _).symm, iSup_coordinateOpen_eq_top, f.preimage_top]

/-- The source cover used for the projective-coordinate construction. -/
abbrev sourceOpenCover : Y.OpenCover :=
  Y.openCoverOfIsOpenCover (sourceOpen f) (.mk (iSup_sourceOpen_eq_top f))

theorem localMap_compatible (i j : ι) :
    CategoryTheory.Limits.pullback.fst ((sourceOpenCover f).f i) ((sourceOpenCover f).f j) ≫
        localMap f D i =
      CategoryTheory.Limits.pullback.snd ((sourceOpenCover f).f i) ((sourceOpenCover f).f j) ≫
        localMap f D j := by
  change CategoryTheory.Limits.pullback.fst (sourceOpen f i).ι (sourceOpen f j).ι ≫
      localMap f D i = CategoryTheory.Limits.pullback.snd (sourceOpen f i).ι
        (sourceOpen f j).ι ≫ localMap f D j
  let h := isPullback_opens_inf (sourceOpen f i) (sourceOpen f j)
  apply (cancel_epi h.isoPullback.hom).mp
  simp only [← Category.assoc]
  rw [h.isoPullback_hom_fst, h.isoPullback_hom_snd]
  exact localMap_agree f D i j (V := coordinateOpen R ι i ⊓ coordinateOpen R ι j)
    inf_le_left inf_le_right

/-- The actual morphism from the original source to native polynomial projective space. -/
def map : Y ⟶ ProjectiveSpace R (Coordinate f D) :=
  (sourceOpenCover f).glueMorphisms (localMap f D) (localMap_compatible f D)

/-- The global morphism restricts to the constructed original chart morphism. -/
@[reassoc (attr := simp)]
theorem ι_map (i : ι) : (sourceOpen f i).ι ≫ map f D = localMap f D i :=
  (sourceOpenCover f).ι_glueMorphisms _ _ i

/-- The distinguished target coordinate opens have exactly the original source preimages. -/
theorem map_preimage_selected (j : ι) :
    map f D ⁻¹ᵁ coordinateOpen R (Coordinate f D) (distinguished f D j) = sourceOpen f j := by
  ext x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, sourceOpen f i by rw [iSup_sourceOpen_eq_top]; trivial)
  have h := congrArg
    (fun U : (sourceOpen f i).toScheme.Opens => (⟨x, hi⟩ : sourceOpen f i) ∈ U)
    ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R (Coordinate f D) (distinguished f D j))
      (ι_map f D i)).trans (localMap_preimage_selected f D i j))
  exact eq_iff_iff.mp h

/-- The actual global projective embedding map has its original structural factorization. -/
@[reassoc]
theorem map_toSpec : map f D ≫ toSpec R (Coordinate f D) = f ≫ toSpec R ι := by
  apply (sourceOpenCover f).hom_ext
  intro i
  change (sourceOpen f i).ι ≫ map f D ≫ toSpec R (Coordinate f D) =
    (sourceOpen f i).ι ≫ f ≫ toSpec R ι
  rw [ι_map_assoc]
  exact localMap_toSpec f D i

end AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
