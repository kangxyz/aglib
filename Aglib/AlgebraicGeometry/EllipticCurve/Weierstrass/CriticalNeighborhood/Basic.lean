/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.CoordinateDisplacement
public import Aglib.RingTheory.Etale.QuadraticDerivative
public import Aglib.RingTheory.Etale.QuadraticRoot
public import Aglib.AlgebraicGeometry.Curves.Nodal.CriticalPoint

/-!
Native extraction from the R5 local-model source
`PointedResolution.EtaleNode.CriticalNeighborhood`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`3725872e5a7325c9a1880131c16858ab6ccbb72001f24f2db312a327b41b8e6a`.
Exact actual critical coefficient-algebra constructors and translation/point/ideal APIs, source
  lines33–437. No local or DVR structure is assigned to the coefficient algebra.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
open Polynomial IsLocalRing WeierstrassCurve WeierstrassCurve.CriticalPoint Algebra.QuadraticRoot
universe u v

namespace WeierstrassCurve
variable {R : Type u} [CommRing R]

/-- An étale, faithfully flat coefficient algebra with a residue-field point and a critical
translation lifting `(x, y)`. The translated `b₂` is a unit; no local-ring structure on the
coefficient algebra is included. -/
structure CriticalNeighborhood [IsLocalRing R] (W : WeierstrassCurve R)
    (x : ResidueField R := 0) (y : ResidueField R := 0) where
  /-- The coefficient algebra in which the critical translation is constructed. -/
  Carrier : Type u
  [commRing : CommRing Carrier]
  [algebra : Algebra R Carrier]
  etale : _root_.Algebra.Etale R Carrier
  faithfullyFlat : Module.FaithfullyFlat R Carrier
  /-- The `R`-algebra map from the coefficient algebra to the original residue field. -/
  point : Carrier →ₐ[R] ResidueField R
  /-- A lift in `R` of the prescribed residue x-coordinate `x`. -/
  liftR : R
  /-- A lift in `R` of the prescribed residue y-coordinate `y`. -/
  liftT : R
  residue_lift_r : residue R liftR = x
  residue_lift_t : residue R liftT = y
  /-- The critical x-coordinate, congruent to `liftR` modulo the extended maximal ideal. -/
  r : Carrier
  /-- The critical y-coordinate, congruent to `liftT` modulo the extended maximal ideal. -/
  t : Carrier
  point_r : point r = x
  point_t : point t = y
  r_displacement_mem : r - algebraMap R Carrier liftR ∈
    Ideal.map (algebraMap R Carrier) (maximalIdeal R)
  t_displacement_mem : t - algebraMap R Carrier liftT ∈
    Ideal.map (algebraMap R Carrier) (maximalIdeal R)
  criticalX : (W.map (algebraMap R Carrier)).a₁ * t -
    (3 * r ^ 2 + 2 * (W.map (algebraMap R Carrier)).a₂ * r +
      (W.map (algebraMap R Carrier)).a₄) = 0
  criticalY : 2 * t + (W.map (algebraMap R Carrier)).a₁ * r +
    (W.map (algebraMap R Carrier)).a₃ = 0
  b2_isUnit : IsUnit (translate (W.map (algebraMap R Carrier)) r t).b₂

attribute [instance] CriticalNeighborhood.commRing CriticalNeighborhood.algebra


end WeierstrassCurve

namespace WeierstrassCurve.CriticalNeighborhood
variable {R : Type u} [CommRing R]

theorem criticalX_of_two_elimination (a₁ a₂ a₃ a₄ r t : R)
    (h2 : IsUnit (2 : R)) (hy : 2 * t + a₁ * r + a₃ = 0)
    (hr : 6 * r ^ 2 + (a₁ ^ 2 + 4 * a₂) * r + (a₁ * a₃ + 2 * a₄) = 0) :
    a₁ * t - (3 * r ^ 2 + 2 * a₂ * r + a₄) = 0 := by
  apply h2.mul_left_cancel
  simp only [mul_zero]
  linear_combination a₁ * hy - hr

/-- Polynomial elimination in the branch where a₁ is a unit. -/
theorem criticalX_of_a1_elimination (a₁ a₂ a₃ a₄ r t : R)
    (h1 : IsUnit a₁) (hy : 2 * t + a₁ * r + a₃ = 0)
    (ht : 12 * t ^ 2 + (12 * a₃ - a₁ * (a₁ ^ 2 + 4 * a₂)) * t +
      (3 * a₃ ^ 2 - 2 * a₂ * a₃ * a₁ + a₄ * a₁ ^ 2) = 0) :
    a₁ * t - (3 * r ^ 2 + 2 * a₂ * r + a₄) = 0 := by
  apply (h1.pow 2).mul_left_cancel
  simp only [mul_zero]
  linear_combination (-3 * (a₁ * r - (2 * t + a₃)) - 2 * a₂ * a₁) * hy - ht

/-- Build the neighbourhood by either of the two valid elimination directions.
The derivative localization itself makes the translated Hessian invertible. -/
def ofOrigin [IsLocalRing R] (W : WeierstrassCurve R)
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (hb : IsUnit W.b₂) : WeierstrassCurve.CriticalNeighborhood W := by
  classical
  by_cases h2 : IsUnit (2 : R)
  · let c := W.a₁ * W.a₃ + 2 * W.a₄
    have hc : c ∈ maximalIdeal R :=
      (maximalIdeal R).add_mem ((maximalIdeal R).mul_mem_left _ h3)
        ((maximalIdeal R).mul_mem_left _ h4)
    let S := Algebra.QuadraticRoot.RootAlgebra (6 : R) W.b₂ c
    let f : R →+* S := algebraMap R S
    let point := Algebra.QuadraticRoot.point (6 : R) W.b₂ c hb hc
    let r : S := Algebra.QuadraticRoot.root (6 : R) W.b₂ c
    let v : Rˣ := h2.unit
    have hv : (v : R) = 2 := h2.unit_spec
    let t : S := -(f W.a₁ * r + f W.a₃) * f ↑v⁻¹
    let I := Ideal.map f (maximalIdeal R)
    have hrm : r ∈ I := root_mem_extended_maximalIdeal _ _ _ hc
    have htm : t ∈ I := I.mul_mem_right _ (I.neg_mem
      (I.add_mem (I.mul_mem_left _ hrm) (Ideal.mem_map_of_mem f h3)))
    have hi : (2 : S) * f ↑v⁻¹ = 1 := by
      simpa only [map_mul, map_one, hv, map_ofNat] using congrArg f v.mul_inv
    have hy : 2 * t + f W.a₁ * r + f W.a₃ = 0 := by
      dsimp [t]
      linear_combination -(f W.a₁ * r + f W.a₃) * hi
    have hr := Algebra.QuadraticRoot.root_equation (6 : R) W.b₂ c
    change f 6 * r ^ 2 + f W.b₂ * r + f c = 0 at hr
    simp only [c, WeierstrassCurve.b₂, map_add, map_pow, map_mul, map_ofNat] at hr
    have hx : f W.a₁ * t - (3 * r ^ 2 + 2 * f W.a₂ * r + f W.a₄) = 0 := by
      exact criticalX_of_two_elimination _ _ _ _ _ _
        (by simpa only [map_ofNat] using h2.map f) hy hr
    have hpr : point r = 0 := Algebra.QuadraticRoot.point_root _ _ _ _ _
    have hpt : point t = 0 := by
      have h03 : residue R W.a₃ = 0 := (residue_eq_zero_iff _).mpr h3
      have hp3 : point (f W.a₃) = 0 := (point.commutes W.a₃).trans h03
      simp only [t, map_mul, map_neg, map_add, hpr, hp3, mul_zero, zero_add, neg_zero, zero_mul]
    have hbu : IsUnit (translate (W.map f) r t).b₂ := by
      rw [translate_b2, WeierstrassCurve.map_b₂]
      have h := root_derivative_isUnit (6 : R) W.b₂ c
      change IsUnit (2 * f 6 * r + f W.b₂) at h
      have he : 2 * f 6 * r + f W.b₂ = f W.b₂ + 12 * r := by
        simp only [map_ofNat]
        ring
      exact he ▸ h
    exact {
      Carrier := S
      etale := Algebra.QuadraticRoot.etale _ _ _
      faithfullyFlat := Algebra.QuadraticRoot.faithfullyFlat _ _ _ hb hc
      point := point
      liftR := 0
      liftT := 0
      residue_lift_r := map_zero _
      residue_lift_t := map_zero _
      r := r
      t := t
      point_r := hpr
      point_t := hpt
      r_displacement_mem := by simpa only [map_zero, sub_zero] using hrm
      t_displacement_mem := by simpa only [map_zero, sub_zero] using htm
      criticalX := hx
      criticalY := hy
      b2_isUnit := hbu }
  · have h1 : IsUnit W.a₁ := (two_or_a1_isUnit W hb).resolve_left h2
    let b : R := 12 * W.a₃ - W.a₁ * W.b₂
    let c : R := 3 * W.a₃ ^ 2 - 2 * W.a₂ * W.a₃ * W.a₁ + W.a₄ * W.a₁ ^ 2
    have hbu : IsUnit b := by
      have he : b = -(W.a₁ * W.b₂) + 12 * W.a₃ := by dsimp [b]; ring
      rw [he]
      exact IsLocalRing.isUnit_add_of_mem_maximalIdeal _ _ (h1.mul hb).neg ((maximalIdeal
        R).mul_mem_left _ h3)
    have hcm : c ∈ maximalIdeal R := by
      apply (residue_eq_zero_iff _).mp
      have hr3 := (residue_eq_zero_iff _).mpr h3
      have hr4 := (residue_eq_zero_iff _).mpr h4
      simp [c, map_sub, map_add, map_mul, map_pow, hr3, hr4]
    let S := Algebra.QuadraticRoot.RootAlgebra (12 : R) b c
    let f : R →+* S := algebraMap R S
    let point := Algebra.QuadraticRoot.point (12 : R) b c hbu hcm
    let t : S := Algebra.QuadraticRoot.root (12 : R) b c
    let v : Rˣ := h1.unit
    have hv : (v : R) = W.a₁ := h1.unit_spec
    let r : S := -(2 * t + f W.a₃) * f ↑v⁻¹
    let I := Ideal.map f (maximalIdeal R)
    have htm : t ∈ I := root_mem_extended_maximalIdeal _ _ _ hcm
    have hrm : r ∈ I := I.mul_mem_right _ (I.neg_mem
      (I.add_mem (I.mul_mem_left _ htm) (Ideal.mem_map_of_mem f h3)))
    have hi : f W.a₁ * f ↑v⁻¹ = 1 := by
      simpa only [map_mul, map_one, hv] using congrArg f v.mul_inv
    have hy : 2 * t + f W.a₁ * r + f W.a₃ = 0 := by
      dsimp [r]
      linear_combination -(2 * t + f W.a₃) * hi
    have ht := Algebra.QuadraticRoot.root_equation (12 : R) b c
    change f 12 * t ^ 2 + f b * t + f c = 0 at ht
    simp only [b, c, WeierstrassCurve.b₂, map_sub, map_add, map_pow, map_mul,
      map_ofNat] at ht
    have hx : f W.a₁ * t - (3 * r ^ 2 + 2 * f W.a₂ * r + f W.a₄) = 0 := by
      exact criticalX_of_a1_elimination _ _ _ _ _ _ (h1.map f) hy ht
    have hpt : point t = 0 := Algebra.QuadraticRoot.point_root _ _ _ _ _
    have hpr : point r = 0 := by
      have h03 : residue R W.a₃ = 0 := (residue_eq_zero_iff _).mpr h3
      have hp3 : point (f W.a₃) = 0 := (point.commutes W.a₃).trans h03
      simp only [r, map_mul, map_neg, map_add, hpt, hp3, mul_zero, zero_add, neg_zero, zero_mul]
    have hbu' : IsUnit (translate (W.map f) r t).b₂ := by
      rw [translate_b2, WeierstrassCurve.map_b₂]
      have h := root_derivative_isUnit (12 : R) b c
      change IsUnit (2 * f 12 * t + f b) at h
      have he : 2 * f 12 * t + f b = -f W.a₁ * (f W.b₂ + 12 * r) := by
        simp only [b, map_sub, map_mul, map_ofNat]
        linear_combination 12 * hy
      rw [he] at h
      exact isUnit_of_mul_isUnit_right h
    exact {
      Carrier := S
      etale := Algebra.QuadraticRoot.etale _ _ _
      faithfullyFlat := Algebra.QuadraticRoot.faithfullyFlat _ _ _ hbu hcm
      point := point
      liftR := 0
      liftT := 0
      residue_lift_r := map_zero _
      residue_lift_t := map_zero _
      r := r
      t := t
      point_r := hpr
      point_t := hpt
      r_displacement_mem := by simpa only [map_zero, sub_zero] using hrm
      t_displacement_mem := by simpa only [map_zero, sub_zero] using htm
      criticalX := hx
      criticalY := hy
      b2_isUnit := hbu' }

section NeighborhoodAPI
variable [IsLocalRing R] {W : WeierstrassCurve R}
  {x y : ResidueField R} (N : WeierstrassCurve.CriticalNeighborhood W x y)

/-- The actual scalar extension of the original equation. -/
def baseCurve : WeierstrassCurve N.Carrier := W.map (algebraMap R N.Carrier)

/-- The actual scale-one admissible translation on the scalar extension. -/
def translated : WeierstrassCurve N.Carrier := translate N.baseCurve N.r N.t

@[simp] theorem translated_a3 : N.translated.a₃ = 0 := by
  simpa only [translated, baseCurve, translate_a3] using N.criticalY

@[simp] theorem translated_a4 : N.translated.a₄ = 0 := by
  simpa only [translated, baseCurve, translate_a4, neg_eq_zero] using N.criticalX

theorem translated_b2_isUnit : IsUnit N.translated.b₂ := N.b2_isUnit

@[simp] theorem translated_discriminant :
    N.translated.Δ = algebraMap R N.Carrier W.Δ := by
  simp only [translated, baseCurve, translate_discriminant, WeierstrassCurve.map_Δ]

/-- Equality of actual polynomials after coordinate substitution. -/
theorem translated_polynomial_eval (x y : N.Carrier) :
    N.translated.toAffine.polynomial.evalEval x y =
      N.baseCurve.toAffine.polynomial.evalEval (x + N.r) (y + N.t) :=
  translate_polynomial_eval N.baseCurve N.r N.t x y

theorem critical_equations :
    N.baseCurve.toAffine.polynomialX.evalEval N.r N.t = 0 ∧
      N.baseCurve.toAffine.polynomialY.evalEval N.r N.t = 0 :=
  (translate_critical_iff N.baseCurve N.r N.t).mp
    ⟨N.translated_a3, N.translated_a4⟩

/-- The chosen point is over the original residue field, not an extension. -/
theorem point_structure (r : R) :
    N.point (algebraMap R N.Carrier r) = residue R r := N.point.commutes r

theorem point_surjective : Function.Surjective N.point := by
  intro x
  obtain ⟨r, hr⟩ := residue_surjective x
  exact ⟨algebraMap R N.Carrier r, (N.point_structure r).trans hr⟩

theorem carrier_nontrivial : Nontrivial N.Carrier := N.point.toRingHom.domain_nontrivial

/-- The actual closed point selected by the original residue-field map. -/
def pointIdeal : Ideal N.Carrier := RingHom.ker N.point.toRingHom

theorem pointIdeal_isMaximal : N.pointIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective N.point.toRingHom N.point_surjective

/-- This selected closed point lies over the original maximal ideal. -/
theorem pointIdeal_comap :
    N.pointIdeal.comap (algebraMap R N.Carrier) = maximalIdeal R := by
  ext r
  change N.point (algebraMap R N.Carrier r) = 0 ↔ r ∈ maximalIdeal R
  rw [N.point_structure, residue_eq_zero_iff]

/-- Vanishing of the constant coefficient is retained at the actual residue point. -/
theorem point_translated_a6 (N : WeierstrassCurve.CriticalNeighborhood W) (h6 : W.a₆ ∈
  maximalIdeal R) :
    N.point N.translated.a₆ = 0 := by
  have h06 : residue R W.a₆ = 0 := (residue_eq_zero_iff _).mpr h6
  simp [translated, baseCurve, translate_a6, WeierstrassCurve.Affine.evalEval_polynomial,
    map_sub, map_add, map_mul, map_pow, N.point_r, N.point_t, AlgHom.commutes, h06]

/-- An actual residue point on the original curve remains on the translated
curve at the origin of the selected residue fibre. -/
theorem point_translated_a6_of_equation
    (he : (W.map (residue R)).toAffine.Equation x y) :
    N.point N.translated.a₆ = 0 := by
  simp only [WeierstrassCurve.Affine.Equation,
    WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at he
  simpa only [translated, baseCurve, translate_a6,
    WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    map_neg, map_sub, map_add, map_mul, map_pow, N.point_r, N.point_t,
    AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, neg_eq_zero] using he

/-- Invertibility of the actual Hessian on the constructed neighbourhood. -/
theorem criticalHessianDet_isUnit : IsUnit (criticalHessianDet N.baseCurve N.r) := by
  rw [criticalHessianDet_eq]
  have h := N.b2_isUnit
  rw [translate_b2] at h
  exact h.neg

end NeighborhoodAPI

/-- Scale-one translation commutes with the actual coefficient extension. -/
theorem translate_map {A : Type u} [CommRing A]
    (f : R →+* A) (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).map f = translate (W.map f) (f r) (f t) := by
  ext <;> simp [translate, WeierstrassCurve.variableChange_def, map_ofNat]

/-- Starting with the actual residue-node equations and nonzero Hessian,
construct a pointed étale neighbourhood and a critical translation of the
same basechanged equation. No lift of the critical point is supplied. -/
def ofResidueNode [IsLocalRing R] (W : WeierstrassCurve R)
    (x y : ResidueField R)
    (_he : (W.map (residue R)).toAffine.Equation x y)
    (hx : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0)
    (hy : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0)
    (hh : criticalHessianDet (W.map (residue R)) x ≠ 0) : WeierstrassCurve.CriticalNeighborhood W
      x y := by
  let r₀ : R := Classical.choose (residue_surjective x)
  let t₀ : R := Classical.choose (residue_surjective y)
  have hr₀ : residue R r₀ = x := Classical.choose_spec (residue_surjective x)
  have ht₀ : residue R t₀ = y := Classical.choose_spec (residue_surjective y)
  simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄] at hx
  simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hy
  have h3 : (translate W r₀ t₀).a₃ ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [translate_a3, map_add, map_mul, map_ofNat, hr₀, ht₀] using hy
  have h4 : (translate W r₀ t₀).a₄ ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [translate_a4, map_neg, map_sub, map_add, map_mul, map_pow,
      map_ofNat, hr₀, ht₀, neg_eq_zero] using hx
  have hb : IsUnit (translate W r₀ t₀).b₂ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [criticalHessianDet_eq, neg_ne_zero] at hh
    simpa only [translate_b2, map_add, map_mul, map_ofNat, hr₀,
      WeierstrassCurve.map_b₂] using hh
  let N := ofOrigin (translate W r₀ t₀) h3 h4 hb
  let S := N.Carrier
  let f : R →+* S := algebraMap R S
  let r : S := f r₀ + N.r
  let t : S := f t₀ + N.t
  have htranslation : translate (W.map f) r t = N.translated := by
    change translate (W.map f) (f r₀ + N.r) (f t₀ + N.t) =
      translate ((translate W r₀ t₀).map f) N.r N.t
    rw [translate_map, translate_translate]
  have h3' : (translate (W.map f) r t).a₃ = 0 := by
    rw [htranslation]
    exact N.translated_a3
  have h4' : (translate (W.map f) r t).a₄ = 0 := by
    rw [htranslation]
    exact N.translated_a4
  exact {
    Carrier := S
    etale := N.etale
    faithfullyFlat := N.faithfullyFlat
    point := N.point
    liftR := r₀ + N.liftR
    liftT := t₀ + N.liftT
    residue_lift_r := by rw [map_add, hr₀, N.residue_lift_r, add_zero]
    residue_lift_t := by rw [map_add, ht₀, N.residue_lift_t, add_zero]
    r := r
    t := t
    point_r := by
      simp only [r, map_add, N.point_r, add_zero]
      exact (N.point.commutes r₀).trans hr₀
    point_t := by
      simp only [t, map_add, N.point_t, add_zero]
      exact (N.point.commutes t₀).trans ht₀
    r_displacement_mem := by
      change r - f (r₀ + N.liftR) ∈ Ideal.map f (maximalIdeal R)
      have he : r - f (r₀ + N.liftR) = N.r - f N.liftR := by
        dsimp [r]
        rw [map_add]
        ring
      rw [he]
      exact N.r_displacement_mem
    t_displacement_mem := by
      change t - f (t₀ + N.liftT) ∈ Ideal.map f (maximalIdeal R)
      have he : t - f (t₀ + N.liftT) = N.t - f N.liftT := by
        dsimp [t]
        rw [map_add]
        ring
      rw [he]
      exact N.t_displacement_mem
    criticalX := by simpa only [translate_a4, neg_eq_zero] using h4'
    criticalY := by simpa only [translate_a3] using h3'
    b2_isUnit := by rw [show algebraMap R S = f from rfl, htranslation]; exact N.b2_isUnit }

section NeighborhoodAPI
variable [IsLocalRing R] {W : WeierstrassCurve R}
  {x y : ResidueField R} (N : WeierstrassCurve.CriticalNeighborhood W x y)

/-- The scalar-extension and original residue-equation triangle commutes. -/
theorem baseCurve_map_point :
    N.baseCurve.map N.point.toRingHom = W.map (residue R) := by
  rw [baseCurve, WeierstrassCurve.map_map]
  congr 1
  ext a
  exact N.point_structure a

/-- Exact equality of the pulled-back coordinate-centre ideals in every
actual target coefficient/coordinate ring. No equality of schemes is assumed. -/
theorem center_ideal_eq {A : Type v} [CommRing A] (f : N.Carrier →+* A) (X Y : A) :
    Ideal.map f (Ideal.map (algebraMap R N.Carrier) (maximalIdeal R)) ⊔
        Ideal.span {X - f (algebraMap R N.Carrier N.liftR),
          Y - f (algebraMap R N.Carrier N.liftT)} =
      Ideal.map f (Ideal.map (algebraMap R N.Carrier) (maximalIdeal R)) ⊔
        Ideal.span {X - f N.r, Y - f N.t} := by
  apply Ideal.coordinate_center_ideal_eq
  · simpa only [map_sub] using Ideal.mem_map_of_mem f N.r_displacement_mem
  · simpa only [map_sub] using Ideal.mem_map_of_mem f N.t_displacement_mem

/-- The actual translated equation specializes to translation by the given
original-residue coordinates. -/
theorem translated_map_point :
    N.translated.map N.point.toRingHom =
      translate (W.map (residue R)) x y := by
  rw [translated, translate_map, N.baseCurve_map_point]
  change translate (W.map (residue R)) (N.point N.r) (N.point N.t) = _
  rw [N.point_r, N.point_t]

end NeighborhoodAPI

/-- The constructor applied to an actual residue node has zero constant
coefficient at its selected point, in addition to its exact critical equations. -/
theorem ofResidueNode_point_a6 [IsLocalRing R] (W : WeierstrassCurve R)
    (x y : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation x y)
    (hx : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0)
    (hy : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0)
    (hh : criticalHessianDet (W.map (residue R)) x ≠ 0) :
    let N := ofResidueNode W x y he hx hy hh
    N.point N.translated.a₆ = 0 :=
  (ofResidueNode W x y he hx hy hh).point_translated_a6_of_equation he

end WeierstrassCurve.CriticalNeighborhood
