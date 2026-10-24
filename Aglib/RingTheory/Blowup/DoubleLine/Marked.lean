/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.DoubleLine.Child
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Corrected marked Case-II continuation

All equations concern the original local ring, its literal saturated chart,
and its actual prime localization. The marker is the simple root of the
original pure binary cubic. Its other cubic terms remain unrestricted.
The original ordinary-blowup normality and full canonical tangent kernel
are genuine inputs; no desired marked transition or hypersurface model is
assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A]

/-- Coefficients of one fixed actual cubic relation. -/
structure CubicCoefficients (A : Type u) where
  /-- The coefficient of `t³` in the fixed cubic. -/
  a0 : A
  /-- The coefficient of `t²s` in the fixed cubic. -/
  a1 : A
  /-- The coefficient of `ts²` in the fixed cubic. -/
  a2 : A
  /-- The coefficient of `s³` in the fixed cubic. -/
  a3 : A
  /-- The coefficient of `zt²` in the fixed cubic. -/
  b0 : A
  /-- The coefficient of `zts` in the fixed cubic. -/
  b1 : A
  /-- The coefficient of `zs²` in the fixed cubic. -/
  b2 : A
  /-- The coefficient of `z²t` in the fixed cubic. -/
  c0 : A
  /-- The coefficient of `z²s` in the fixed cubic. -/
  c1 : A
  /-- The coefficient of `z³` in the fixed cubic. -/
  d0 : A

namespace CubicCoefficients

/-- The fixed original polynomial evaluated on the original generators. -/
def value (C : CubicCoefficients A) (t s z : A) : A :=
  z ^ 2 + (C.a0 * t ^ 3 + C.a1 * t ^ 2 * s + C.a2 * t * s ^ 2 + C.a3 * s ^ 3) +
    z * (C.b0 * t ^ 2 + C.b1 * t * s + C.b2 * s ^ 2) +
    z ^ 2 * (C.c0 * t + C.c1 * s) + C.d0 * z ^ 3

/-- The same pure coefficients reduced through the original residue map. -/
def residueCubic [IsLocalRing A] (C : CubicCoefficients A) : (IsLocalRing.ResidueField A)[X] :=
  IsLocalRing.residueBinaryCubic C.a0 C.a1 C.a2 C.a3

/-- Interchanging the two actual tangent-plane generators reverses the pure coefficients. -/
def swap (C : CubicCoefficients A) : CubicCoefficients A :=
  ⟨C.a3, C.a2, C.a1, C.a0, C.b2, C.b1, C.b0, C.c1, C.c0, C.d0⟩

theorem swap_value (C : CubicCoefficients A) (t s z : A) :
    C.swap.value s t z = C.value t s z := by
  dsimp only [swap, value]
  ring

end CubicCoefficients

variable [IsLocalRing A]

/-- One true original cubic equation, allowing its genuine fourth-order remainder. -/
structure CubicRelation (t s z : maximalIdeal A) where
  /-- The coefficients of the original cubic part of the relation. -/
  coefficients : CubicCoefficients A
  /-- The actual fourth-order remainder added to the cubic part. -/
  remainder : A
  remainder_mem : remainder ∈ maximalIdeal A ^ 4
  equation : coefficients.value (t : A) (s : A) (z : A) + remainder = 0

namespace CubicRelation

/-- The same original relation on the genuine second projective chart. -/
def swap {t s z : maximalIdeal A} (F : CubicRelation t s z) : CubicRelation s t z where
  coefficients := F.coefficients.swap
  remainder := F.remainder
  remainder_mem := F.remainder_mem
  equation := by rw [CubicCoefficients.swap_value]; exact F.equation

/-- Divide the fixed true relation in the actual saturated chart. -/
theorem divided {t s z : maximalIdeal A} (F : CubicRelation t s z) :
    ∃ r : saturatedChart A (maximalIdeal A) (t : A),
      let φ := algebraMap A (saturatedChart A (maximalIdeal A) (t : A))
      let τ := φ (t : A)
      let U := fractionElement (maximalIdeal A) t s
      let V := fractionElement (maximalIdeal A) t z
      let C := F.coefficients
      V ^ 2 + τ * (φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3) +
        τ * V * (φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
          φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2) + τ ^ 2 * r = 0 :=
  exists_divided_cubic_relation t s z F.coefficients.a0 F.coefficients.a1
    F.coefficients.a2 F.coefficients.a3 F.coefficients.b0 F.coefficients.b1
    F.coefficients.b2 F.coefficients.c0 F.coefficients.c1 F.coefficients.d0
    F.remainder F.remainder_mem F.equation

end CubicRelation

/-- The actual cone equivalence with all original coefficient and symbol formulas. -/
structure DoubleLinePresentation (t s z : maximalIdeal A) where
  /-- The original associated graded ring identified with the double-line cone quotient. -/
  equivalence : (maximalIdeal A).associatedGraded ≃+*
    Polynomial.quotientCone ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
  parameter : equivalence.toRingHom
    (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) t)) =
        Polynomial.quotientConeParameter ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
  other : equivalence.toRingHom
    (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) s)) =
        Polynomial.quotientConeMk ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
          (C (C (X : (IsLocalRing.ResidueField A)[X])))
  square : equivalence.toRingHom
    (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) z)) =
        Polynomial.quotientConeMk ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
          (C (X : (IsLocalRing.ResidueField A)[X][X]))
  coefficient : ∀ a : A, equivalence.toRingHom
    (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (algebraMap A (reesAlgebra (maximalIdeal A)) a)) =
        Polynomial.quotientConeMk ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
          (C (C (C (residue A a))))

namespace DoubleLinePresentation

variable {t s z : maximalIdeal A} (E : DoubleLinePresentation t s z)

/-- The actual reduced exceptional map, retaining the chosen original presentation. -/
def reduction : saturatedChart A (maximalIdeal A) (t : A) →+* (IsLocalRing.ResidueField A)[X] :=
  reesAlgebra.reducedDoubleLineChartMap t E.equivalence E.parameter

theorem reduction_surjective : Function.Surjective E.reduction :=
  reesAlgebra.reducedDoubleLineChartMap_surjective t E.equivalence E.parameter

theorem reduction_kernel : RingHom.ker E.reduction = Ideal.span
    ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
      fractionElement (maximalIdeal A) t z} :
        Set (saturatedChart A (maximalIdeal A) (t : A))) :=
  reesAlgebra.ker_reducedDoubleLineChartMap t z E.equivalence E.parameter E.square

theorem reduction_other : E.reduction (fractionElement (maximalIdeal A) t s) = X :=
  reesAlgebra.reducedDoubleLineChartMap_fraction t s E.equivalence E.parameter E.other

theorem reduction_coefficient (a : A) :
    E.reduction (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a) = C (residue A a) :=
  reesAlgebra.reducedDoubleLineChartMap_base t E.equivalence E.parameter a (E.coefficient a)

end DoubleLinePresentation

/-- Normality proves nonvanishing of these fixed original cubic coefficients,
including an arbitrary true fourth-order remainder. -/
theorem fixed_cubic_nonzero [IsDomain A] [IsNoetherianRing A]
    {t s z : maximalIdeal A} (ht0 : (t : A) ≠ 0)
    [IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A))]
    (E : DoubleLinePresentation t s z) (F : CubicRelation t s z) :
    F.coefficients.residueCubic ≠ 0 := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsDomain (Localization.Away (t : A)) := Localization.Away.isDomain ht0
  let : IsDomain S := inferInstance
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let cA : A →+* S := algebraMap A S
  let τ := cA (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  have htC : τ ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (t : A)) (t : A)).ne_zero hz
  obtain ⟨r, hr⟩ := F.divided
  let e := reesAlgebra.exceptionalQuotientConeEquiv (maximalIdeal A) t
    ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2) E.equivalence E.parameter
  let φ : S →+* (IsLocalRing.ResidueField A)[X][X] ⧸
      Ideal.span {(X : (IsLocalRing.ResidueField A)[X][X]) ^ 2} :=
    e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {τ}))
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {τ} := by
    ext x
    change e (Ideal.Quotient.mk (Ideal.span {τ}) x) = 0 ↔ x ∈ Ideal.span {τ}
    constructor
    · intro hx
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply e.injective
      simpa only [map_zero] using hx
    · intro hx
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hV : φ V = Polynomial.doubleLineCoordinate (R := (IsLocalRing.ResidueField A)[X]) := by
    simpa only [φ, e, τ, cA, V, RingHom.comp_apply, Polynomial.doubleLineCoordinate, eval_C] using
      reesAlgebra.exceptionalQuotientConeEquiv_mk_fraction (maximalIdeal A) t
        ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2) E.equivalence E.parameter z
        (C (X : (IsLocalRing.ResidueField A)[X][X])) E.square
  let q : Ideal S := Ideal.span ({τ, V} : Set S)
  let : q.IsPrime := Ideal.span_pair_isPrime_of_doubleLine_quotient φ hφ hker hV
  have hann : ∀ b : S, b * V ∈ Ideal.span {τ} → b ∈ q :=
    Ideal.mul_mem_parameter_implies_mem_pair_of_doubleLine_quotient φ hφ hker hV
  let C := F.coefficients
  let H := cA C.a0 + cA C.a1 * U + cA C.a2 * U ^ 2 + cA C.a3 * U ^ 3
  let L := cA C.b0 + cA C.b1 * U + cA C.b2 * U ^ 2 +
    cA C.c0 * V + cA C.c1 * U * V + cA C.d0 * V ^ 2
  have hdiv : V ^ 2 + τ * H + τ * V * L + τ ^ 2 * r = 0 := hr
  have hunit := Ideal.isUnit_cubicCoefficient_at_generic_doubleLine q H L r htC rfl hann hdiv
  let D : Type u := Localization.AtPrime q
  let c : A →+* D := localizedChartMap (maximalIdeal A) (t : A) q
  let : IsLocalHom c := localizedChartMap_isLocal_of_parameter_mem t q
    (Ideal.subset_span (Or.inl rfl))
  apply IsLocalRing.residueBinaryCubic_ne_zero_of_isUnit c (algebraMap S D U)
    C.a0 C.a1 C.a2 C.a3
  simpa only [H, c, cA, localizedChartMap, RingHom.comp_apply,
    map_add, map_mul, map_pow] using hunit

end Localization.Away.SaturatedChart

namespace MvPolynomial

variable {k : Type u} [Field k]

private theorem homogeneous_linear_three {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) :
    ∃ a b c : k, L = C a * X 0 + C b * X 1 + C c * X 2 := by
  have hmem : L ∈ Submodule.span k (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  clear hL
  induction hmem using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    fin_cases i
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨a, b, c, rfl⟩ := ihf
    obtain ⟨d, e, f, rfl⟩ := ihg
    refine ⟨a + d, b + e, c + f, ?_⟩
    simp only [map_add]
    ring
  | smul a f hf ih =>
    obtain ⟨b, c, d, rfl⟩ := ih
    refine ⟨a * b, a * c, a * d, ?_⟩
    simp only [Algebra.smul_def, algebraMap_eq, map_mul]
    ring

/-- A monic two-coordinate quadratic in a genuine linear-square kernel has
its square alignment over the original field, without extracting a square root. -/
theorem exists_original_square_alignment (c e : k)
    (L : MvPolynomial (Fin 3) k) (hL : L.IsHomogeneous 1)
    (hmem : doubleLineChildQuadratic 0 c e ∈ Ideal.span {L ^ 2}) :
    ∃ μ : k, c = 2 * μ ∧ e = μ ^ 2 ∧
      Ideal.span ({L ^ 2} : Set (MvPolynomial (Fin 3) k)) =
        Ideal.span {(X 1 + C μ * X 2) ^ 2} := by
  have hh : (doubleLineChildQuadratic 0 c e).IsHomogeneous 2 :=
    (isHomogeneous_X_pow 1 2).add
      ((isHomogeneous_X k 2).mul
        (((isHomogeneous_C_mul_X (0 : k) 0).add (isHomogeneous_C_mul_X c 1)).add
          (isHomogeneous_C_mul_X e 2)))
  have hn : doubleLineChildQuadratic 0 c e ≠ 0 := by
    intro hz
    have h := congrArg (eval₂Hom (RingHom.id k) ![0, 1, 0]) hz
    simp [doubleLineChildQuadratic] at h
  obtain ⟨δ, hδ⟩ := eq_scalar_square_of_mem_span_square hh hn hL hmem
  obtain ⟨a, b, d, hlin⟩ := homogeneous_linear_three hL
  have hb : 1 = δ * b ^ 2 := by
    have h := congrArg (eval₂Hom (RingHom.id k) ![0, 1, 0]) hδ
    simpa [doubleLineChildQuadratic, hlin] using h
  have hd : e = δ * d ^ 2 := by
    have h := congrArg (eval₂Hom (RingHom.id k) ![0, 0, 1]) hδ
    simpa [doubleLineChildQuadratic, hlin] using h
  have hbd : 1 + (c + e) = δ * (b + d) ^ 2 := by
    have h := congrArg (eval₂Hom (RingHom.id k) ![0, 1, 1]) hδ
    simpa [doubleLineChildQuadratic, hlin] using h
  have hc : c = 2 * (δ * b * d) := by linear_combination hbd - hb - hd
  have he : e = (δ * b * d) ^ 2 := by
    calc
      e = δ * d ^ 2 := hd
      _ = (δ * b ^ 2) * (δ * d ^ 2) := by rw [← hb, one_mul]
      _ = (δ * b * d) ^ 2 := by ring
  have hδ0 : δ ≠ 0 := by intro hz; simp [hz] at hb
  have hpoly : doubleLineChildQuadratic 0 c e =
      (X 1 + C (δ * b * d) * X 2) ^ 2 := by
    rw [hc, he]
    simp only [doubleLineChildQuadratic, map_zero, zero_mul, zero_add, map_mul, map_ofNat, map_pow]
    ring
  refine ⟨δ * b * d, hc, he, ?_⟩
  rw [← hpoly, hδ]
  exact (Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr hδ0).map (C : k →+* MvPolynomial (Fin 3) k)) (L ^ 2)).symm

end MvPolynomial

namespace MvPolynomial

variable {k : Type u} [CommRing k]

/-- The invertible square-coordinate shift, with the other two coordinates fixed. -/
def squareShiftHom (μ : k) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![X 0, X 1 + C μ * X 2, X 2]

@[simp] theorem squareShiftHom_zero (μ : k) : squareShiftHom μ (X 0) = X 0 := by
  simp [squareShiftHom]

@[simp] theorem squareShiftHom_one (μ : k) : squareShiftHom μ (X 1) = X 1 + C μ * X 2 := by
  simp [squareShiftHom]

@[simp] theorem squareShiftHom_two (μ : k) : squareShiftHom μ (X 2) = X 2 := by
  simp [squareShiftHom]

theorem squareShiftHom_comp (μ : k) :
    (squareShiftHom μ).comp (squareShiftHom (-μ)) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply, squareShiftHom]

/-- The original inverse shift is its actual algebra inverse. -/
def squareShift (μ : k) : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  AlgEquiv.ofAlgHom (squareShiftHom μ) (squareShiftHom (-μ))
    (squareShiftHom_comp μ) (by simpa only [neg_neg] using squareShiftHom_comp (-μ))

end MvPolynomial

namespace IsLocalRing

variable {B : Type u} [CommRing B] [IsLocalRing B]

omit [IsLocalRing B] in
private theorem original_degreeOne_smul (I : Ideal B) (a : B) (x : I) :
    Ideal.associatedGradedDegreeOneLinear I (a • x) =
      algebraMap B I.associatedGraded a * Ideal.associatedGradedDegreeOneLinear I x := by
  let π : reesAlgebra I →+* I.associatedGraded := Ideal.Quotient.mk I.associatedGradedIdeal
  have h : reesAlgebra.degreeOne I (a • x) =
      algebraMap B (reesAlgebra I) a * reesAlgebra.degreeOne I x := by
    apply Subtype.ext
    change Polynomial.monomial 1 (a * (x : B)) =
      Polynomial.C a * Polynomial.monomial 1 (x : B)
    exact Polynomial.C_mul_monomial.symm
  change π (reesAlgebra.degreeOne I (a • x)) =
    π (algebraMap B (reesAlgebra I) a) * π (reesAlgebra.degreeOne I x)
  rw [h, π.map_mul]

/-- The shifted generators are actual elements of the same original maximal ideal. -/
def squareShiftTriple (g : Fin 3 → maximalIdeal B) (μ : B) : Fin 3 → maximalIdeal B :=
  ![g 0, g 1 + μ • g 2, g 2]

theorem squareShiftTriple_triple (u v t : maximalIdeal B) (μ : B) :
    squareShiftTriple ![u, v, t] μ = ![u, v + μ • t, t] := by
  funext i
  fin_cases i <;> rfl

/-- The original canonical tangent map commutes with the actual coordinate shift. -/
theorem cotangentPolynomialMap_squareShift (g : Fin 3 → maximalIdeal B) (μ : B) :
    Ideal.cotangentPolynomialMap (maximalIdeal B) (squareShiftTriple g μ) =
      (Ideal.cotangentPolynomialMap (maximalIdeal B) g).comp
        (MvPolynomial.squareShiftHom (k := B ⧸ maximalIdeal B)
          (Ideal.Quotient.mk (maximalIdeal B) μ)) := by
  let I := maximalIdeal B
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [squareShiftTriple, AlgHom.comp_apply, Ideal.cotangentPolynomialMap_X]
  · change Ideal.cotangentPolynomialMap I (squareShiftTriple g μ) (MvPolynomial.X 1) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.squareShiftHom (k := B ⧸ I) (Ideal.Quotient.mk I μ)
          (MvPolynomial.X 1))
    rw [MvPolynomial.squareShiftHom_one]
    simp only [map_add, map_mul, Ideal.cotangentPolynomialMap_X,
      Ideal.cotangentPolynomialMap_C_mk]
    change Ideal.associatedGradedDegreeOneLinear I (g 1 + μ • g 2) =
      Ideal.associatedGradedDegreeOneLinear I (g 1) +
        algebraMap B I.associatedGraded μ * Ideal.associatedGradedDegreeOneLinear I (g 2)
    rw [map_add, original_degreeOne_smul]
  · simp [squareShiftTriple, AlgHom.comp_apply, Ideal.cotangentPolynomialMap_X]

/-- The full actual kernel becomes the square of the shifted coordinate. -/
theorem cotangentKernel_squareShift (g : Fin 3 → maximalIdeal B) (μ : B)
    (hker : doubleLineChildCotangentKernel B g =
      Ideal.span {(MvPolynomial.X 1 + MvPolynomial.C (residue B μ) * MvPolynomial.X 2) ^ 2}) :
    doubleLineChildCotangentKernel B (squareShiftTriple g μ) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField B)) ^ 2} := by
  let σ := MvPolynomial.squareShift (residue B μ)
  have hmap : (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3)
      (IsLocalRing.ResidueField B)) ^ 2}).map σ.toRingHom =
      Ideal.span {(MvPolynomial.X 1 + MvPolynomial.C (residue B μ) * MvPolynomial.X 2) ^ 2} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change σ (MvPolynomial.X 1 ^ 2) = _
    rw [map_pow]
    change (MvPolynomial.squareShiftHom (residue B μ) (MvPolynomial.X 1)) ^ 2 = _
    rw [MvPolynomial.squareShiftHom_one]
  have hcomp : doubleLineChildCotangentKernel B (squareShiftTriple g μ) =
      (doubleLineChildCotangentKernel B g).comap σ.toRingHom := by
    ext p
    change Ideal.cotangentPolynomialMap (maximalIdeal B) (squareShiftTriple g μ) p = 0 ↔
      Ideal.cotangentPolynomialMap (maximalIdeal B) g (σ p) = 0
    rw [cotangentPolynomialMap_squareShift]
    rfl
  rw [hcomp, hker, ← hmap]
  exact Ideal.comap_map_of_bijective σ.toRingHom σ.bijective

/-- Square alignment gives exact actual coefficients in the maximal ideal.
The exponent is two for marked continuation and three for triple-root entry. -/
theorem exists_exact_aligned_relation
    (t u v : maximalIdeal B) (a L H : B) (m : ℕ) (hm : 2 ≤ m)
    (hrel : (v : B) ^ 2 + a * (t : B) * (u : B) ^ m +
      (t : B) * (v : B) * L + (t : B) ^ 2 * H = 0)
    (ell : MvPolynomial (Fin 3) (IsLocalRing.ResidueField B)) (hell : ell.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel B ![u, v, t] = Ideal.span {ell ^ 2}) :
    ∃ μ P Q : B,
      P ∈ maximalIdeal B ∧ Q ∈ maximalIdeal B ∧
      ((v : B) + μ * (t : B)) ^ 2 + a * (t : B) * (u : B) ^ m +
        (t : B) * ((v : B) + μ * (t : B)) * P + (t : B) ^ 2 * Q = 0 ∧
      doubleLineChildCotangentKernel B (squareShiftTriple ![u, v, t] μ) =
        Ideal.span
          {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField B)) ^ 2} := by
  have hm0 : m - 1 ≠ 0 := by omega
  have hu : residue B (u : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr u.property
  have hcu : residue B (a * (u : B) ^ (m - 1)) = 0 := by
    rw [map_mul, map_pow, hu, zero_pow hm0, mul_zero]
  have hrel' : (v : B) ^ 2 + (t : B) *
      (a * (u : B) ^ (m - 1) * (u : B) + L * (v : B) + H * (t : B)) = 0 := by
    have hm1 : m = (m - 1) + 1 := by omega
    rw [hm1, pow_succ] at hrel
    linear_combination hrel
  have hf := doubleLineChildQuadratic_mem_cotangent_kernel t v u
    (a * (u : B) ^ (m - 1)) L H hrel'
  rw [hcu, hker] at hf
  obtain ⟨lam, hlamL, hlamH, hlamker⟩ :=
    MvPolynomial.exists_original_square_alignment (residue B L) (residue B H) ell hell hf
  obtain ⟨μ, hμ⟩ := residue_surjective (R := B) lam
  let P := L - 2 * μ
  let Q := H + μ ^ 2 - μ * L
  have hP : P ∈ maximalIdeal B := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residue B (L - 2 * μ) = 0
    rw [map_sub, map_mul, map_ofNat, hμ, hlamL, sub_self]
  have hQ : Q ∈ maximalIdeal B := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residue B (H + μ ^ 2 - μ * L) = 0
    rw [map_sub, map_add, map_pow, map_mul, hμ, hlamH, hlamL]
    ring
  refine ⟨μ, P, Q, hP, hQ, ?_, ?_⟩
  · dsimp only [P, Q]
    linear_combination hrel
  · apply cotangentKernel_squareShift
    rw [hker, hμ]
    exact hlamker

end IsLocalRing

namespace Ideal

variable {S k : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field k]

/-- A dimension-two actual exceptional child is a closed polynomial point,
not the generic double-line prime. Its irreducible parameter is constructed. -/
theorem exists_monic_irreducible_of_doubleLine_child
    (red : S →+* k[X]) (hred : Function.Surjective red) (t v : S)
    (hker : RingHom.ker red = Ideal.span ({t, v} : Set S)) (ht0 : t ≠ 0)
    (hv2 : v ^ 2 ∈ Ideal.span ({t} : Set S))
    (P : Ideal S) [P.IsPrime] (htP : t ∈ P)
    (hd : ringKrullDim (Localization.AtPrime P) = 2) :
    ∃ q : k[X], q.Monic ∧ Irreducible q ∧ P = (Ideal.span {q}).comap red := by
  classical
  have hvP : v ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2
    ((Ideal.span_singleton_le_iff_mem P).mpr htP hv2)
  have hkerP : RingHom.ker red ≤ P := by
    rw [hker]
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact htP
    · exact hvP
  let J : Ideal k[X] := P.map red
  let : J.IsPrime := Ideal.map_isPrime_of_surjective hred hkerP
  have hback : J.comap red = P := by
    change (P.map red).comap red = P
    rw [Ideal.comap_map_of_surjective red hred]
    exact sup_eq_left.mpr hkerP
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hPker : P = RingHom.ker red := by
      rw [← hback, hJ]
      rfl
    have hheight : P.height = 1 :=
      Ideal.height_eq_one_of_span_pair_of_sq_mem P ht0 (hPker.trans hker) hv2
    have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
    rw [hheight, hd] at hdim
    norm_num at hdim
  have hmax : J.IsMaximal := IsPrime.to_maximal_ideal hJ0
  let p : k[X] := Submodule.IsPrincipal.generator J
  have hpSpan : Ideal.span ({p} : Set k[X]) = J := Ideal.span_singleton_generator J
  have hp0 : p ≠ 0 := by
    intro hp
    apply hJ0
    rw [← hpSpan, hp, Ideal.span_singleton_zero]
  have hpMax : (Ideal.span ({p} : Set k[X])).IsMaximal := by
    rw [hpSpan]
    exact hmax
  have hirp : Irreducible p :=
    Ideal.irreducible_of_isMaximal_span_singleton hp0 hpMax
  refine ⟨normalize p, Polynomial.monic_normalize hp0,
    (associated_normalize p).irreducible hirp, ?_⟩
  have hqSpan : Ideal.span ({normalize p} : Set k[X]) = J :=
    (Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated p)).trans hpSpan
  rw [hqSpan]
  exact hback.symm

end Ideal

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The fixed-remainder child theorem uses the actual canonical kernel and the
same original coefficients, not an independently chosen cubic. -/
theorem fixed_cubic_child_sq_dvd [IsNoetherianRing A]
    {t s z : maximalIdeal A} (E : DoubleLinePresentation t s z) (F : CubicRelation t s z)
    (Q : saturatedChart A (maximalIdeal A) (t : A)) (q : (IsLocalRing.ResidueField A)[X])
    (hQ : E.reduction Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap E.reduction)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (g : Fin 3 → maximalIdeal (Localization.AtPrime P))
    (hgQ : (g 0 : Localization.AtPrime P) =
      algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P) Q)
    (hgv : (g 1 : Localization.AtPrime P) =
      algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P)
        (fractionElement (maximalIdeal A) t z))
    (hgt : (g 2 : Localization.AtPrime P) = localizedChartMap (maximalIdeal A) (t : A) P (t : A))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P) g = Ideal.span {L ^ 2}) :
    q ^ 2 ∣ F.coefficients.residueCubic := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let φ : A →+* S := algebraMap A S
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  let C := F.coefficients
  let H := φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3
  let l := φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
    φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2
  obtain ⟨r, hr⟩ := F.divided
  have hφ (a : A) : E.reduction (φ a) = Polynomial.C (residue A a) :=
    E.reduction_coefficient a
  have hU : E.reduction U = X := E.reduction_other
  have hH : E.reduction H = F.coefficients.residueCubic := by
    dsimp only [H, CubicCoefficients.residueCubic]
    simp only [map_add, map_mul, map_pow, hφ, hU, IsLocalRing.residueBinaryCubic]
    ring
  exact Ideal.sq_dvd_of_actual_doubleLine_child E.reduction E.reduction_surjective
    τ V Q H l r q F.coefficients.residueCubic E.reduction_kernel hQ hH hr
    P hP hd hsing g hgQ hgv hgt L hL hCaseII

/-- The irreducible coordinate belongs to the actual exceptional child prime.
Its construction uses the original chart and dimension, without a point oracle. -/
theorem exists_actual_child_prime_parameter [IsDomain A] [IsNoetherianRing A]
    {t s z : maximalIdeal A} (ht0 : (t : A) ≠ 0)
    (E : DoubleLinePresentation t s z) (F : CubicRelation t s z)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (htP : algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A) ∈ P)
    (hd : ringKrullDim (Localization.AtPrime P) = 2) :
    ∃ q : (IsLocalRing.ResidueField A)[X], q.Monic ∧ Irreducible q ∧
      P = (Ideal.span {q}).comap E.reduction ∧
      ∃ Q : saturatedChart A (maximalIdeal A) (t : A), E.reduction Q = q := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsDomain (Localization.Away (t : A)) := Localization.Away.isDomain ht0
  let : IsDomain S := inferInstance
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let φ : A →+* S := algebraMap A S
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  have hτ : τ ≠ 0 := by
    intro h
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (t : A)) (t : A)).ne_zero (congrArg Subtype.val h)
  obtain ⟨r, hr⟩ := F.divided
  let C := F.coefficients
  let H := φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3
  let l := φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
    φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2
  have hdiv : V ^ 2 + τ * H + τ * V * l + τ ^ 2 * r = 0 := hr
  have hV2 : V ^ 2 ∈ Ideal.span ({τ} : Set S) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-(H + V * l + τ * r), ?_⟩
    linear_combination hdiv
  obtain ⟨q, hmonic, hirr, hP⟩ := Ideal.exists_monic_irreducible_of_doubleLine_child
    E.reduction E.reduction_surjective τ V E.reduction_kernel hτ hV2 P htP hd
  exact ⟨q, hmonic, hirr, hP, E.reduction_surjective q⟩

end Localization.Away.SaturatedChart

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The corrected simple-root marker, on actual generators and their full
canonical tangent kernel. It does not impose the rejected special cubic shape. -/
structure MarkedCubic (t : maximalIdeal A) where
  /-- The second tangent-plane generator alongside the marked parameter. -/
  other : maximalIdeal A
  /-- The generator whose cotangent variable squares to the full tangent relation. -/
  square : maximalIdeal A
  generates : maximalIdeal A = Ideal.span ({(t : A), (other : A), (square : A)} : Set A)
  tangent : doubleLineChildCotangentKernel A ![other, square, t] =
    Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2}
  /-- The true cubic relation on these original generators, with its fourth-order remainder. -/
  relation : CubicRelation t other square
  constant_at_infinity : residue A relation.coefficients.a3 = 0
  linear_at_infinity : residue A relation.coefficients.a2 ≠ 0

omit [IsLocalRing A] in
private theorem span_triple_square_shift (t u v μ : A) :
    Ideal.span ({t, u, v + μ * t} : Set A) = Ideal.span ({t, u, v} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x (rfl | rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.mul_mem_left _ μ (Ideal.subset_span (by simp)))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxt | hxu | hxv
    · subst x
      exact Ideal.subset_span (by simp)
    · subst x
      exact Ideal.subset_span (by simp)
    · subst x
      change v ∈ (Ideal.span ({t, u, v + μ * t} : Set A) : Ideal A)
      have htJ : t ∈ Ideal.span ({t, u, v + μ * t} : Set A) := Ideal.subset_span (by simp)
      have h : (v + μ * t) - μ * t ∈ (Ideal.span ({t, u, v + μ * t} : Set A) : Ideal A) :=
        (Ideal.span ({t, u, v + μ * t} : Set A)).sub_mem
        (Ideal.subset_span (by simp : v + μ * t ∈ ({t, u, v + μ * t} : Set A)))
        ((Ideal.span ({t, u, v + μ * t} : Set A)).mul_mem_left μ htJ)
      rw [add_sub_cancel_right] at h
      exact h

private theorem exists_triple_coefficients (t u w : A)
    (hgen : maximalIdeal A = Ideal.span ({t, u, w} : Set A))
    (P : A) (hP : P ∈ maximalIdeal A) :
    ∃ p_t p_u p_w : A, P = p_t * t + p_u * u + p_w * w := by
  rw [hgen] at hP
  obtain ⟨p_t, R, hR, hP⟩ := Ideal.mem_span_insert.mp hP
  obtain ⟨p_u, p_w, hR⟩ := Ideal.mem_span_pair.mp hR
  refine ⟨p_t, p_u, p_w, ?_⟩
  rw [← hR] at hP
  simpa only [add_assoc] using hP

/-- Exact collection preserves the original nonzero `t*u²` coefficient. -/
theorem markedCubic_of_exact_aligned_relation
    (t u w : maximalIdeal A) (a P Q : A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (w : A)} : Set A))
    (ha : residue A a ≠ 0) (hP : P ∈ maximalIdeal A) (hQ : Q ∈ maximalIdeal A)
    (hrel : (w : A) ^ 2 + a * (t : A) * (u : A) ^ 2 +
      (t : A) * (w : A) * P + (t : A) ^ 2 * Q = 0)
    (hker : doubleLineChildCotangentKernel A ![u, w, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2}) :
    ∃ M : MarkedCubic t, M.other = u ∧ M.square = w ∧
      residue A M.relation.coefficients.a2 = residue A a := by
  obtain ⟨p_t, p_u, p_w, hP'⟩ := exists_triple_coefficients (t : A) (u : A) (w : A) hgen P hP
  obtain ⟨q_t, q_u, q_w, hQ'⟩ := exists_triple_coefficients (t : A) (u : A) (w : A) hgen Q hQ
  let C : CubicCoefficients A := ⟨q_t, q_u, a, 0, p_t + q_w, p_u, 0, p_w, 0, 0⟩
  have heq : C.value (t : A) (u : A) (w : A) + 0 = 0 := by
    dsimp only [C, CubicCoefficients.value]
    rw [hP', hQ'] at hrel
    linear_combination hrel
  let F : CubicRelation t u w := ⟨C, 0, Ideal.zero_mem _, heq⟩
  let M : MarkedCubic t :=
    ⟨u, w, hgen, hker, F, map_zero _, ha⟩
  exact ⟨M, rfl, rfl, rfl⟩

/-- The same actual parameter is marked after a square-aligned continuing
Case-II relation. No grandchild or special-shape premise is required. -/
theorem markedCubic_of_divided_relation
    (t u v : maximalIdeal A) (a L H : A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (v : A)} : Set A))
    (ha : residue A a ≠ 0)
    (hrel : (v : A) ^ 2 + a * (t : A) * (u : A) ^ 2 +
      (t : A) * (v : A) * L + (t : A) ^ 2 * H = 0)
    (ell : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hell : ell.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A ![u, v, t] = Ideal.span {ell ^ 2}) :
    ∃ μ : A, ∃ M : MarkedCubic t,
      M.other = u ∧ M.square = v + μ • t ∧
      residue A M.relation.coefficients.a2 = residue A a := by
  obtain ⟨μ, P, Q, hP, hQ, heq, hnew⟩ :=
    exists_exact_aligned_relation t u v a L H 2 (by decide) hrel ell hell hker
  let w : maximalIdeal A := v + μ • t
  have hwgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (w : A)} : Set A) :=
    hgen.trans (span_triple_square_shift (t : A) (u : A) (v : A) μ).symm
  have hnew' : doubleLineChildCotangentKernel A ![u, w, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
    rw [squareShiftTriple_triple] at hnew
    exact hnew
  obtain ⟨M, hMu, hMw, hMa⟩ := markedCubic_of_exact_aligned_relation t u w a P Q
    hwgen ha hP hQ heq hnew'
  exact ⟨μ, M, hMu, hMw, hMa⟩

/-- The actual marker is minimal in a singular two-dimensional local ring. -/
theorem MarkedCubic.parameter_not_mem_sq [IsNoetherianRing A]
    {t : maximalIdeal A} (M : MarkedCubic t)
    (hd : ringKrullDim A = 2) (hsing : ¬ IsRegularLocalRing A) :
    (t : A) ∉ maximalIdeal A ^ 2 :=
  first_not_mem_sq_of_span_triple_of_not_regular A (t : A) M.other M.square M.generates hd hsing

end IsLocalRing

namespace MvPolynomial

variable {k : Type u} [CommRing k]

/-- A change of the actual two tangent-plane coordinates leaves the square coordinate fixed. -/
def planeChangeHom (a b c d : k) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![C a * X 0 + C b * X 2, X 1, C c * X 0 + C d * X 2]

theorem planeChangeHom_comp (a b c d e f g h : k) :
    (planeChangeHom a b c d).comp (planeChangeHom e f g h) =
      planeChangeHom (e * a + f * c) (e * b + f * d) (g * a + h * c) (g * b + h * d) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [planeChangeHom, AlgHom.comp_apply] <;> ring

theorem planeChangeHom_identity : planeChangeHom (1 : k) 0 0 1 = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [planeChangeHom]

end MvPolynomial

namespace MvPolynomial

variable {k : Type u} [Field k]

/-- The actual plane change is invertible when its displayed determinant is nonzero. -/
def planeChange (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k := by
  let Δ := a * d - b * c
  have hi : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 := mul_inv_cancel₀ hdet
  refine AlgEquiv.ofAlgHom (planeChangeHom a b c d)
    (planeChangeHom (d / Δ) (-b / Δ) (-c / Δ) (a / Δ)) ?_ ?_
  · rw [planeChangeHom_comp, ← planeChangeHom_identity]
    congr 1
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      linear_combination hi
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      ring
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      ring
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      linear_combination hi
  · rw [planeChangeHom_comp, ← planeChangeHom_identity]
    congr 1
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      linear_combination hi
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      ring
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      ring
    · dsimp only [Δ]
      simp only [div_eq_mul_inv]
      linear_combination hi

end MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- These are the actual linear combinations in the same original maximal ideal. -/
def planeChangeTriple (g : Fin 3 → maximalIdeal A) (a b c d : A) : Fin 3 → maximalIdeal A :=
  ![a • g 0 + b • g 2, g 1, c • g 0 + d • g 2]

theorem planeChangeTriple_triple (u w t : maximalIdeal A) (a b c d : A) :
    planeChangeTriple ![u, w, t] a b c d = ![a • u + b • t, w, c • u + d • t] := by
  funext i
  fin_cases i <;> rfl

theorem cotangentPolynomialMap_planeChange (g : Fin 3 → maximalIdeal A) (a b c d : A) :
    Ideal.cotangentPolynomialMap (maximalIdeal A) (planeChangeTriple g a b c d) =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).comp
        (MvPolynomial.planeChangeHom (k := A ⧸ maximalIdeal A)
          (Ideal.Quotient.mk (maximalIdeal A) a) (Ideal.Quotient.mk (maximalIdeal A) b)
          (Ideal.Quotient.mk (maximalIdeal A) c) (Ideal.Quotient.mk (maximalIdeal A) d)) := by
  let I := maximalIdeal A
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change Ideal.cotangentPolynomialMap I (planeChangeTriple g a b c d) (MvPolynomial.X 0) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.planeChangeHom (k := A ⧸ I)
          (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b)
          (Ideal.Quotient.mk I c) (Ideal.Quotient.mk I d) (MvPolynomial.X 0))
    rw [MvPolynomial.planeChangeHom, MvPolynomial.aeval_X]
    change Ideal.cotangentPolynomialMap I (planeChangeTriple g a b c d) (MvPolynomial.X 0) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.C (Ideal.Quotient.mk I a) * MvPolynomial.X 0 +
          MvPolynomial.C (Ideal.Quotient.mk I b) * MvPolynomial.X 2)
    simp only [map_add, map_mul, Ideal.cotangentPolynomialMap_C_mk,
      Ideal.cotangentPolynomialMap_X]
    change Ideal.associatedGradedDegreeOneLinear I (a • g 0 + b • g 2) =
      algebraMap A I.associatedGraded a * Ideal.associatedGradedDegreeOneLinear I (g 0) +
        algebraMap A I.associatedGraded b * Ideal.associatedGradedDegreeOneLinear I (g 2)
    rw [map_add, original_degreeOne_smul, original_degreeOne_smul]
  · simp [planeChangeTriple, MvPolynomial.planeChangeHom, AlgHom.comp_apply,
      Ideal.cotangentPolynomialMap_X]
  · change Ideal.cotangentPolynomialMap I (planeChangeTriple g a b c d) (MvPolynomial.X 2) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.planeChangeHom (k := A ⧸ I)
          (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b)
          (Ideal.Quotient.mk I c) (Ideal.Quotient.mk I d) (MvPolynomial.X 2))
    rw [MvPolynomial.planeChangeHom, MvPolynomial.aeval_X]
    change Ideal.cotangentPolynomialMap I (planeChangeTriple g a b c d) (MvPolynomial.X 2) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.C (Ideal.Quotient.mk I c) * MvPolynomial.X 0 +
          MvPolynomial.C (Ideal.Quotient.mk I d) * MvPolynomial.X 2)
    simp only [map_add, map_mul, Ideal.cotangentPolynomialMap_C_mk,
      Ideal.cotangentPolynomialMap_X]
    change Ideal.associatedGradedDegreeOneLinear I (c • g 0 + d • g 2) =
      algebraMap A I.associatedGraded c * Ideal.associatedGradedDegreeOneLinear I (g 0) +
        algebraMap A I.associatedGraded d * Ideal.associatedGradedDegreeOneLinear I (g 2)
    rw [map_add, original_degreeOne_smul, original_degreeOne_smul]

/-- An invertible change in the actual plane preserves the full square-coordinate kernel. -/
theorem cotangentKernel_planeChange (g : Fin 3 → maximalIdeal A) (a b c d : A)
    (hdet : IsUnit (a * d - b * c))
    (hker : doubleLineChildCotangentKernel A g =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2}) :
    doubleLineChildCotangentKernel A (planeChangeTriple g a b c d) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
  have hdet' : residue A a * residue A d - residue A b * residue A c ≠ 0 := by
    simpa only [map_sub, map_mul] using (hdet.map (residue A)).ne_zero
  let σ := MvPolynomial.planeChange (residue A a) (residue A b) (residue A c) (residue A d) hdet'
  let J : Ideal (MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) :=
    Ideal.span {MvPolynomial.X 1 ^ 2}
  have hmap : J.map σ.toRingHom = J := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change σ (MvPolynomial.X 1 ^ 2) = MvPolynomial.X 1 ^ 2
    rw [map_pow]
    change (MvPolynomial.planeChangeHom (residue A a) (residue A b)
      (residue A c) (residue A d) (MvPolynomial.X 1)) ^ 2 = _
    simp [MvPolynomial.planeChangeHom]
  have hcomp : doubleLineChildCotangentKernel A (planeChangeTriple g a b c d) =
      (doubleLineChildCotangentKernel A g).comap σ.toRingHom := by
    ext p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) (planeChangeTriple g a b c d) p = 0 ↔
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p) = 0
    rw [cotangentPolynomialMap_planeChange]
    rfl
  rw [hcomp, hker]
  change J.comap σ.toRingHom = J
  exact (congrArg (Ideal.comap σ.toRingHom) hmap.symm).trans
    (Ideal.comap_map_of_bijective σ.toRingHom σ.bijective)

omit [IsLocalRing A] in
private theorem mem_of_unit_mul_mem (J : Ideal A) (d x : A)
    (hd : IsUnit d) (hx : d * x ∈ J) : x ∈ J := by
  obtain ⟨e, rfl⟩ := hd
  have h := J.mul_mem_left ((e⁻¹ : Aˣ) : A) hx
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using h

/-- The actual three-generator ideal is unchanged by an invertible plane substitution. -/
theorem maximalIdeal_planeChange (t u w : maximalIdeal A) (a b c d : A)
    (hdet : IsUnit (a * d - b * c))
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (w : A)} : Set A)) :
    maximalIdeal A = Ideal.span
      ({c * (u : A) + d * (t : A), a * (u : A) + b * (t : A), (w : A)} : Set A) := by
  let J : Ideal A := Ideal.span
    ({c * (u : A) + d * (t : A), a * (u : A) + b * (t : A), (w : A)} : Set A)
  have hnewt : c * (u : A) + d * (t : A) ∈ J := Ideal.subset_span (by simp)
  have hnewu : a * (u : A) + b * (t : A) ∈ J := Ideal.subset_span (by simp)
  have ht : (t : A) ∈ J := by
    apply mem_of_unit_mul_mem J (a * d - b * c) (t : A) hdet
    convert J.sub_mem (J.mul_mem_left a hnewt) (J.mul_mem_left c hnewu) using 1
    ring
  have hu : (u : A) ∈ J := by
    apply mem_of_unit_mul_mem J (a * d - b * c) (u : A) hdet
    convert J.sub_mem (J.mul_mem_left d hnewu) (J.mul_mem_left b hnewt) using 1
    ring
  apply le_antisymm
  · refine hgen.le.trans ?_
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl | rfl)
    · exact ht
    · exact hu
    · exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    rintro x (rfl | rfl | rfl)
    · exact (maximalIdeal A).add_mem ((maximalIdeal A).mul_mem_left c u.property)
        ((maximalIdeal A).mul_mem_left d t.property)
    · exact (maximalIdeal A).add_mem ((maximalIdeal A).mul_mem_left a u.property)
        ((maximalIdeal A).mul_mem_left b t.property)
    · exact w.property

end IsLocalRing

namespace Localization.Away.SaturatedChart.CubicCoefficients

variable {A : Type u} [CommRing A]

/-- Substitute the original two plane variables by displayed linear combinations.
The square coordinate and original coefficient ring are unchanged. -/
def substitute (C : CubicCoefficients A) (p q r s : A) : CubicCoefficients A where
  a0 := C.a0 * p ^ 3 + C.a1 * p ^ 2 * r + C.a2 * p * r ^ 2 + C.a3 * r ^ 3
  a1 := 3 * C.a0 * p ^ 2 * q + C.a1 * (p ^ 2 * s + 2 * p * q * r) +
    C.a2 * (2 * p * r * s + q * r ^ 2) + 3 * C.a3 * r ^ 2 * s
  a2 := 3 * C.a0 * p * q ^ 2 + C.a1 * (2 * p * q * s + q ^ 2 * r) +
    C.a2 * (p * s ^ 2 + 2 * q * r * s) + 3 * C.a3 * r * s ^ 2
  a3 := C.a0 * q ^ 3 + C.a1 * q ^ 2 * s + C.a2 * q * s ^ 2 + C.a3 * s ^ 3
  b0 := C.b0 * p ^ 2 + C.b1 * p * r + C.b2 * r ^ 2
  b1 := 2 * C.b0 * p * q + C.b1 * (p * s + q * r) + 2 * C.b2 * r * s
  b2 := C.b0 * q ^ 2 + C.b1 * q * s + C.b2 * s ^ 2
  c0 := C.c0 * p + C.c1 * r
  c1 := C.c0 * q + C.c1 * s
  d0 := C.d0

theorem substitute_value (C : CubicCoefficients A) (p q r s t u z : A) :
    (C.substitute p q r s).value t u z = C.value (p * t + q * u) (r * t + s * u) z := by
  dsimp only [substitute, value]
  ring

theorem substitute_recenter_a2 (C : CubicCoefficients A) (α : A) :
    (C.substitute 1 0 α 1).a2 = C.a2 + 3 * C.a3 * α := by
  dsimp only [substitute]
  ring

theorem substitute_recenter_a3 (C : CubicCoefficients A) (α : A) :
    (C.substitute 1 0 α 1).a3 = C.a3 := by
  simp [substitute]

end Localization.Away.SaturatedChart.CubicCoefficients

namespace Localization.Away.SaturatedChart.CubicRelation

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Transport the same true relation through actual identities of its generators. -/
def substitute {t u z : maximalIdeal A} (F : CubicRelation t u z)
    (t' u' : maximalIdeal A) (p q r s : A)
    (ht : (t : A) = p * (t' : A) + q * (u' : A))
    (hu : (u : A) = r * (t' : A) + s * (u' : A)) : CubicRelation t' u' z where
  coefficients := F.coefficients.substitute p q r s
  remainder := F.remainder
  remainder_mem := F.remainder_mem
  equation := by rw [CubicCoefficients.substitute_value, ← ht, ← hu]; exact F.equation

end Localization.Away.SaturatedChart.CubicRelation

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A coefficient-one square relation identifies the full genuine Case-II
kernel in these actual coordinates; no second square shift is used. -/
theorem cotangentKernel_eq_square_of_quadratic_relation
    (t u w : maximalIdeal A) (c d e : A)
    (hc : c ∈ maximalIdeal A) (hd : d ∈ maximalIdeal A) (he : e ∈ maximalIdeal A)
    (hrel : (w : A) ^ 2 + (t : A) * (c * (u : A) + d * (w : A) + e * (t : A)) = 0)
    (ell : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hell : ell.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A ![u, w, t] = Ideal.span {ell ^ 2}) :
    doubleLineChildCotangentKernel A ![u, w, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
  have hf := doubleLineChildQuadratic_mem_cotangent_kernel t w u c d e hrel
  rw [(residue_eq_zero_iff c).mpr hc, (residue_eq_zero_iff d).mpr hd,
    (residue_eq_zero_iff e).mpr he, hker] at hf
  have hf' : (MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2 ∈
      Ideal.span {ell ^ 2} := by
    simpa only [MvPolynomial.doubleLineChildQuadratic, map_zero, zero_mul, zero_add,
      add_zero, mul_zero] using hf
  have hn : (MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (MvPolynomial.X_ne_zero 1)
  obtain ⟨δ, hδ⟩ := MvPolynomial.eq_scalar_square_of_mem_span_square
    (MvPolynomial.isHomogeneous_X_pow 1 2) hn hell hf'
  have hδ0 : δ ≠ 0 := by
    intro hz
    apply hn
    simpa only [hz, map_zero, zero_mul] using hδ
  rw [hker, hδ]
  exact (Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr hδ0).map
      (MvPolynomial.C : IsLocalRing.ResidueField A →+*
        MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)))
    (ell ^ 2)).symm

/-- The exact first-child equation at a triple root, including its higher terms. -/
structure TripleEntryData (t u w : maximalIdeal A) where
  /-- The unit coefficient of the original `t*u³` term in the entry equation. -/
  coefficient : A
  coefficient_unit : IsUnit coefficient
  /-- The maximal-ideal coefficient of the entry equation's `t*w` term. -/
  P : A
  /-- The maximal-ideal coefficient of the entry equation's `t²` term. -/
  Q : A
  P_mem : P ∈ maximalIdeal A
  Q_mem : Q ∈ maximalIdeal A
  generates : maximalIdeal A = Ideal.span ({(t : A), (u : A), (w : A)} : Set A)
  tangent : doubleLineChildCotangentKernel A ![u, w, t] =
    Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2}
  equation : (w : A) ^ 2 + coefficient * (t : A) * (u : A) ^ 3 +
    (t : A) * (w : A) * P + (t : A) ^ 2 * Q = 0

/-- The first triple-entry identity is produced by the true divided relation
and genuine child tangent kernel. -/
theorem exists_tripleEntryData_of_divided_relation
    (t u v : maximalIdeal A) (a L H : A) (ha : IsUnit a)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (v : A)} : Set A))
    (hrel : (v : A) ^ 2 + a * (t : A) * (u : A) ^ 3 +
      (t : A) * (v : A) * L + (t : A) ^ 2 * H = 0)
    (ell : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hell : ell.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A ![u, v, t] = Ideal.span {ell ^ 2}) :
    ∃ μ : A, ∃ D : TripleEntryData t u (v + μ • t), D.coefficient = a := by
  obtain ⟨μ, P, Q, hP, hQ, heq, hnew⟩ :=
    exists_exact_aligned_relation t u v a L H 3 (by decide) hrel ell hell hker
  have hgen' : maximalIdeal A =
      Ideal.span ({(t : A), (u : A), ((v + μ • t : maximalIdeal A) : A)} : Set A) :=
    hgen.trans (span_triple_square_shift (t : A) (u : A) (v : A) μ).symm
  have hnew' : doubleLineChildCotangentKernel A ![u, v + μ • t, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
    rw [squareShiftTriple_triple] at hnew
    exact hnew
  exact ⟨μ, ⟨a, ha, P, Q, hP, hQ, hgen', hnew', heq⟩, rfl⟩

namespace TripleEntryData

variable {t u w : maximalIdeal A} (D : TripleEntryData t u w)

/-- The actual first-child cubic is `T²*(alpha*T+beta*U)`.
Its fourth-order term and the exact decomposition of Q are retained. -/
theorem exists_fixed_cubic : ∃ (alpha beta gamma : A) (F : CubicRelation t u w),
    D.Q = alpha * (t : A) + beta * (u : A) + gamma * (w : A) ∧
    F.coefficients.a0 = alpha ∧ F.coefficients.a1 = beta ∧
    F.coefficients.a2 = 0 ∧ F.coefficients.a3 = 0 ∧
    F.remainder = D.coefficient * (t : A) * (u : A) ^ 3 := by
  obtain ⟨p_t, p_u, p_w, hP⟩ := exists_triple_coefficients (t : A) (u : A) (w : A)
    D.generates D.P D.P_mem
  obtain ⟨alpha, beta, gamma, hQ⟩ := exists_triple_coefficients (t : A) (u : A) (w : A)
    D.generates D.Q D.Q_mem
  let C : CubicCoefficients A := ⟨alpha, beta, 0, 0, p_t + gamma, p_u, 0, p_w, 0, 0⟩
  have hR : D.coefficient * (t : A) * (u : A) ^ 3 ∈ maximalIdeal A ^ 4 := by
    have h := (maximalIdeal A ^ 4).mul_mem_left D.coefficient
      (show (t : A) * (u : A) ^ 3 ∈ maximalIdeal A ^ 4 from by
        simpa only [pow_succ'] using Ideal.mul_mem_mul t.property (Ideal.pow_mem_pow u.property 3))
    simpa only [mul_assoc] using h
  have heq : C.value (t : A) (u : A) (w : A) +
      D.coefficient * (t : A) * (u : A) ^ 3 = 0 := by
    have h := D.equation
    rw [hP, hQ] at h
    dsimp only [C, CubicCoefficients.value]
    linear_combination h
  exact ⟨alpha, beta, gamma, ⟨C, _, hR, heq⟩, hQ, rfl, rfl, rfl, rfl, rfl⟩

/-- A nonzero linear U coefficient gives the actual simple-factor marker
at the first child, with an invertible change of its own plane coordinates. -/
theorem marked_of_beta_nonzero (D : TripleEntryData t u w)
    (alpha beta : A) (F : CubicRelation t u w)
    (hF0 : F.coefficients.a0 = alpha) (hF1 : F.coefficients.a1 = beta)
    (hF2 : F.coefficients.a2 = 0) (hF3 : F.coefficients.a3 = 0)
    (hbeta : residue A beta ≠ 0) :
    ∃ M : MarkedCubic (beta • u + alpha • t), M.other = t ∧ M.square = w := by
  have hunit : IsUnit beta := (residue_ne_zero_iff_isUnit beta).mp hbeta
  obtain ⟨e, he⟩ := hunit
  have hunit : IsUnit beta := ⟨e, he⟩
  let η : A := ((e⁻¹ : Aˣ) : A)
  have hη : η * beta = 1 := by rw [← he]; exact Units.inv_mul e
  let ell : maximalIdeal A := beta • u + alpha • t
  have ht : (t : A) = 0 * (ell : A) + 1 * (t : A) := by ring
  have hu : (u : A) = η * (ell : A) + (-η * alpha) * (t : A) := by
    change (u : A) = η * (beta * (u : A) + alpha * (t : A)) + (-η * alpha) * (t : A)
    linear_combination -(u : A) * hη
  let F' := F.substitute ell t 0 1 η (-η * alpha) ht hu
  have hgen : maximalIdeal A = Ideal.span ({(ell : A), (t : A), (w : A)} : Set A) := by
    have hell : (ell : A) = beta * (u : A) + alpha * (t : A) := rfl
    rw [hell]
    simpa only [zero_mul, one_mul, zero_add] using
      maximalIdeal_planeChange t u w 0 1 beta alpha (by simpa using hunit.neg) D.generates
  have hkernel : doubleLineChildCotangentKernel A ![t, w, ell] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
    have h := cotangentKernel_planeChange ![u, w, t] 0 1 beta alpha
      (by simpa using hunit.neg) D.tangent
    simpa [planeChangeTriple, ell] using h
  have h2 : F'.coefficients.a2 = 1 := by
    dsimp only [F', CubicRelation.substitute, CubicCoefficients.substitute]
    rw [hF0, hF1, hF2, hF3]
    linear_combination hη
  have h3 : F'.coefficients.a3 = 0 := by
    dsimp only [F', CubicRelation.substitute, CubicCoefficients.substitute]
    rw [hF0, hF1, hF2, hF3]
    linear_combination -alpha * hη
  let M : MarkedCubic ell := ⟨t, w, hgen, hkernel, F',
    by rw [h3, map_zero], by rw [h2, map_one]; exact one_ne_zero⟩
  exact ⟨M, rfl, rfl⟩

/-- A zero linear U coefficient gives an actual square-ideal remainder. -/
theorem split_Q_of_beta_zero (alpha beta gamma : A)
    (hQ : D.Q = alpha * (t : A) + beta * (u : A) + gamma * (w : A))
    (hbeta : residue A beta = 0) :
    ∃ Q2 : A, Q2 ∈ maximalIdeal A ^ 2 ∧
      D.Q = alpha * (t : A) + gamma * (w : A) + Q2 := by
  refine ⟨beta * (u : A), ?_, ?_⟩
  · simpa only [pow_two] using
      Ideal.mul_mem_mul (Ideal.Quotient.eq_zero_iff_mem.mp hbeta) u.property
  · linear_combination hQ

end TripleEntryData

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The exact second chart in the triple-root branch. All original fourth-order
terms keep their explicit factors after the actual denominator is cancelled. -/
theorem TripleEntryData_second_chart_equation {t u w : maximalIdeal A}
    (D : IsLocalRing.TripleEntryData t u w) (alpha gamma Q2 : A)
    (hQ2 : Q2 ∈ maximalIdeal A ^ 2)
    (hQ : D.Q = alpha * (t : A) + gamma * (w : A) + Q2) :
    ∃ P1 Q2' : saturatedChart A (maximalIdeal A) (u : A),
      let φ := algebraMap A (saturatedChart A (maximalIdeal A) (u : A))
      let τ := φ (u : A)
      let R := fractionElement (maximalIdeal A) u t
      let V := fractionElement (maximalIdeal A) u w
      V ^ 2 + φ D.coefficient * τ ^ 2 * R + τ * R * V * P1 +
        τ * R ^ 2 * (φ alpha * R + φ gamma * V) + τ ^ 2 * R ^ 2 * Q2' = 0 := by
  let S : Type u := saturatedChart A (maximalIdeal A) (u : A)
  let φ : A →+* S := algebraMap A S
  let τ := φ (u : A)
  let R := fractionElement (maximalIdeal A) u t
  let V := fractionElement (maximalIdeal A) u w
  have hPmem : φ D.P ∈ Ideal.span {τ} := by
    have h := Ideal.mem_map_of_mem φ D.P_mem
    rw [map_center_eq_span (maximalIdeal A) (u : A) u.property] at h
    exact h
  have hQmem : φ Q2 ∈ Ideal.span {τ ^ 2} := by
    have h := Ideal.mem_map_of_mem φ hQ2
    rw [map_center_pow_eq_span (maximalIdeal A) (u : A) 2 u.property] at h
    exact h
  obtain ⟨P1, hP1⟩ := Ideal.mem_span_singleton.mp hPmem
  obtain ⟨Q2', hQ2'⟩ := Ideal.mem_span_singleton.mp hQmem
  refine ⟨P1, Q2', ?_⟩
  have ht : τ * R = φ (t : A) := fractionElement_mul (maximalIdeal A) u t
  have hw : τ * V = φ (w : A) := fractionElement_mul (maximalIdeal A) u w
  have h := D.equation
  rw [hQ] at h
  have hmap := congrArg φ h
  simp only [map_add, map_mul, map_pow, map_zero] at hmap
  rw [← ht, ← hw, hP1, hQ2'] at hmap
  apply exceptional_pow_mul_injective (maximalIdeal A) (u : A) 2
  change τ ^ 2 * _ = τ ^ 2 * 0
  rw [mul_zero]
  convert hmap using 1
  ring

end Localization.Away.SaturatedChart

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The second triple-entry equation marks the actual new coordinate `r=t/u`.
Its square coordinate is already aligned, including in characteristic two. -/
theorem markedCubic_of_second_triple_equation
    (r u v : maximalIdeal A) (b P1 Q2 alpha gamma : A) (hb : IsUnit b)
    (hgen : maximalIdeal A = Ideal.span ({(r : A), (u : A), (v : A)} : Set A))
    (hrel : (v : A) ^ 2 + b * (u : A) ^ 2 * (r : A) +
      (u : A) * (r : A) * (v : A) * P1 +
      (u : A) * (r : A) ^ 2 * (alpha * (r : A) + gamma * (v : A)) +
      (u : A) ^ 2 * (r : A) ^ 2 * Q2 = 0)
    (ell : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hell : ell.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A ![u, v, r] = Ideal.span {ell ^ 2}) :
    ∃ M : MarkedCubic r, M.other = u ∧ M.square = v ∧
      residue A M.relation.coefficients.a2 = residue A b := by
  let P := (u : A) * P1
  let Q := (u : A) * (alpha * (r : A) + gamma * (v : A) + (u : A) * Q2)
  have hP : P ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right P1 u.property
  have hQ : Q ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right _ u.property
  have hc : b * (u : A) ∈ maximalIdeal A := (maximalIdeal A).mul_mem_left b u.property
  have hquad : (v : A) ^ 2 + (r : A) *
      (b * (u : A) * (u : A) + P * (v : A) + Q * (r : A)) = 0 := by
    dsimp only [P, Q]
    linear_combination hrel
  have hnew := cotangentKernel_eq_square_of_quadratic_relation r u v
    (b * (u : A)) P Q hc hP hQ hquad ell hell hker
  have hmarked : (v : A) ^ 2 + b * (r : A) * (u : A) ^ 2 +
      (r : A) * (v : A) * P + (r : A) ^ 2 * Q = 0 := by
    linear_combination hquad
  exact markedCubic_of_exact_aligned_relation r u v b P Q hgen
    (hb.map (residue A)).ne_zero hP hQ hmarked hnew

end IsLocalRing

namespace Ideal

variable {S : Type u} [CommRing S]

/-- The displayed actual prime supplies its actual three localized ideal elements. -/
def localTriple (P : Ideal S) [P.IsPrime] (t u v : S)
    (hP : P = Ideal.span ({t, u, v} : Set S)) :
    Fin 3 → IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
  ![⟨algebraMap S (Localization.AtPrime P) u,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P u).mpr
        (by rw [hP]; exact Ideal.subset_span (by simp))⟩,
    ⟨algebraMap S (Localization.AtPrime P) v,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P v).mpr
        (by rw [hP]; exact Ideal.subset_span (by simp))⟩,
    ⟨algebraMap S (Localization.AtPrime P) t,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P t).mpr
        (by rw [hP]; exact Ideal.subset_span (by simp))⟩]

theorem localTriple_generates (P : Ideal S) [P.IsPrime] (t u v : S)
    (hP : P = Ideal.span ({t, u, v} : Set S)) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span
      ({(localTriple P t u v hP 2 : Localization.AtPrime P),
        (localTriple P t u v hP 0 : Localization.AtPrime P),
        (localTriple P t u v hP 1 : Localization.AtPrime P)} : Set (Localization.AtPrime P)) := by
  have h := congrArg (Ideal.map (algebraMap S (Localization.AtPrime P))) hP
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)).symm.trans h

end Ideal

namespace Localization.Away.SaturatedChart.CubicCoefficients

variable {A : Type u} [CommRing A]

/-- Replace only the pure coefficients, retaining the coefficients that contain
the square variable. -/
def replacePure (C : CubicCoefficients A) (a0 a1 a2 a3 : A) : CubicCoefficients A :=
  { C with a0 := a0, a1 := a1, a2 := a2, a3 := a3 }

theorem residueCubic_recenter [IsLocalRing A] (C : CubicCoefficients A) (α : A) :
    (C.substitute 1 0 α 1).residueCubic =
      C.residueCubic.comp (X + Polynomial.C (residue A α)) := by
  dsimp only [substitute, residueCubic, IsLocalRing.residueBinaryCubic]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero,
    Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.C_comp, Polynomial.X_comp]
  ring

theorem residueCubic_coeff_zero [IsLocalRing A] (C : CubicCoefficients A) :
    C.residueCubic.coeff 0 = residue A C.a0 := by
  simp [residueCubic, IsLocalRing.residueBinaryCubic]

theorem residueCubic_coeff_one [IsLocalRing A] (C : CubicCoefficients A) :
    C.residueCubic.coeff 1 = residue A C.a1 := by
  simp [residueCubic, IsLocalRing.residueBinaryCubic]

end Localization.Away.SaturatedChart.CubicCoefficients

namespace Localization.Away.SaturatedChart.CubicRelation

variable {A : Type u} [CommRing A] [IsLocalRing A]

private theorem four_factor_mem (a b c d : A)
    (ha : a ∈ maximalIdeal A) (hb : b ∈ maximalIdeal A)
    (hc : c ∈ maximalIdeal A) (hd : d ∈ maximalIdeal A) :
    a * b * c * d ∈ maximalIdeal A ^ 4 := by
  have hab : a * b ∈ maximalIdeal A ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul ha hb
  have hcd : c * d ∈ maximalIdeal A ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hc hd
  have h := Ideal.mul_mem_mul hab hcd
  rw [← pow_add] at h
  simpa only [mul_assoc] using h

/-- Differences of coefficient lifts are absorbed into the actual fourth power,
preserving an exact equation in the original ring. -/
def replacePure {t u z : maximalIdeal A} (F : CubicRelation t u z)
    (a0 a1 a2 a3 : A)
    (h0 : residue A F.coefficients.a0 = residue A a0)
    (h1 : residue A F.coefficients.a1 = residue A a1)
    (h2 : residue A F.coefficients.a2 = residue A a2)
    (h3 : residue A F.coefficients.a3 = residue A a3) : CubicRelation t u z where
  coefficients := F.coefficients.replacePure a0 a1 a2 a3
  remainder := F.remainder + (F.coefficients.a0 - a0) * (t : A) ^ 3 +
    (F.coefficients.a1 - a1) * (t : A) ^ 2 * (u : A) +
    (F.coefficients.a2 - a2) * (t : A) * (u : A) ^ 2 +
    (F.coefficients.a3 - a3) * (u : A) ^ 3
  remainder_mem := by
    have hc (x y : A) (h : residue A x = residue A y) : x - y ∈ maximalIdeal A := by
      apply (residue_eq_zero_iff (x - y)).mp
      rw [map_sub, h, sub_self]
    have ht0 := four_factor_mem (F.coefficients.a0 - a0) (t : A) (t : A) (t : A)
      (hc _ _ h0) t.property t.property t.property
    have ht1 := four_factor_mem (F.coefficients.a1 - a1) (t : A) (t : A) (u : A)
      (hc _ _ h1) t.property t.property u.property
    have ht2 := four_factor_mem (F.coefficients.a2 - a2) (t : A) (u : A) (u : A)
      (hc _ _ h2) t.property u.property u.property
    have ht3 := four_factor_mem (F.coefficients.a3 - a3) (u : A) (u : A) (u : A)
      (hc _ _ h3) u.property u.property u.property
    apply (maximalIdeal A ^ 4).add_mem
    · apply (maximalIdeal A ^ 4).add_mem
      · apply (maximalIdeal A ^ 4).add_mem
        · exact (maximalIdeal A ^ 4).add_mem F.remainder_mem
            (by convert ht0 using 1; ring)
        · simpa only [pow_two, mul_assoc] using ht1
      · simpa only [pow_two, mul_assoc] using ht2
    · convert ht3 using 1; ring
  equation := by
    dsimp only [CubicCoefficients.replacePure, CubicCoefficients.value]
    have h := F.equation
    dsimp only [CubicCoefficients.value] at h
    linear_combination h

/-- Recenter an actual rational root without changing the original denominator. -/
def recenter {t u z : maximalIdeal A} (F : CubicRelation t u z) (α : A) :
    CubicRelation t (u - α • t) z :=
  F.substitute t (u - α • t) 1 0 α 1 (by simp)
    (by
      simp only [Submodule.coe_sub, Submodule.coe_smul, smul_eq_mul, one_mul]
      ring)

/-- Repeatedness kills the actual two low pure coefficients after recentering. -/
theorem recenter_zero_coefficients {t u z : maximalIdeal A} (F : CubicRelation t u z) (α : A)
    (hsq : (X - Polynomial.C (residue A α)) ^ 2 ∣ F.coefficients.residueCubic) :
    residue A (F.recenter α).coefficients.a0 = 0 ∧
      residue A (F.recenter α).coefficients.a1 = 0 := by
  have hshift : (F.recenter α).coefficients.residueCubic =
      F.coefficients.residueCubic.comp (X + Polynomial.C (residue A α)) :=
    CubicCoefficients.residueCubic_recenter F.coefficients α
  obtain ⟨p, hp⟩ := hsq
  have hdiv : (X : (IsLocalRing.ResidueField A)[X]) ^ 2 ∣
      (F.recenter α).coefficients.residueCubic := by
    rw [hshift, hp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right]
    exact dvd_mul_right _ _
  have h0 := Polynomial.X_pow_dvd_iff.mp hdiv 0 (by decide)
  have h1 := Polynomial.X_pow_dvd_iff.mp hdiv 1 (by decide)
  exact ⟨(CubicCoefficients.residueCubic_coeff_zero _).symm.trans h0,
    (CubicCoefficients.residueCubic_coeff_one _).symm.trans h1⟩

end Localization.Away.SaturatedChart.CubicRelation

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A double factor and its distinct simple factor give the original-ring marker.
The coordinate inverse uses the proved unit coefficient, never the integer two. -/
theorem markedCubic_of_simple_factor
    (t u z : maximalIdeal A) (F : CubicRelation t u z)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (u : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![u, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2})
    (h0 : F.coefficients.a0 = 0) (h1 : F.coefficients.a1 = 0)
    (h2 : residue A F.coefficients.a2 ≠ 0) :
    ∃ M : MarkedCubic (F.coefficients.a3 • u + F.coefficients.a2 • t),
      M.other = u ∧ M.square = z := by
  let a := F.coefficients.a2
  let b := F.coefficients.a3
  have ha : IsUnit a := (residue_ne_zero_iff_isUnit a).mp h2
  obtain ⟨e, he⟩ := ha
  have ha : IsUnit a := ⟨e, he⟩
  let η : A := ((e⁻¹ : Aˣ) : A)
  have hη : η * a = 1 := by rw [← he]; exact Units.inv_mul e
  let ell : maximalIdeal A := b • u + a • t
  have ht : (t : A) = η * (ell : A) + (-η * b) * (u : A) := by
    change (t : A) = η * (b * (u : A) + a * (t : A)) + (-η * b) * (u : A)
    linear_combination -(t : A) * hη
  have hu : (u : A) = 0 * (ell : A) + 1 * (u : A) := by ring
  let F' := F.substitute ell u η (-η * b) 0 1 ht hu
  have hgen' : maximalIdeal A = Ideal.span ({(ell : A), (u : A), (z : A)} : Set A) := by
    have hell : (ell : A) = b * (u : A) + a * (t : A) := rfl
    rw [hell]
    simpa only [one_mul, zero_mul, add_zero] using
      maximalIdeal_planeChange t u z 1 0 b a (by simpa using ha) hgen
  have hkernel : doubleLineChildCotangentKernel A ![u, z, ell] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
    have h := cotangentKernel_planeChange ![u, z, t] 1 0 b a (by simpa using ha) hker
    simpa [planeChangeTriple, ell] using h
  have hF2 : F'.coefficients.a2 = 1 := by
    dsimp only [F', CubicRelation.substitute, CubicCoefficients.substitute]
    rw [h0, h1]
    change 3 * 0 * η * (-η * b) ^ 2 + 0 * _ + a * (η * 1 ^ 2 + _) + 3 * b * 0 * 1 ^ 2 = 1
    linear_combination hη
  have hF3 : F'.coefficients.a3 = 0 := by
    dsimp only [F', CubicRelation.substitute, CubicCoefficients.substitute]
    rw [h0, h1]
    change 0 * (-η * b) ^ 3 + 0 * (-η * b) ^ 2 * 1 + a * (-η * b) * 1 ^ 2 + b * 1 ^ 3 = 0
    linear_combination -b * hη
  let M : MarkedCubic ell := ⟨u, z, hgen', hkernel, F',
    by rw [hF3, map_zero], by rw [hF2, map_one]; exact one_ne_zero⟩
  exact ⟨M, rfl, rfl⟩

/-- Recentring the other plane coordinate preserves the corrected marker and
the same actual parameter. -/
def MarkedCubic.recenter {t : maximalIdeal A} (M : MarkedCubic t) (α : A) : MarkedCubic t where
  other := M.other - α • t
  square := M.square
  generates := by
    have hother : ((M.other - α • t : maximalIdeal A) : A) =
        (M.other : A) - α * (t : A) := by
      simp only [Submodule.coe_sub, Submodule.coe_smul, smul_eq_mul]
    rw [hother]
    have h := maximalIdeal_planeChange t M.other M.square 1 (-α) 0 1 (by simp) M.generates
    simpa only [one_mul, zero_mul, zero_add, add_zero, sub_eq_add_neg, neg_mul] using h
  tangent := by
    have h := cotangentKernel_planeChange ![M.other, M.square, t] 1 (-α) 0 1 (by simp) M.tangent
    simpa only [planeChangeTriple_triple, one_smul, zero_smul, zero_add,
      add_zero, neg_smul, sub_eq_add_neg] using h
  relation := M.relation.recenter α
  constant_at_infinity := by
    change residue A (M.relation.coefficients.substitute 1 0 α 1).a3 = 0
    rw [CubicCoefficients.substitute_recenter_a3]
    exact M.constant_at_infinity
  linear_at_infinity := by
    change residue A (M.relation.coefficients.substitute 1 0 α 1).a2 ≠ 0
    rw [CubicCoefficients.substitute_recenter_a2, map_add, map_mul, map_mul, map_ofNat,
      M.constant_at_infinity, mul_zero, zero_mul, add_zero]
    exact M.linear_at_infinity

end IsLocalRing
