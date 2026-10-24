/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.MarkedChart
public import Aglib.RingTheory.ReesAlgebra.ExceptionalChart
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# Original double-line charts and their nonzero residue cubics

The original degree-two tangent relation gives a true cubic equation in the
original local ring. Its divided relation is proved in the actual saturated
chart. The actual associated-graded quotient comparison identifies the
exceptional double line, retaining the original denominator and numerators.

Its generic prime and annihilator are then derived from that quotient.
Normality of the actual chart and the principal ideal theorem give the actual
generic DVR; the original cubic coefficient is a unit there. The canonical
local coefficient map proves that the original reduced cubic is nonzero.
The final polynomial lemmas give rationality and uniqueness of a repeated
prime divisor of a nonzero cubic over the original field.

The normalized tangent-square presentation and normality of the actual
ordinary chart remain inputs. The Case-II child tangent-coordinate comparison
needed for square divisibility, projective chart coverage, and persistent
simple-root marking are separate obligations. No ambient local-ring
presentation, coefficient-field section, perfectness or termination premise
is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial IsLocalRing Pointwise

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The square of the original degree-one z-class vanishes precisely when z² has order at least3. -/
theorem associatedGraded_degreeOne_sq_eq_zero_iff (I : Ideal A) (z : I) :
    (Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I z)) ^ 2 = 0 ↔
      (z : A) ^ 2 ∈ I ^ 3 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, I.mem_associatedGradedIdeal_iff]
  constructor
  · intro h
    simpa [reesAlgebra.degreeOne_val, Polynomial.monomial_pow] using h 2
  · intro hz n
    by_cases hn : n = 2
    · subst n
      simpa [reesAlgebra.degreeOne_val, Polynomial.monomial_pow] using hz
    · change (((reesAlgebra.degreeOne I z : A[X]) ^ 2).coeff n) ∈ I ^ (n + 1)
      rw [reesAlgebra.degreeOne_val, Polynomial.monomial_pow, one_mul,
        Polynomial.coeff_monomial, ite_eq_right (Ne.symm hn)]
      exact (I ^ (n + 1)).zero_mem

/-- The actual third power of a three-generated ideal is spanned by its ten cubic monomials. -/
theorem span_triple_cube_le_cubic_monomials (t s z : A) :
    Ideal.span ({t, s, z} : Set A) ^ 3 ≤
      Ideal.span ({t ^ 3, t ^ 2 * s, t * s ^ 2, s ^ 3,
        t ^ 2 * z, t * s * z, s ^ 2 * z, t * z ^ 2, s * z ^ 2, z ^ 3} : Set A) := by
  let J : Ideal A := Ideal.span ({t ^ 3, t ^ 2 * s, t * s ^ 2, s ^ 3,
    t ^ 2 * z, t * s * z, s ^ 2 * z, t * z ^ 2, s * z ^ 2, z ^ 3} : Set A)
  have h0 : t ^ 3 ∈ J := Ideal.subset_span (Or.inl rfl)
  have h1 : t ^ 2 * s ∈ J := Ideal.subset_span (Or.inr (Or.inl rfl))
  have h2 : t * s ^ 2 ∈ J := Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : s ^ 3 ∈ J := Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : t ^ 2 * z ∈ J := Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : t * s * z ∈ J :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : s ^ 2 * z ∈ J :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h7 : t * z ^ 2 ∈ J :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h8 : s * z ^ 2 ∈ J :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h9 : z ^ 3 ∈ J :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))
  have hmem {a b : A} (hab : a = b) (hb : b ∈ J) : a ∈ J := hab.symm ▸ hb
  change Ideal.span ({t, s, z} : Set A) ^ 3 ≤ J
  rw [pow_succ, pow_two, Ideal.span_mul_span, Ideal.span_mul_span]
  apply Ideal.span_le.mpr
  rintro w ⟨x, hx, y, hy, rfl⟩
  rcases hx with ⟨p, hp, q, hq, rfl⟩
  change p * q * y ∈ J
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl
  · refine hmem ?_ h0
    ring
  · refine hmem ?_ h1
    ring
  · refine hmem ?_ h4
    ring
  · refine hmem ?_ h1
    ring
  · refine hmem ?_ h2
    ring
  · exact h5
  · refine hmem ?_ h4
    ring
  · refine hmem ?_ h5
    ring
  · refine hmem ?_ h7
    ring
  · refine hmem ?_ h1
    ring
  · refine hmem ?_ h2
    ring
  · refine hmem ?_ h5
    ring
  · refine hmem ?_ h2
    ring
  · refine hmem ?_ h3
    ring
  · refine hmem ?_ h6
    ring
  · refine hmem ?_ h5
    ring
  · refine hmem ?_ h6
    ring
  · refine hmem ?_ h8
    ring
  · refine hmem ?_ h4
    ring
  · refine hmem ?_ h5
    ring
  · refine hmem ?_ h7
    ring
  · refine hmem ?_ h5
    ring
  · refine hmem ?_ h6
    ring
  · refine hmem ?_ h8
    ring
  · refine hmem ?_ h7
    ring
  · refine hmem ?_ h8
    ring
  · refine hmem ?_ h9
    ring

/-- A genuine tangent-square relation and the original three generators produce
one true cubic equation in the original ring, with original coefficients. -/
theorem exists_original_cubic_relation (I : Ideal A) (t s z : A)
    (hgen : I = Ideal.span ({t, s, z} : Set A)) (hz : z ^ 2 ∈ I ^ 3) :
    ∃ a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 : A,
      z ^ 2 + (a0 * t ^ 3 + a1 * t ^ 2 * s + a2 * t * s ^ 2 + a3 * s ^ 3) +
        z * (b0 * t ^ 2 + b1 * t * s + b2 * s ^ 2) +
        z ^ 2 * (c0 * t + c1 * s) + d0 * z ^ 3 = 0 := by
  have hneg : -(z ^ 2) ∈ Ideal.span ({t, s, z} : Set A) ^ 3 :=
    hgen ▸ (I ^ 3).neg_mem hz
  have h := span_triple_cube_le_cubic_monomials t s z hneg
  obtain ⟨a0, w0, hw0, h0⟩ := Ideal.mem_span_insert.mp h
  obtain ⟨a1, w1, hw1, h1⟩ := Ideal.mem_span_insert.mp hw0
  obtain ⟨a2, w2, hw2, h2⟩ := Ideal.mem_span_insert.mp hw1
  obtain ⟨a3, w3, hw3, h3⟩ := Ideal.mem_span_insert.mp hw2
  obtain ⟨b0, w4, hw4, h4⟩ := Ideal.mem_span_insert.mp hw3
  obtain ⟨b1, w5, hw5, h5⟩ := Ideal.mem_span_insert.mp hw4
  obtain ⟨b2, w6, hw6, h6⟩ := Ideal.mem_span_insert.mp hw5
  obtain ⟨c0, w7, hw7, h7⟩ := Ideal.mem_span_insert.mp hw6
  obtain ⟨c1, w8, hw8, h8⟩ := Ideal.mem_span_insert.mp hw7
  obtain ⟨d0, h9⟩ := Ideal.mem_span_singleton.mp hw8
  refine ⟨a0, a1, a2, a3, b0, b1, b2, c0, c1, d0, ?_⟩
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9] at h0
  linear_combination -h0

end Ideal

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A true cubic relation with a fourth-order remainder gives the true divided
relation on the actual saturated t-chart, with every original coefficient retained. -/
theorem exists_divided_cubic_relation
    (t s z : maximalIdeal A) (a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 R : A)
    (hR : R ∈ maximalIdeal A ^ 4)
    (hrel : (z : A) ^ 2 +
      (a0 * (t : A) ^ 3 + a1 * (t : A) ^ 2 * (s : A) +
        a2 * (t : A) * (s : A) ^ 2 + a3 * (s : A) ^ 3) +
      (z : A) * (b0 * (t : A) ^ 2 + b1 * (t : A) * (s : A) + b2 * (s : A) ^ 2) +
      (z : A) ^ 2 * (c0 * (t : A) + c1 * (s : A)) + d0 * (z : A) ^ 3 + R = 0) :
    ∃ ρ : saturatedChart A (maximalIdeal A) (t : A),
      let φ := algebraMap A (saturatedChart A (maximalIdeal A) (t : A))
      let τ := φ (t : A)
      let U := fractionElement (maximalIdeal A) t s
      let V := fractionElement (maximalIdeal A) t z
      V ^ 2 + τ * (φ a0 + φ a1 * U + φ a2 * U ^ 2 + φ a3 * U ^ 3) +
        τ * V * (φ b0 + φ b1 * U + φ b2 * U ^ 2 +
          φ c0 * V + φ c1 * U * V + φ d0 * V ^ 2) + τ ^ 2 * ρ = 0 := by
  let C := saturatedChart A (maximalIdeal A) (t : A)
  let φ : A →+* C := algebraMap A C
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  have hRm : φ R ∈ Ideal.span {τ ^ 4} := by
    have h := Ideal.mem_map_of_mem φ hR
    rw [map_center_pow_eq_span (maximalIdeal A) (t : A) 4 t.property] at h
    exact h
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton.mp hRm
  refine ⟨ρ, ?_⟩
  change V ^ 2 + τ * (φ a0 + φ a1 * U + φ a2 * U ^ 2 + φ a3 * U ^ 3) +
    τ * V * (φ b0 + φ b1 * U + φ b2 * U ^ 2 +
      φ c0 * V + φ c1 * U * V + φ d0 * V ^ 2) + τ ^ 2 * ρ = 0
  have hs : τ * U = φ (s : A) := fractionElement_mul (maximalIdeal A) t s
  have hz : τ * V = φ (z : A) := fractionElement_mul (maximalIdeal A) t z
  have hmap := congrArg φ hrel
  simp only [map_add, map_mul, map_pow, map_zero] at hmap
  rw [← hs, ← hz, hρ] at hmap
  apply exceptional_pow_mul_injective (maximalIdeal A) (t : A) 2
  change τ ^ 2 * _ = τ ^ 2 * 0
  rw [mul_zero]
  convert hmap using 1; ring

end Localization.Away.SaturatedChart

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The actual quotient cone with one distinguished degree-one parameter. -/
abbrev quotientCone (x : R) := R[X] ⧸ Ideal.span ({C x} : Set R[X])

/-- The original quotient map into the cone, with its native polynomial ring fixed. -/
def quotientConeMk (x : R) : R[X] →+* quotientCone x :=
  Ideal.Quotient.mk (Ideal.span ({C x} : Set R[X]))

/-- The distinguished original polynomial variable in the actual quotient cone. -/
def quotientConeParameter (x : R) : quotientCone x := quotientConeMk x X

/-- The actual parameter equation is the image of the original polynomial equation. -/
theorem quotientConeParameterIdeal_eq (x : R) :
    Ideal.span {quotientConeParameter x - 1} =
      (Ideal.span ({X - C (1 : R)} : Set R[X])).map (quotientConeMk x) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  change Ideal.span {quotientConeParameter x - 1} =
    Ideal.span {quotientConeParameter x - (quotientConeMk x) 1}
  rw [map_one]

/-- Setting the distinguished original variable equal to one leaves the original relation. -/
def quotientConeChartEquiv (x : R) :
    quotientCone x ⧸ Ideal.span {quotientConeParameter x - 1} ≃+*
      R ⧸ Ideal.span ({x} : Set R) :=
  (Ideal.quotEquivOfEq (quotientConeParameterIdeal_eq x)).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({C x} : Set R[X]))
        (Ideal.span ({X - C (1 : R)} : Set R[X]))).trans
      ((Ideal.quotEquivOfEq (show Ideal.span ({C x} : Set R[X]) ⊔
          Ideal.span ({X - C (1 : R)} : Set R[X]) =
            Ideal.span ({C x, X - C (1 : R)} : Set R[X]) by
        rw [Ideal.span_insert])).trans
          (quotientSpanCXSubCAlgEquiv x (1 : R)).toRingEquiv))

/-- The native two-relation quotient equivalence retains evaluation of every original polynomial. -/
theorem quotientSpanCXSubCAlgEquiv_mk (x y : R) (p : R[X]) :
    quotientSpanCXSubCAlgEquiv x y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval y) := rfl

/-- The actual numerator is evaluated at the original parameter value one. -/
theorem quotientConeChartEquiv_mk_mk (x : R) (p : R[X]) :
    (quotientConeChartEquiv x).toRingHom
      (Ideal.Quotient.mk (Ideal.span {quotientConeParameter x - 1})
        (quotientConeMk x p)) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  let J₁ : Ideal R[X] := Ideal.span {C x}
  let J₂ : Ideal R[X] := Ideal.span {X - C (1 : R)}
  have hsum : J₁ ⊔ J₂ = Ideal.span ({C x, X - C (1 : R)} : Set R[X]) := by
    rw [Ideal.span_insert]
  let e₀ := Ideal.quotEquivOfEq (quotientConeParameterIdeal_eq x)
  let e₁ := DoubleQuot.quotQuotEquivQuotSup J₁ J₂
  let e₂ := Ideal.quotEquivOfEq hsum
  let e₃ := (quotientSpanCXSubCAlgEquiv x (1 : R)).toRingEquiv
  have h₀ : e₀ (Ideal.Quotient.mk (Ideal.span {quotientConeParameter x - 1})
      (quotientConeMk x p)) = DoubleQuot.quotQuotMk J₁ J₂ p :=
    Ideal.quotEquivOfEq_mk (quotientConeParameterIdeal_eq x) (quotientConeMk x p)
  change e₃ (e₂ (e₁ (e₀ (Ideal.Quotient.mk
    (Ideal.span {quotientConeParameter x - 1}) (quotientConeMk x p))))) = _
  calc
    _ = e₃ (e₂ (e₁ (DoubleQuot.quotQuotMk J₁ J₂ p))) :=
      congrArg (fun y => e₃ (e₂ (e₁ y))) h₀
    _ = e₃ (e₂ (Ideal.Quotient.mk (J₁ ⊔ J₂) p)) :=
      congrArg (fun y => e₃ (e₂ y))
        (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk J₁ J₂ p)
    _ = e₃ (Ideal.Quotient.mk (Ideal.span ({C x, X - C (1 : R)} : Set R[X])) p) :=
      congrArg e₃ (Ideal.quotEquivOfEq_mk hsum p)
    _ = _ := quotientSpanCXSubCAlgEquiv_mk x 1 p

end Polynomial

namespace HomogeneousLocalization.Away

variable {D R : Type u} [CommRing D] [CommRing R] (J : Ideal D) {f : D ⧸ J}

/-- The original presentation sends the original parameter equation to the cone equation. -/
theorem quotientCone_mappedIdeal (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x) :
    Ideal.span {Polynomial.quotientConeParameter x - 1} =
      (dehomogenizingIdeal (f := f)).map E.toRingHom := by
  rw [dehomogenizingIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {Polynomial.quotientConeParameter x - 1} =
    Ideal.span {E.toRingHom (f - 1)}
  rw [map_sub, map_one, hE]

/-- The original two-step quotient comparison before homogeneous localization. -/
def quotientConeQuotientEquiv (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x) :
    (D ⧸ J) ⧸ dehomogenizingIdeal (f := f) ≃+* R ⧸ Ideal.span {x} :=
  (Ideal.quotientEquiv _ _ E (quotientCone_mappedIdeal J x E hE)).trans
    (Polynomial.quotientConeChartEquiv x)

/-- The original quotient numerator is retained by the two-step comparison. -/
theorem quotientConeQuotientEquiv_mk (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x)
    (y : D ⧸ J) (p : R[X]) (hyp : E.toRingHom y = Polynomial.quotientConeMk x p) :
    (quotientConeQuotientEquiv J x E hE).toRingHom
      (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) y) =
        Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  let e := Ideal.quotientEquiv _ _ E (quotientCone_mappedIdeal J x E hE)
  have hq : e.toRingHom (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) y) =
      Ideal.Quotient.mk (Ideal.span {Polynomial.quotientConeParameter x - 1})
        (E.toRingHom y) := by
    simpa only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      Ideal.quotientEquiv_mk _ _ E (quotientCone_mappedIdeal J x E hE) y
  have he : e.toRingHom (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) y) =
      Ideal.Quotient.mk (Ideal.span {Polynomial.quotientConeParameter x - 1})
        (Polynomial.quotientConeMk x p) :=
    hq.trans (congrArg (Ideal.Quotient.mk
      (Ideal.span {Polynomial.quotientConeParameter x - 1})) hyp)
  change (Polynomial.quotientConeChartEquiv x).toRingHom
    (e.toRingHom (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) y)) = _
  exact (congrArg (Polynomial.quotientConeChartEquiv x).toRingHom he).trans
    (Polynomial.quotientConeChartEquiv_mk_mk x p)

variable {A : Type u} [CommRing A] [Algebra A D]
  (G : ℕ → Submodule A (D ⧸ J)) [GradedAlgebra G]

/-- Dehomogenize the original quotient grading through its actual cone presentation. -/
def quotientConeEquiv (hf : f ∈ G 1) (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x) :
    Away G f ≃+* R ⧸ Ideal.span ({x} : Set R) :=
  (degreeOneQuotientEquiv G hf).trans (quotientConeQuotientEquiv J x E hE)

/-- Every original homogeneous numerator follows the actual presentation and evaluation maps. -/
theorem quotientConeEquiv_mk (hf : f ∈ G 1) (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x)
    (n : ℕ) (y : D ⧸ J) (hy : y ∈ G (n • 1)) (p : R[X])
    (hyp : E.toRingHom y = Polynomial.quotientConeMk x p) :
    (quotientConeEquiv J G hf x E hE).toRingHom (Away.mk G hf n y hy) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  have hraw : (degreeOneQuotientEquiv G hf).toRingHom (Away.mk G hf n y hy) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) y := by
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      degreeOneQuotientEquiv_mk G hf n y hy
  change (quotientConeQuotientEquiv J x E hE).toRingHom
    ((degreeOneQuotientEquiv G hf).toRingHom (Away.mk G hf n y hy)) = _
  exact (congrArg (quotientConeQuotientEquiv J x E hE).toRingHom hraw).trans
    (quotientConeQuotientEquiv_mk J x E hE y p hyp)

end HomogeneousLocalization.Away

namespace reesAlgebra

variable {A R : Type u} [CommRing A] [CommRing R] (I : Ideal A) (a : I)
  (x : R) (E : I.associatedGraded ≃+* Polynomial.quotientCone x)
  (ha : E.toRingHom (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I a)) =
    Polynomial.quotientConeParameter x)

/-- The actual associated-graded cone presentation yields the actual exceptional chart model. -/
def exceptionalQuotientConeEquiv :
    (Localization.Away.saturatedChart A I (a : A)) ⧸
        Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)} ≃+*
      R ⧸ Ideal.span ({x} : Set R) :=
  (exceptionalChartEquiv I a).trans
    (HomogeneousLocalization.Away.quotientConeEquiv (D := reesAlgebra I)
      I.associatedGradedIdeal I.associatedGradedGrading
      (degreeOne_associatedGraded_mem I a) x E ha)

/-- Each original b/a retains the numerator supplied by the actual tangent-cone presentation. -/
theorem exceptionalQuotientConeEquiv_mk_fraction (b : I) (p : R[X])
    (hb : E.toRingHom (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I b)) =
      Polynomial.quotientConeMk x p) :
    (exceptionalQuotientConeEquiv I a x E ha).toRingHom
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (Localization.Away.SaturatedChart.fractionElement I a b)) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  let e := HomogeneousLocalization.Away.quotientConeEquiv (D := reesAlgebra I)
    I.associatedGradedIdeal I.associatedGradedGrading
    (degreeOne_associatedGraded_mem I a) x E ha
  have hraw : (exceptionalChartEquiv I a).toRingHom
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (Localization.Away.SaturatedChart.fractionElement I a b)) =
      HomogeneousLocalization.Away.mk I.associatedGradedGrading
        (degreeOne_associatedGraded_mem I a) 1
        (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I b))
        (by simpa only [one_smul] using degreeOne_associatedGraded_mem I b) := by
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      exceptionalChartEquiv_mk_fraction I a b
  change e.toRingHom ((exceptionalChartEquiv I a).toRingHom
    (Ideal.Quotient.mk
      (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
      (Localization.Away.SaturatedChart.fractionElement I a b))) = _
  exact (congrArg e.toRingHom hraw).trans
    (HomogeneousLocalization.Away.quotientConeEquiv_mk (D := reesAlgebra I)
      I.associatedGradedIdeal I.associatedGradedGrading
      (degreeOne_associatedGraded_mem I a) x E ha 1 _ _ p hb)

end reesAlgebra

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The nilpotent coordinate of the literal double-line quotient. -/
def doubleLineCoordinate : R[X] ⧸ Ideal.span ({X ^ 2} : Set R[X]) :=
  Ideal.Quotient.mk _ X

/-- The original nilpotent coordinate has exactly its own principal annihilator. -/
theorem mul_doubleLineCoordinate_eq_zero_iff
    (x : R[X] ⧸ Ideal.span ({X ^ 2} : Set R[X])) :
    x * doubleLineCoordinate (R := R) = 0 ↔
      x ∈ Ideal.span {doubleLineCoordinate (R := R)} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro h
    have hp : (X : R[X]) ^ 2 ∣ p * X := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [doubleLineCoordinate, map_mul] using h
    have hp0 : p.coeff 0 = 0 := by
      simpa only [coeff_mul_X] using (X_pow_dvd_iff.mp hp 1 (by decide))
    have hmem := Ideal.mem_map_of_mem
      (Ideal.Quotient.mk (Ideal.span ({X ^ 2} : Set R[X])))
      (Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr hp0))
    simpa only [Ideal.map_span, Set.image_singleton, doubleLineCoordinate] using hmem
  · intro h
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp h
    rw [hy, mul_comm (doubleLineCoordinate (R := R)) y, mul_assoc,
      ← pow_two, doubleLineCoordinate, ← map_pow]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), mul_zero]

/-- Over the original domain of line coordinates, the double line has its actual generic prime. -/
theorem doubleLineCoordinate_span_isPrime [IsDomain R] :
    (Ideal.span {doubleLineCoordinate (R := R)}).IsPrime := by
  have hX : (Ideal.span ({X} : Set R[X])).IsPrime := by
    rw [← ker_constantCoeff]
    exact RingHom.ker_isPrime (constantCoeff : R[X] →+* R)
  let : (Ideal.span ({X} : Set R[X])).IsPrime := hX
  have hle : Ideal.span ({X ^ 2} : Set R[X]) ≤ Ideal.span ({X} : Set R[X]) := by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = X ^ 2)
    exact Ideal.mem_span_singleton.mpr ⟨X, pow_two X⟩
  have h := Ideal.isPrime_map_quotientMk_of_isPrime hle
  simpa only [Ideal.map_span, Set.image_singleton, doubleLineCoordinate] using h

end Polynomial

namespace Ideal

variable {R S : Type u} [CommRing R] [CommRing S]
  {t v : S}
  (φ : S →+* R[X] ⧸ Ideal.span ({X ^ 2} : Set R[X]))
  (hφ : Function.Surjective φ)
  (hker : RingHom.ker φ = Ideal.span ({t} : Set S))
  (hv : φ v = Polynomial.doubleLineCoordinate (R := R))

include hφ hker hv

/-- The original prime preimage is generated by the original parameter
and double-line coordinate. -/
theorem doubleLine_comap_span :
    (Ideal.span {Polynomial.doubleLineCoordinate (R := R)}).comap φ =
      Ideal.span ({t, v} : Set S) := by
  have hmap : (Ideal.span ({v} : Set S)).map φ =
      Ideal.span {Polynomial.doubleLineCoordinate (R := R)} := by
    rw [Ideal.map_span, Set.image_singleton, hv]
  rw [← hmap, Ideal.comap_map_of_surjective' φ hφ, hker,
    sup_comm, ← Ideal.span_insert]

/-- The original double-line chart quotient supplies the actual prime, without a prime oracle. -/
theorem span_pair_isPrime_of_doubleLine_quotient [IsDomain R] :
    (Ideal.span ({t, v} : Set S)).IsPrime := by
  have h := Polynomial.doubleLineCoordinate_span_isPrime (R := R)
  let : (Ideal.span {Polynomial.doubleLineCoordinate (R := R)}).IsPrime := h
  have hp : ((Ideal.span {Polynomial.doubleLineCoordinate (R := R)}).comap φ).IsPrime :=
    inferInstance
  exact doubleLine_comap_span φ hφ hker hv ▸ hp

/-- The original exceptional quotient supplies the annihilator condition at its generic point. -/
theorem mul_mem_parameter_implies_mem_pair_of_doubleLine_quotient
    (c : S) (hc : c * v ∈ Ideal.span ({t} : Set S)) :
    c ∈ Ideal.span ({t, v} : Set S) := by
  rw [← doubleLine_comap_span φ hφ hker hv]
  change φ c ∈ Ideal.span {Polynomial.doubleLineCoordinate (R := R)}
  apply (Polynomial.mul_doubleLineCoordinate_eq_zero_iff (φ c)).mp
  rw [← hv, ← map_mul]
  exact (show c * v ∈ RingHom.ker φ from hker.symm ▸ hc)

end Ideal

namespace Ideal

variable {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
  {t v : S} (q : Ideal S) [q.IsPrime]

omit [IsDomain S] [IsNoetherianRing S] in
/-- The actual generic double-line prime is minimal over the actual exceptional parameter. -/
theorem span_pair_mem_minimalPrimes_of_sq_mem
    (hq : q = Ideal.span ({t, v} : Set S)) (hv : v ^ 2 ∈ Ideal.span ({t} : Set S)) :
    q ∈ (Ideal.span ({t} : Set S)).minimalPrimes := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = t)
    rw [hq]
    exact Ideal.subset_span (by simp)
  · intro p hp hpq
    rw [hq]
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact hp.2 (Ideal.subset_span (by simp))
    · exact hp.1.mem_of_pow_mem 2 (hp.2 hv)

/-- A nonzero actual exceptional parameter gives height one at that prime. -/
theorem height_eq_one_of_span_pair_of_sq_mem
    (ht : t ≠ 0) (hq : q = Ideal.span ({t, v} : Set S))
    (hv : v ^ 2 ∈ Ideal.span ({t} : Set S)) : q.height = 1 := by
  have hmin := span_pair_mem_minimalPrimes_of_sq_mem q hq hv
  have hq0 : q ≠ ⊥ := by
    intro hzero
    have htq := hmin.1.2 (Ideal.subset_span (by simp : t ∈ ({t} : Set S)))
    exact ht (by simpa only [hzero, Ideal.mem_bot] using htq)
  exact le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {t}) q hmin)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hq0))

omit [IsDomain S] [IsNoetherianRing S] in
/-- The actual double-line class remains nonzero after localization at its generic prime. -/
theorem localized_doubleLine_not_mem_parameter
    (hann : ∀ c : S, c * v ∈ Ideal.span ({t} : Set S) → c ∈ q) :
    algebraMap S (Localization.AtPrime q) v ∉
      Ideal.span {algebraMap S (Localization.AtPrime q) t} := by
  intro hv
  have hmap : (Ideal.span ({t} : Set S)).map (algebraMap S (Localization.AtPrime q)) =
      Ideal.span {algebraMap S (Localization.AtPrime q) t} := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨c, hc, hcv⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) (Ideal.span {t}) v).mp (hmap.symm ▸ hv)
  exact hc (hann c hcv)

/-- The original generic chart equation forces its actual cubic coefficient to be a unit.
The DVR is derived from normality and the original exceptional prime. -/
theorem isUnit_cubicCoefficient_at_generic_doubleLine [IsIntegrallyClosed S]
    (H l r : S) (ht : t ≠ 0) (hq : q = Ideal.span ({t, v} : Set S))
    (hann : ∀ c : S, c * v ∈ Ideal.span ({t} : Set S) → c ∈ q)
    (hrel : v ^ 2 + t * H + t * v * l + t ^ 2 * r = 0) :
    IsUnit (algebraMap S (Localization.AtPrime q) H) := by
  have hv : v ^ 2 ∈ Ideal.span ({t} : Set S) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-(H + v * l + t * r), ?_⟩
    linear_combination hrel
  let D := Localization.AtPrime q
  let : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one q D
      (height_eq_one_of_span_pair_of_sq_mem q ht hq hv)
  have hgen : IsLocalRing.maximalIdeal D =
      Ideal.span ({algebraMap S D t, algebraMap S D v} : Set D) := by
    have hmap := congrArg (Ideal.map (algebraMap S D)) hq
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at hmap
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal q D).symm.trans hmap
  apply IsLocalRing.isUnit_cubic_coefficient_of_generic_double_line D
    (algebraMap S D t) (algebraMap S D v) (algebraMap S D H)
    (algebraMap S D l) (algebraMap S D r) hgen
    (localized_doubleLine_not_mem_parameter q hann)
  simpa only [map_add, map_mul, map_pow, map_zero] using congrArg (algebraMap S D) hrel

end Ideal

namespace Localization.Away

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Every actual prime on the exceptional divisor gives a local original coefficient map. -/
theorem localizedChartMap_isLocal_of_parameter_mem
    (t : maximalIdeal A)
    (q : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [q.IsPrime]
    (ht : algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A) ∈ q) :
    IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) q) := by
  apply ((local_hom_TFAE (localizedChartMap (maximalIdeal A) (t : A) q)).out 1 3).mpr
  rw [localizedChartMap_center (maximalIdeal A) (t : A) t.property]
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).mpr ht

/-- A square-alignment coefficient whose original residue vanishes is divisible
by the same original exceptional parameter in the actual localized chart. -/
theorem exists_square_alignment_coefficient
    (t : maximalIdeal A)
    (q : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [q.IsPrime]
    (c mu : A) (hc : residue A (c - 2 * mu) = 0) :
    ∃ b : Localization.AtPrime q,
      localizedChartMap (maximalIdeal A) (t : A) q c -
        2 * localizedChartMap (maximalIdeal A) (t : A) q mu =
          localizedChartMap (maximalIdeal A) (t : A) q (t : A) * b := by
  let φ := localizedChartMap (maximalIdeal A) (t : A) q
  have hmem : c - 2 * mu ∈ maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.mp hc
  have h := Ideal.mem_map_of_mem φ hmem
  rw [localizedChartMap_center (maximalIdeal A) (t : A) t.property] at h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h
  refine ⟨b, ?_⟩
  simpa only [map_sub, map_mul, map_ofNat] using hb

end Localization.Away

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The binary cubic on the fixed affine chart, reduced through the original residue map. -/
def residueBinaryCubic (a0 a1 a2 a3 : A) : (ResidueField A)[X] :=
  C (residue A a3) * X ^ 3 + C (residue A a2) * X ^ 2 +
    C (residue A a1) * X + C (residue A a0)

/-- The actual reduced polynomial has degree at most three. -/
theorem residueBinaryCubic_natDegree_le (a0 a1 a2 a3 : A) :
    (residueBinaryCubic a0 a1 a2 a3).natDegree ≤ 3 := natDegree_cubic_le

/-- An actual local map and a unit value of the original cubic coefficient prove
the same residue polynomial nonzero, without requiring a coefficient field. -/
theorem residueBinaryCubic_ne_zero_of_isUnit
    {D : Type u} [CommRing D] [IsLocalRing D]
    (c : A →+* D) [IsLocalHom c] (U : D) (a0 a1 a2 a3 : A)
    (hH : IsUnit (c a0 + c a1 * U + c a2 * U ^ 2 + c a3 * U ^ 3)) :
    residueBinaryCubic a0 a1 a2 a3 ≠ 0 := by
  let E : (ResidueField A)[X] →+* ResidueField D :=
    eval₂RingHom (ResidueField.map c) (residue D U)
  have he : E (residueBinaryCubic a0 a1 a2 a3) =
      residue D (c a0 + c a1 * U + c a2 * U ^ 2 + c a3 * U ^ 3) := by
    change eval₂ (ResidueField.map c) (residue D U)
      (residueBinaryCubic a0 a1 a2 a3) = _
    simp only [residueBinaryCubic, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C,
      eval₂_X, ResidueField.map_residue, map_add, map_mul, map_pow]
    ring
  intro hz
  apply (hH.map (residue D)).ne_zero
  rw [← he, hz, map_zero]

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]

/-- The original tangent-square presentation and normality of the actual chart
produce a true original cubic relation with nonzero original residue cubic. -/
theorem exists_original_cubic_relation_nonzero
    (t s z : maximalIdeal A) (ht0 : (t : A) ≠ 0)
    [IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A))]
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (reesAlgebra.degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2))
    (hEz : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (reesAlgebra.degreeOne (maximalIdeal A) z)) =
      Polynomial.quotientConeMk ((X : (ResidueField A)[X][X]) ^ 2)
        (C (X : (ResidueField A)[X][X]))) :
    ∃ a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 : A,
      ((z : A) ^ 2 +
        (a0 * (t : A) ^ 3 + a1 * (t : A) ^ 2 * (s : A) +
          a2 * (t : A) * (s : A) ^ 2 + a3 * (s : A) ^ 3) +
        (z : A) * (b0 * (t : A) ^ 2 + b1 * (t : A) * (s : A) + b2 * (s : A) ^ 2) +
        (z : A) ^ 2 * (c0 * (t : A) + c1 * (s : A)) + d0 * (z : A) ^ 3 = 0) ∧
      IsLocalRing.residueBinaryCubic a0 a1 a2 a3 ≠ 0 := by
  let S := saturatedChart A (maximalIdeal A) (t : A)
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
  have hsq : (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) z)) ^ 2 = 0 := by
    apply E.injective
    change E.toRingHom ((Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) z)) ^ 2) = E.toRingHom 0
    rw [map_pow, hEz, map_zero]
    have hzero : Polynomial.quotientConeMk ((X : (ResidueField A)[X][X]) ^ 2)
        (C ((X : (ResidueField A)[X][X]) ^ 2)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_pow] using hzero
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, c0, c1, d0, hrel⟩ :=
    Ideal.exists_original_cubic_relation (maximalIdeal A) (t : A) (s : A) (z : A) hgen
      ((Ideal.associatedGraded_degreeOne_sq_eq_zero_iff (maximalIdeal A) z).mp hsq)
  refine ⟨a0, a1, a2, a3, b0, b1, b2, c0, c1, d0, hrel, ?_⟩
  obtain ⟨ρ, hdiv⟩ := exists_divided_cubic_relation t s z
    a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 0 (Ideal.zero_mem _)
    (by simpa only [add_zero] using hrel)
  let e := reesAlgebra.exceptionalQuotientConeEquiv (maximalIdeal A) t
    ((X : (ResidueField A)[X][X]) ^ 2) E hEt
  let φ : S →+* (ResidueField A)[X][X] ⧸ Ideal.span {(X : (ResidueField A)[X][X]) ^ 2} :=
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
  have hV : φ V = Polynomial.doubleLineCoordinate (R := (ResidueField A)[X]) := by
    simpa only [φ, e, τ, cA, V, RingHom.comp_apply,
      Polynomial.doubleLineCoordinate, eval_C] using
      reesAlgebra.exceptionalQuotientConeEquiv_mk_fraction (maximalIdeal A) t
        ((X : (ResidueField A)[X][X]) ^ 2) E hEt z (C (X : (ResidueField A)[X][X])) hEz
  let q : Ideal S := Ideal.span ({τ, V} : Set S)
  let : q.IsPrime := Ideal.span_pair_isPrime_of_doubleLine_quotient φ hφ hker hV
  have hann : ∀ b : S, b * V ∈ Ideal.span {τ} → b ∈ q :=
    Ideal.mul_mem_parameter_implies_mem_pair_of_doubleLine_quotient φ hφ hker hV
  let H := cA a0 + cA a1 * U + cA a2 * U ^ 2 + cA a3 * U ^ 3
  let L := cA b0 + cA b1 * U + cA b2 * U ^ 2 +
    cA c0 * V + cA c1 * U * V + cA d0 * V ^ 2
  have hdiv' : V ^ 2 + τ * H + τ * V * L + τ ^ 2 * ρ = 0 := hdiv
  have hunit := Ideal.isUnit_cubicCoefficient_at_generic_doubleLine q H L ρ htC rfl hann hdiv'
  let D := Localization.AtPrime q
  let c : A →+* D := localizedChartMap (maximalIdeal A) (t : A) q
  let : IsLocalHom c := localizedChartMap_isLocal_of_parameter_mem t q
    (Ideal.subset_span (Or.inl rfl))
  apply IsLocalRing.residueBinaryCubic_ne_zero_of_isUnit c (algebraMap S D U) a0 a1 a2 a3
  simpa only [H, c, cA, localizedChartMap, RingHom.comp_apply,
    map_add, map_mul, map_pow] using hunit

end Localization.Away.SaturatedChart

namespace IsLocalRing

/-- Singularity forces the actual cubic coefficient into the actual maximal ideal.
Otherwise the displayed relation would put the minimal exceptional element in m². -/
theorem cubic_coefficient_mem_maximal_of_singular_chart
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (t v q H l r : B) (hgen : maximalIdeal B = Ideal.span ({t, v, q} : Set B))
    (hd : ringKrullDim B = 2) (hsing : ¬ IsRegularLocalRing B)
    (hrel : v ^ 2 + t * H + t * v * l + t ^ 2 * r = 0) : H ∈ maximalIdeal B := by
  have ht : t ∈ maximalIdeal B := by rw [hgen]; exact Ideal.subset_span (by simp)
  have hv : v ∈ maximalIdeal B := by rw [hgen]; exact Ideal.subset_span (by simp)
  by_contra hH
  let G := H + v * l + t * r
  have hG : IsUnit G := by
    apply notMem_maximalIdeal.mp
    intro hGm
    apply hH
    have he : H = G - (v * l + t * r) := by dsimp [G]; ring
    rw [he]
    exact (maximalIdeal B).sub_mem hGm ((maximalIdeal B).add_mem
      ((maximalIdeal B).mul_mem_right l hv) ((maximalIdeal B).mul_mem_right r ht))
  have hs : v ^ 2 + t * G = 0 := by
    calc
      _ = v ^ 2 + t * H + t * v * l + t ^ 2 * r := by dsimp [G]; ring
      _ = 0 := hrel
  have htG : t * G = -(v ^ 2) :=
    add_eq_zero_iff_eq_neg.mp ((add_comm (t * G) (v ^ 2)).trans hs)
  have hv2 : v ^ 2 ∈ maximalIdeal B ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hv hv
  have hmG : t * G ∈ maximalIdeal B ^ 2 := by
    rw [htG]
    exact (maximalIdeal B ^ 2).neg_mem hv2
  obtain ⟨w, hw⟩ := hG
  have htw : t * (w : B) ∈ maximalIdeal B ^ 2 := by rw [hw]; exact hmG
  have htm : t ∈ maximalIdeal B ^ 2 := by
    have h := (maximalIdeal B ^ 2).mul_mem_right ((w⁻¹ : Bˣ) : B) htw
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h
  exact first_not_mem_sq_of_span_triple_of_not_regular B t v q hgen hd hsing htm

end IsLocalRing

namespace Polynomial

/-- A scalar square of degree at most one in the distinguished coordinate has
zero linear coefficient over a domain. This does not extend the coefficient field. -/
theorem coeff_one_eq_zero_of_scalar_square_of_natDegree_le_one
    {R : Type u} [CommRing R] [IsDomain R] {f g : R[X]} (c : R)
    (hsq : f = C c * g ^ 2) (hdeg : f.natDegree ≤ 1) : f.coeff 1 = 0 := by
  by_cases hc : c = 0
  · simp only [hsq, hc, map_zero, zero_mul, coeff_zero]
  by_cases hg : g = 0
  · simp only [hsq, hg, zero_pow (by decide : 2 ≠ 0), mul_zero, coeff_zero]
  have heq : f.natDegree = 2 * g.natDegree := by
    rw [hsq, natDegree_mul (C_ne_zero.mpr hc) (pow_ne_zero 2 hg), natDegree_C,
      natDegree_pow, zero_add]
  have hg0 : g.natDegree = 0 := by omega
  apply coeff_eq_zero_of_natDegree_lt
  rw [heq, hg0, mul_zero]
  exact Nat.zero_lt_one

end Polynomial

namespace Polynomial

variable {k : Type u} [Field k]

/-- A repeated irreducible divisor of a nonzero cubic has degree one over the
original coefficient field. This is the rationality part of the point criterion. -/
theorem natDegree_eq_one_of_irreducible_sq_dvd_cubic
    {h q : k[X]} (hh : h ≠ 0) (hdeg : h.natDegree ≤ 3)
    (hq : Irreducible q) (hdiv : q ^ 2 ∣ h) : q.natDegree = 1 := by
  have hbound := (natDegree_le_of_dvd hdiv hh).trans hdeg
  rw [natDegree_pow] at hbound
  have hpos := hq.natDegree_pos
  omega

/-- The monic repeated prime is the actual linear polynomial of a point over
the same residue field. Its coordinate is constructed from its constant term. -/
theorem exists_eq_X_sub_C_of_monic_irreducible_sq_dvd_cubic
    {h q : k[X]} (hh : h ≠ 0) (hdeg : h.natDegree ≤ 3)
    (hq : Irreducible q) (hm : q.Monic) (hdiv : q ^ 2 ∣ h) :
    ∃ α : k, q = X - C α := by
  refine ⟨-q.coeff 0, ?_⟩
  exact (hm.eq_X_add_C (natDegree_eq_one_of_irreducible_sq_dvd_cubic hh hdeg hq hdiv)).trans
    (by simp)

/-- Two repeated irreducible divisors of the same nonzero cubic represent
the same prime; four units of total degree cannot fit in degree at most three. -/
theorem associated_of_irreducible_sq_dvd_cubic
    {h p q : k[X]} (hh : h ≠ 0) (hdeg : h.natDegree ≤ 3)
    (hp : Irreducible p) (hq : Irreducible q)
    (hpdiv : p ^ 2 ∣ h) (hqdiv : q ^ 2 ∣ h) : Associated p q := by
  by_contra hne
  have hndvd : ¬ p ∣ q := fun hdvd => hne (hp.associated_of_dvd hq hdvd)
  have hc : IsCoprime (p ^ 2) (q ^ 2) := (hp.coprime_iff_not_dvd.mpr hndvd).pow
  have hbound := (natDegree_le_of_dvd (hc.mul_dvd hpdiv hqdiv) hh).trans hdeg
  rw [natDegree_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    natDegree_pow, natDegree_pow] at hbound
  have hpdeg := hp.natDegree_pos
  have hqdeg := hq.natDegree_pos
  omega

end Polynomial
