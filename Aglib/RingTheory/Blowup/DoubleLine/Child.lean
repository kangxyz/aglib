/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.DoubleLine
public import Aglib.RingTheory.AssociatedGraded.Cotangent.Graded
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.FinCases

/-!
# Actual Case-II children of a double-line blowup chart

The quadratic initial relation of a simple prime factor has a nonzero mixed
term and no square term in that prime parameter. The canonical cotangent
polynomial map of the actual child therefore cannot have a linear-square
kernel. This argument uses the prime polynomial itself, including at an
inseparable closed point, and does not introduce a coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace MvPolynomial

variable {k : Type u} [Field k]

/-- The actual quadratic relation, in the order `Q,V,T`. There is no `Q²` term. -/
def doubleLineChildQuadratic (c d e : k) : MvPolynomial (Fin 3) k :=
  X 1 ^ 2 + X 2 * (C c * X 0 + C d * X 1 + C e * X 2)

private theorem doubleLineChildQuadratic_homogeneous (c d e : k) :
    (doubleLineChildQuadratic c d e).IsHomogeneous 2 :=
  (isHomogeneous_X_pow 1 2).add
    ((isHomogeneous_X k 2).mul
      (((isHomogeneous_C_mul_X c 0).add (isHomogeneous_C_mul_X d 1)).add
        (isHomogeneous_C_mul_X e 2)))

private theorem doubleLineChildQuadratic_ne_zero (c d e : k) :
    doubleLineChildQuadratic c d e ≠ 0 := by
  intro h
  have := congrArg (eval₂Hom (RingHom.id k) ![0, 1, 0]) h
  simp [doubleLineChildQuadratic] at this

/-- A homogeneous quadratic in a linear-square ideal is a scalar square.
The statement concerns the actual polynomial, not a rank approximation. -/
theorem eq_scalar_square_of_mem_span_square
    {f L : MvPolynomial (Fin 3) k}
    (hf : f.IsHomogeneous 2) (hf0 : f ≠ 0) (hL : L.IsHomogeneous 1)
    (hmem : f ∈ Ideal.span {L ^ 2}) :
    ∃ c : k, f = C c * L ^ 2 := by
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
  have hL0 : L ≠ 0 := by
    intro hz
    simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hp
    exact hf0 hp
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hp
    exact hf0 hp
  have hdeg := hf.totalDegree_le
  rw [hp, totalDegree_mul_of_isDomain (pow_ne_zero _ hL0) hp0,
    (hL.pow 2).totalDegree (pow_ne_zero _ hL0)] at hdeg
  have hpdeg : p.totalDegree = 0 := by omega
  have hpC := totalDegree_eq_zero_iff_eq_C.mp hpdeg
  refine ⟨p.coeff 0, ?_⟩
  calc
    f = L ^ 2 * p := hp
    _ = L ^ 2 * C (p.coeff 0) := congrArg (fun x => L ^ 2 * x) hpC
    _ = C (p.coeff 0) * L ^ 2 := mul_comm _ _

/-- The mixed coefficient vanishes if this quadratic belongs to an actual
linear-square kernel. This works in every characteristic. -/
theorem doubleLineChildQuadratic_coefficient_eq_zero
    (c d e : k) (L : MvPolynomial (Fin 3) k) (hL : L.IsHomogeneous 1)
    (hmem : doubleLineChildQuadratic c d e ∈ Ideal.span {L ^ 2}) : c = 0 := by
  obtain ⟨a, ha⟩ := eq_scalar_square_of_mem_span_square
    (doubleLineChildQuadratic_homogeneous c d e)
    (doubleLineChildQuadratic_ne_zero c d e) hL hmem
  let R : Type u := MvPolynomial (Fin 2) k
  let ψ : MvPolynomial (Fin 3) k →+* R[X] :=
    eval₂Hom (Polynomial.C.comp MvPolynomial.C)
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1)]
  have hψQ : ψ (MvPolynomial.X 0) = Polynomial.X := by simp [ψ]
  have hψV : ψ (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by simp [ψ]
  have hψT : ψ (MvPolynomial.X 2) = Polynomial.C (MvPolynomial.X 1) := by simp [ψ]
  have hψC (x : k) : ψ (MvPolynomial.C x) = Polynomial.C (MvPolynomial.C x) := by
    simp [ψ]
  have hψ : ψ (doubleLineChildQuadratic c d e) =
      Polynomial.C (MvPolynomial.C c * MvPolynomial.X 1) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 *
          (MvPolynomial.C d * MvPolynomial.X 0 + MvPolynomial.C e * MvPolynomial.X 1)) := by
    simp only [doubleLineChildQuadratic, map_add, map_mul, map_pow, hψQ, hψV, hψT, hψC]
    ring
  have hsq : ψ (doubleLineChildQuadratic c d e) =
      Polynomial.C (MvPolynomial.C a) * ψ L ^ 2 := by
    rw [ha, map_mul, map_pow, hψC]
  have hdeg : (ψ (doubleLineChildQuadratic c d e)).natDegree ≤ 1 := by
    rw [hψ]
    exact Polynomial.natDegree_linear_le
  have hc := Polynomial.coeff_one_eq_zero_of_scalar_square_of_natDegree_le_one
    (MvPolynomial.C a) hsq hdeg
  rw [hψ] at hc
  have hprod : MvPolynomial.C c * (MvPolynomial.X 1 : R) = 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at hc
    norm_num only at hc
    rw [ite_true, ite_false, add_zero] at hc
    exact hc
  apply MvPolynomial.C_injective (Fin 2) k
  simpa only [map_zero] using (mul_eq_zero.mp hprod).resolve_right (X_ne_zero 1)

end MvPolynomial

namespace IsLocalRing

/-- The literal canonical cotangent kernel, with its original residue-field
carrier fixed before specializing to a prime localization. -/
def doubleLineChildCotangentKernel (B : Type u) [CommRing B] [IsLocalRing B]
    (g : Fin 3 → maximalIdeal B) : Ideal (MvPolynomial (Fin 3) (ResidueField B)) :=
  RingHom.ker (R := MvPolynomial (Fin 3) (B ⧸ maximalIdeal B))
    (S := (maximalIdeal B).associatedGraded)
    (Ideal.cotangentPolynomialMap (maximalIdeal B) g).toRingHom

variable {B : Type u} [CommRing B] [IsLocalRing B]

/-- A true relation in the original local ring gives the corresponding quadratic
in the kernel of its canonical cotangent polynomial map. -/
theorem doubleLineChildQuadratic_mem_cotangent_kernel
    (t v q : maximalIdeal B) (c d e : B)
    (hrel : (v : B) ^ 2 + (t : B) * (c * (q : B) + d * (v : B) + e * (t : B)) = 0) :
    MvPolynomial.doubleLineChildQuadratic (residue B c) (residue B d) (residue B e) ∈
      doubleLineChildCotangentKernel B ![q, v, t] := by
  let I := maximalIdeal B
  let F : MvPolynomial (Fin 3) (ResidueField B) →+* I.associatedGraded :=
    (Ideal.cotangentPolynomialMap I ![q, v, t]).toRingHom
  let τ := reesAlgebra.degreeOne I t
  let V := reesAlgebra.degreeOne I v
  let Q := reesAlgebra.degreeOne I q
  have hFQ : F (MvPolynomial.X 0) = Ideal.Quotient.mk I.associatedGradedIdeal Q :=
    Ideal.cotangentPolynomialMap_X I ![q, v, t] 0
  have hFV : F (MvPolynomial.X 1) = Ideal.Quotient.mk I.associatedGradedIdeal V :=
    Ideal.cotangentPolynomialMap_X I ![q, v, t] 1
  have hFT : F (MvPolynomial.X 2) = Ideal.Quotient.mk I.associatedGradedIdeal τ :=
    Ideal.cotangentPolynomialMap_X I ![q, v, t] 2
  have hFC (a : B) : F (MvPolynomial.C (residue B a)) =
      Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap B (reesAlgebra I) a) :=
    Ideal.cotangentPolynomialMap_C_mk I ![q, v, t] a
  have hrees : V ^ 2 + τ *
      (algebraMap B (reesAlgebra I) c * Q + algebraMap B (reesAlgebra I) d * V +
        algebraMap B (reesAlgebra I) e * τ) = 0 := by
    apply Subtype.ext
    change Polynomial.monomial 1 (v : B) ^ 2 + Polynomial.monomial 1 (t : B) *
      (Polynomial.C c * Polynomial.monomial 1 (q : B) +
        Polynomial.C d * Polynomial.monomial 1 (v : B) +
          Polynomial.C e * Polynomial.monomial 1 (t : B)) = 0
    have he : Polynomial.monomial 1 (v : B) ^ 2 + Polynomial.monomial 1 (t : B) *
        (Polynomial.C c * Polynomial.monomial 1 (q : B) +
          Polynomial.C d * Polynomial.monomial 1 (v : B) +
            Polynomial.C e * Polynomial.monomial 1 (t : B)) =
        Polynomial.monomial 2
          ((v : B) ^ 2 + (t : B) * (c * (q : B) + d * (v : B) + e * (t : B))) := by
      simp only [Polynomial.C_mul_monomial, mul_add,
        Polynomial.monomial_mul_monomial, Polynomial.monomial_pow,
        one_mul, ← map_add]
    rw [he, hrel, map_zero]
  have hmap := congrArg (Ideal.Quotient.mk I.associatedGradedIdeal) hrees
  change F
    (MvPolynomial.doubleLineChildQuadratic (residue B c) (residue B d) (residue B e)) = 0
  simp only [MvPolynomial.doubleLineChildQuadratic, F.map_add, F.map_mul, F.map_pow,
    hFQ, hFV, hFT, hFC]
  simpa only [map_add, map_mul, map_pow, map_zero] using hmap

/-- The actual Case-II kernel forces the local cofactor to have zero residue.
This is the missing obstruction to a simple prime factor. -/
theorem cofactor_mem_maximal_of_doubleLineChild
    (t v q : maximalIdeal B) (c d e : B)
    (hrel : (v : B) ^ 2 + (t : B) * (c * (q : B) + d * (v : B) + e * (t : B)) = 0)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField B)) (hL : L.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel B ![q, v, t] =
      Ideal.span {L ^ 2}) : c ∈ maximalIdeal B := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply MvPolynomial.doubleLineChildQuadratic_coefficient_eq_zero
    (residue B c) (residue B d) (residue B e) L hL
  rw [← hker]
  exact doubleLineChildQuadratic_mem_cotangent_kernel t v q c d e hrel

end IsLocalRing

namespace Ideal

variable {k S : Type u} [Field k] [CommRing S]

/-- The actual reduced exceptional quotient gives the displayed generators of
the prime, using a lift of its prime polynomial rather than a derivative. -/
theorem reduced_doubleLine_child_prime_eq_span
    (red : S →+* k[X]) (hred : Function.Surjective red)
    (t v Q : S) (q : k[X])
    (hker : RingHom.ker red = Ideal.span ({t, v} : Set S)) (hQ : red Q = q) :
    (Ideal.span {q}).comap red = Ideal.span ({t, v, Q} : Set S) := by
  have hmap : (Ideal.span ({Q} : Set S)).map red = Ideal.span {q} := by
    rw [Ideal.map_span, Set.image_singleton, hQ]
  rw [← hmap, Ideal.comap_map_of_surjective' red hred, hker]
  simp only [Ideal.span_insert]
  ac_rfl

private theorem sq_dvd_of_doubleLine_localization
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (red : S →+* k[X]) (hred : Function.Surjective red)
    (t v Q H l r : S) (q h : k[X])
    (hredker : RingHom.ker red = Ideal.span ({t, v} : Set S))
    (hQ : red Q = q) (hH : red H = h)
    (hrel : v ^ 2 + t * H + t * v * l + t ^ 2 * r = 0)
    (P : Ideal S) (hP : P = (Ideal.span {q}).comap red)
    (loc : S →+* B) (hmap : P.map loc = maximalIdeal B)
    (hmem : ∀ x : S, loc x ∈ maximalIdeal B ↔ x ∈ P)
    (hd : ringKrullDim B = 2) (hsing : ¬ IsRegularLocalRing B)
    (g : Fin 3 → maximalIdeal B)
    (hgQ : (g 0 : B) = loc Q) (hgv : (g 1 : B) = loc v) (hgt : (g 2 : B) = loc t)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField B)) (hL : L.IsHomogeneous 1)
    (hCaseII : IsLocalRing.doubleLineChildCotangentKernel B g = Ideal.span {L ^ 2}) :
    q ^ 2 ∣ h := by
  have hPgen : P = Ideal.span ({t, v, Q} : Set S) :=
    hP.trans (reduced_doubleLine_child_prime_eq_span red hred t v Q q hredker hQ)
  have hgen : maximalIdeal B =
      Ideal.span ({(g 2 : B), (g 1 : B), (g 0 : B)} : Set B) := by
    have hm := congrArg (Ideal.map loc) hPgen
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at hm
    rw [hgt, hgv, hgQ]
    exact hmap.symm.trans hm
  have hrelB : (g 1 : B) ^ 2 + (g 2 : B) * loc H +
      (g 2 : B) * (g 1 : B) * loc l + (g 2 : B) ^ 2 * loc r = 0 := by
    simpa only [hgt, hgv, map_add, map_mul, map_pow, map_zero] using congrArg loc hrel
  have hHm : loc H ∈ maximalIdeal B :=
    IsLocalRing.cubic_coefficient_mem_maximal_of_singular_chart B
      (g 2 : B) (g 1 : B) (g 0 : B) (loc H) (loc l) (loc r) hgen hd hsing hrelB
  have hHP : H ∈ P := (hmem H).mp hHm
  have hqh : q ∣ h := by
    apply Ideal.mem_span_singleton.mp
    rw [hP] at hHP
    simpa only [Ideal.mem_comap, hH] using hHP
  obtain ⟨r₀, hr₀⟩ := hqh
  obtain ⟨R, hR⟩ := hred r₀
  have hdiff : H - Q * R ∈ Ideal.span ({t, v} : Set S) := by
    rw [← hredker]
    change red (H - Q * R) = 0
    rw [map_sub, map_mul, hH, hQ, hR, hr₀, sub_self]
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hdiff
  have hquad : v ^ 2 + t * (R * Q + (l + b) * v + (r + a) * t) = 0 := by
    linear_combination hrel + t * hab
  have hquadB : (g 1 : B) ^ 2 + (g 2 : B) *
      (loc R * (g 0 : B) + loc (l + b) * (g 1 : B) + loc (r + a) * (g 2 : B)) = 0 := by
    simpa only [hgQ, hgt, hgv, map_add, map_mul, map_pow, map_zero] using congrArg loc hquad
  have hg : ![g 0, g 1, g 2] = g := by
    funext i
    fin_cases i <;> rfl
  have hRm : loc R ∈ maximalIdeal B :=
    IsLocalRing.cofactor_mem_maximal_of_doubleLineChild (g 2) (g 1) (g 0)
      (loc R) (loc (l + b)) (loc (r + a)) hquadB L hL (by rw [hg]; exact hCaseII)
  have hRP : R ∈ P := (hmem R).mp hRm
  have hqr : q ∣ r₀ := by
    apply Ideal.mem_span_singleton.mp
    rw [hP] at hRP
    simpa only [Ideal.mem_comap, hR] using hRP
  obtain ⟨r₁, hr₁⟩ := hqr
  refine ⟨r₁, ?_⟩
  rw [hr₀, hr₁, pow_two, mul_assoc]

variable [IsNoetherianRing S]

/-- At an actual localized child with the Case-II cotangent kernel, its prime
polynomial divides the original cubic twice. A factor is lifted through the
actual reduced exceptional quotient, so inseparability causes no exception. -/
theorem sq_dvd_of_actual_doubleLine_child
    (red : S →+* k[X]) (hred : Function.Surjective red)
    (t v Q H l r : S) (q h : k[X])
    (hredker : RingHom.ker red = Ideal.span ({t, v} : Set S))
    (hQ : red Q = q) (hH : red H = h)
    (hrel : v ^ 2 + t * H + t * v * l + t ^ 2 * r = 0)
    (P : Ideal S) [P.IsPrime] (hP : P = (Ideal.span {q}).comap red)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (g : Fin 3 → maximalIdeal (Localization.AtPrime P))
    (hgQ : (g 0 : Localization.AtPrime P) = algebraMap S (Localization.AtPrime P) Q)
    (hgv : (g 1 : Localization.AtPrime P) = algebraMap S (Localization.AtPrime P) v)
    (hgt : (g 2 : Localization.AtPrime P) = algebraMap S (Localization.AtPrime P) t)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : IsLocalRing.doubleLineChildCotangentKernel (Localization.AtPrime P) g =
        Ideal.span {L ^ 2}) : q ^ 2 ∣ h := by
  let B : Type u := Localization.AtPrime P
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  exact sq_dvd_of_doubleLine_localization (B := B) red hred t v Q H l r q h
    hredker hQ hH hrel P hP (algebraMap S B)
    (IsLocalization.AtPrime.map_eq_maximalIdeal P B)
    (fun x => IsLocalization.AtPrime.to_map_mem_maximal_iff B P x)
    hd hsing g hgQ hgv hgt L hL hCaseII

end Ideal

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The reduced coordinate map of the literal double line. -/
def doubleLineReduction :
    R[X] ⧸ Ideal.span ({X ^ 2} : Set R[X]) →+* R :=
  Ideal.Quotient.lift _ Polynomial.constantCoeff (by
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp)

@[simp] theorem doubleLineReduction_mk (p : R[X]) :
    doubleLineReduction (Ideal.Quotient.mk (Ideal.span ({X ^ 2} : Set R[X])) p) =
      p.coeff 0 := rfl

/-- Reduction is surjective through the original constant polynomials. -/
theorem doubleLineReduction_surjective : Function.Surjective (doubleLineReduction (R := R)) := by
  intro a
  exact ⟨Ideal.Quotient.mk _ (C a), by simp⟩

/-- Its kernel is exactly the original nilpotent coordinate. -/
theorem ker_doubleLineReduction :
    RingHom.ker (doubleLineReduction (R := R)) = Ideal.span {doubleLineCoordinate (R := R)} := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change p.coeff 0 = 0 ↔ Ideal.Quotient.mk _ p ∈ Ideal.span {doubleLineCoordinate (R := R)}
  constructor
  · intro hp
    have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span ({X ^ 2} : Set R[X])))
      (Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr hp))
    simpa only [Ideal.map_span, Set.image_singleton, doubleLineCoordinate] using hm
  · intro hp
    have hle : Ideal.span {doubleLineCoordinate (R := R)} ≤
        RingHom.ker (doubleLineReduction (R := R)) := by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = doubleLineCoordinate (R := R))
      change (X : R[X]).coeff 0 = 0
      simp
    exact hle hp

end Polynomial

namespace Ideal

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Reduction of the actual double-line quotient has the actual kernel `(t,v)`. -/
theorem ker_reduced_doubleLine_quotient
    (t v : S) (φ : S →+* R[X] ⧸ Ideal.span ({X ^ 2} : Set R[X]))
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span ({t} : Set S))
    (hv : φ v = Polynomial.doubleLineCoordinate (R := R)) :
    RingHom.ker (Polynomial.doubleLineReduction.comp φ) = Ideal.span ({t, v} : Set S) := by
  change (RingHom.ker Polynomial.doubleLineReduction).comap φ = _
  rw [Polynomial.ker_doubleLineReduction]
  exact doubleLine_comap_span φ hφ hker hv

end Ideal

namespace HomogeneousLocalization.Away

variable {A D R : Type u} [CommRing A] [CommRing D] [CommRing R] [Algebra A D]

private theorem quotientConeEquiv_dehomogenize
    (J : Ideal D) (G : ℕ → Submodule A (D ⧸ J)) [GradedAlgebra G]
    {f : D ⧸ J} (hf : f ∈ G 1) (x : R)
    (E : (D ⧸ J) ≃+* Polynomial.quotientCone x)
    (hE : E.toRingHom f = Polynomial.quotientConeParameter x)
    (y : D ⧸ J) (p : R[X]) (hy : E.toRingHom y = Polynomial.quotientConeMk x p) :
    (quotientConeEquiv J G hf x E hE).toRingHom (dehomogenize G hf y) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  let e := quotientConeQuotientEquiv J x E hE
  change e.toRingHom (toQuotient G (dehomogenize G hf y)) = _
  exact (congrArg e.toRingHom (toQuotient_dehomogenize G hf y)).trans
    (quotientConeQuotientEquiv_mk J x E hE y p hy)

end HomogeneousLocalization.Away

namespace reesAlgebra

variable {A R : Type u} [CommRing A] [CommRing R]

/-- The original cone presentation retains the coefficient formula after
dehomogenization, as well as the degree-one numerator formulas. -/
theorem exceptionalQuotientConeEquiv_mk_base
    (I : Ideal A) (a : I) (x : R)
    (E : I.associatedGraded ≃+* Polynomial.quotientCone x)
    (ha : E.toRingHom (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I a)) =
      Polynomial.quotientConeParameter x)
    (r : A) (p : R[X])
    (hr : E.toRingHom (Ideal.Quotient.mk I.associatedGradedIdeal
        (algebraMap A (reesAlgebra I) r)) = Polynomial.quotientConeMk x p) :
    (exceptionalQuotientConeEquiv I a x E ha).toRingHom
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (algebraMap A (Localization.Away.saturatedChart A I (a : A)) r)) =
      Ideal.Quotient.mk (Ideal.span {x}) (p.eval 1) := by
  let e := HomogeneousLocalization.Away.quotientConeEquiv (D := reesAlgebra I)
    I.associatedGradedIdeal I.associatedGradedGrading
    (degreeOne_associatedGraded_mem I a) x E ha
  have hbase : (exceptionalChartEquiv I a).toRingHom
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (algebraMap A (Localization.Away.saturatedChart A I (a : A)) r)) =
      HomogeneousLocalization.Away.dehomogenize I.associatedGradedGrading
        (degreeOne_associatedGraded_mem I a)
        (Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap A (reesAlgebra I) r)) := by
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      exceptionalChartEquiv_mk_base I a r
  change e.toRingHom ((exceptionalChartEquiv I a).toRingHom
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (algebraMap A (Localization.Away.saturatedChart A I (a : A)) r))) = _
  exact (congrArg e.toRingHom hbase).trans
    (HomogeneousLocalization.Away.quotientConeEquiv_dehomogenize (D := reesAlgebra I)
      I.associatedGradedIdeal I.associatedGradedGrading
      (degreeOne_associatedGraded_mem I a) x E ha _ p hr)

variable [IsLocalRing A]

/-- The reduced exceptional map of the literal saturated chart, constructed
from its original associated-graded presentation and the native Rees comparison. -/
def reducedDoubleLineChartMap
    (t : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2)) :
    Localization.Away.saturatedChart A (maximalIdeal A) (t : A) →+* (ResidueField A)[X] :=
  Polynomial.doubleLineReduction.comp
    ((exceptionalQuotientConeEquiv (maximalIdeal A) t
      ((X : (ResidueField A)[X][X]) ^ 2) E hEt).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.span
          {algebraMap A (Localization.Away.saturatedChart A (maximalIdeal A) (t : A)) (t : A)})))

/-- The native exceptional quotient and reduction are both surjective. -/
theorem reducedDoubleLineChartMap_surjective
    (t : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2)) :
    Function.Surjective (reducedDoubleLineChartMap t E hEt) :=
  Polynomial.doubleLineReduction_surjective.comp
    ((exceptionalQuotientConeEquiv (maximalIdeal A) t
      ((X : (ResidueField A)[X][X]) ^ 2) E hEt).surjective.comp Ideal.Quotient.mk_surjective)

/-- The kernel is the actual exceptional parameter and actual fraction `z/t`. -/
theorem ker_reducedDoubleLineChartMap
    (t z : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2))
    (hEz : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) z)) =
      Polynomial.quotientConeMk ((X : (ResidueField A)[X][X]) ^ 2)
        (C (X : (ResidueField A)[X][X]))) :
    RingHom.ker (reducedDoubleLineChartMap t E hEt) = Ideal.span
      ({algebraMap A (Localization.Away.saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        Localization.Away.SaturatedChart.fractionElement (maximalIdeal A) t z} :
          Set (Localization.Away.saturatedChart A (maximalIdeal A) (t : A))) := by
  let S : Type u := Localization.Away.saturatedChart A (maximalIdeal A) (t : A)
  let τ := algebraMap A S (t : A)
  let V := Localization.Away.SaturatedChart.fractionElement (maximalIdeal A) t z
  let e := exceptionalQuotientConeEquiv (maximalIdeal A) t
    ((X : (ResidueField A)[X][X]) ^ 2) E hEt
  let φ := e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {τ}))
  have hker : RingHom.ker φ = Ideal.span {τ} := by
    ext x
    change e (Ideal.Quotient.mk (Ideal.span {τ}) x) = 0 ↔ x ∈ Ideal.span {τ}
    rw [← e.map_zero, e.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hV : φ V = Polynomial.doubleLineCoordinate (R := (ResidueField A)[X]) := by
    simpa only [φ, e, τ, V, RingHom.comp_apply, Polynomial.doubleLineCoordinate, eval_C] using
      exceptionalQuotientConeEquiv_mk_fraction (maximalIdeal A) t
        ((X : (ResidueField A)[X][X]) ^ 2) E hEt z (C (X : (ResidueField A)[X][X])) hEz
  exact Ideal.ker_reduced_doubleLine_quotient τ V φ
    (e.surjective.comp Ideal.Quotient.mk_surjective) hker hV

/-- The other actual fraction is the original polynomial coordinate `U`. -/
theorem reducedDoubleLineChartMap_fraction
    (t s : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2))
    (hEs : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) s)) =
      Polynomial.quotientConeMk ((X : (ResidueField A)[X][X]) ^ 2)
        (C (C (X : (ResidueField A)[X])))) :
    reducedDoubleLineChartMap t E hEt
      (Localization.Away.SaturatedChart.fractionElement (maximalIdeal A) t s) = X := by
  unfold reducedDoubleLineChartMap
  rw [RingHom.comp_apply, RingHom.comp_apply,
    exceptionalQuotientConeEquiv_mk_fraction (maximalIdeal A) t
      ((X : (ResidueField A)[X][X]) ^ 2) E hEt s (C (C (X : (ResidueField A)[X]))) hEs]
  simp

/-- Every original coefficient reduces by the original residue map. -/
theorem reducedDoubleLineChartMap_base
    (t : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (ResidueField A)[X][X]) ^ 2))
    (hEt : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (degreeOne (maximalIdeal A) t)) =
      Polynomial.quotientConeParameter ((X : (ResidueField A)[X][X]) ^ 2))
    (r : A)
    (hEr : E.toRingHom (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (algebraMap A (reesAlgebra (maximalIdeal A)) r)) =
      Polynomial.quotientConeMk ((X : (ResidueField A)[X][X]) ^ 2)
        (C (C (C (residue A r))))) :
    reducedDoubleLineChartMap t E hEt
      (algebraMap A (Localization.Away.saturatedChart A (maximalIdeal A) (t : A)) r) =
        C (residue A r) := by
  unfold reducedDoubleLineChartMap
  rw [RingHom.comp_apply, RingHom.comp_apply,
    exceptionalQuotientConeEquiv_mk_base (maximalIdeal A) t
      ((X : (ResidueField A)[X][X]) ^ 2) E hEt r (C (C (C (residue A r)))) hEr]
  simp

end reesAlgebra

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The actual Case-II child is a repeated divisor of the original residue
cubic. The relation is divided in the literal saturated chart, and the child
kernel is the canonical cotangent map on the actual localized coordinates. -/
theorem original_cubic_sq_dvd_of_caseII_child
    (t s z : maximalIdeal A)
    (red : saturatedChart A (maximalIdeal A) (t : A) →+* (ResidueField A)[X])
    (hred : Function.Surjective red)
    (hredker : RingHom.ker red = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))))
    (hredU : red (fractionElement (maximalIdeal A) t s) = X)
    (hredbase : ∀ a : A, red (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a) =
      C (residue A a))
    (Q : saturatedChart A (maximalIdeal A) (t : A)) (q : (ResidueField A)[X])
    (hQ : red Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap red)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (g : Fin 3 → maximalIdeal (Localization.AtPrime P))
    (hgQ : (g 0 : Localization.AtPrime P) =
      algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P) Q)
    (hgv : (g 1 : Localization.AtPrime P) =
      algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P)
        (fractionElement (maximalIdeal A) t z))
    (hgt : (g 2 : Localization.AtPrime P) =
      localizedChartMap (maximalIdeal A) (t : A) P (t : A))
    (L : MvPolynomial (Fin 3) (ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : IsLocalRing.doubleLineChildCotangentKernel (Localization.AtPrime P) g =
        Ideal.span {L ^ 2})
    (a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 : A)
    (hrel : (z : A) ^ 2 +
      (a0 * (t : A) ^ 3 + a1 * (t : A) ^ 2 * (s : A) +
        a2 * (t : A) * (s : A) ^ 2 + a3 * (s : A) ^ 3) +
      (z : A) * (b0 * (t : A) ^ 2 + b1 * (t : A) * (s : A) + b2 * (s : A) ^ 2) +
      (z : A) ^ 2 * (c0 * (t : A) + c1 * (s : A)) + d0 * (z : A) ^ 3 = 0) :
    q ^ 2 ∣ IsLocalRing.residueBinaryCubic a0 a1 a2 a3 := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let φ : A →+* S := algebraMap A S
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  let H := φ a0 + φ a1 * U + φ a2 * U ^ 2 + φ a3 * U ^ 3
  let l := φ b0 + φ b1 * U + φ b2 * U ^ 2 + φ c0 * V + φ c1 * U * V + φ d0 * V ^ 2
  obtain ⟨r, hr⟩ := exists_divided_cubic_relation t s z
    a0 a1 a2 a3 b0 b1 b2 c0 c1 d0 0 (Ideal.zero_mem _)
    (by simpa only [add_zero] using hrel)
  have hφ (a : A) : red (φ a) = C (residue A a) := hredbase a
  have hU : red U = X := hredU
  have hH : red H = IsLocalRing.residueBinaryCubic a0 a1 a2 a3 := by
    dsimp only [H]
    simp only [map_add, map_mul, map_pow, hφ, hU, IsLocalRing.residueBinaryCubic]
    ring
  exact Ideal.sq_dvd_of_actual_doubleLine_child red hred τ V Q H l r q
    (IsLocalRing.residueBinaryCubic a0 a1 a2 a3) hredker hQ hH hr
    P hP hd hsing g hgQ hgv hgt L hL hCaseII

end Localization.Away.SaturatedChart

namespace Localization.Away

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- An equality with the actual rational-point kernel identifies the original
local coefficient map and its residue map, including an arbitrarily named prime. -/
theorem localizedChartMap_residue_bijective_of_point_kernel
    (I : Ideal A) (a : A) (P : Ideal (saturatedChart A I a)) [P.IsPrime]
    (φ : saturatedChart A I a →+* ResidueField A)
    (hφ : φ.comp (algebraMap A (saturatedChart A I a)) = residue A)
    (hP : P = RingHom.ker φ) :
    ∃ hlocal : IsLocalHom (localizedChartMap I a P),
      let _ := hlocal
      Function.Bijective (ResidueField.map (R := A) (S := Localization.AtPrime P)
        (localizedChartMap I a P)) := by
  subst P
  refine ⟨localizedChartMap_isLocal_of_residue_point I a φ hφ, ?_⟩
  exact localizedChartMap_residue_bijective I a φ hφ

/-- For the repeated divisor produced by the child theorem, degree three forces
a point over the original field, and the original residue map is bijective. -/
theorem original_child_prime_and_residue_of_sq_dvd
    (t : maximalIdeal A)
    (red : saturatedChart A (maximalIdeal A) (t : A) →+* (ResidueField A)[X])
    (hredbase : ∀ a : A, red (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a) =
      C (residue A a))
    (q h : (ResidueField A)[X]) (hq : Irreducible q) (hm : q.Monic)
    (hh : h ≠ 0) (hdeg : h.natDegree ≤ 3) (hsq : q ^ 2 ∣ h)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap red) :
    q.natDegree = 1 ∧ ∃ α : ResidueField A,
      q = X - C α ∧
      P = RingHom.ker ((Polynomial.evalRingHom α).comp red) ∧
      ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
        let _ := hlocal
        Function.Bijective (ResidueField.map (R := A) (S := Localization.AtPrime P)
          (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  refine ⟨Polynomial.natDegree_eq_one_of_irreducible_sq_dvd_cubic hh hdeg hq hsq, ?_⟩
  obtain ⟨α, hα⟩ := Polynomial.exists_eq_X_sub_C_of_monic_irreducible_sq_dvd_cubic
    hh hdeg hq hm hsq
  let φ := (Polynomial.evalRingHom α).comp red
  have hφ : φ.comp (algebraMap A (saturatedChart A (maximalIdeal A) (t : A))) = residue A := by
    apply RingHom.ext
    intro a
    change (red (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a)).eval α = residue A a
    rw [hredbase, eval_C]
  have hker : P = RingHom.ker φ := by
    rw [hP, hα, ← Polynomial.ker_evalRingHom]
    rfl
  exact ⟨α, hα, hker,
    localizedChartMap_residue_bijective_of_point_kernel (maximalIdeal A) (t : A) P φ hφ hker⟩

/-- A lift of the proved rational root gives the same actual prime in the
displayed coordinates used by the marked-chart parameter theorem. -/
theorem original_child_prime_eq_displayed_span
    (t s z : maximalIdeal A)
    (red : saturatedChart A (maximalIdeal A) (t : A) →+* (ResidueField A)[X])
    (hred : Function.Surjective red)
    (hredker : RingHom.ker red = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        SaturatedChart.fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))))
    (hredU : red (SaturatedChart.fractionElement (maximalIdeal A) t s) = X)
    (hredbase : ∀ a : A, red (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a) =
      C (residue A a))
    (q : (ResidueField A)[X]) (α : A) (hq : q = X - C (residue A α))
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A)))
    (hP : P = (Ideal.span {q}).comap red) :
    P = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        SaturatedChart.fractionElement (maximalIdeal A) t s -
          algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) α,
        SaturatedChart.fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let τ := algebraMap A S (t : A)
  let V := SaturatedChart.fractionElement (maximalIdeal A) t z
  let Q := SaturatedChart.fractionElement (maximalIdeal A) t s - algebraMap A S α
  have hQ : red Q = q := by
    dsimp only [Q]
    rw [map_sub, hredU, hredbase, hq]
  have hgen : P = Ideal.span ({τ, V, Q} : Set S) :=
    hP.trans (Ideal.reduced_doubleLine_child_prime_eq_span red hred τ V Q q hredker hQ)
  change P = Ideal.span ({τ, Q, V} : Set S)
  refine hgen.trans ?_
  simp only [Ideal.span_insert]
  exact congrArg (fun J : Ideal S => Ideal.span ({τ} : Set S) ⊔ J) (sup_comm _ _)

end Localization.Away
