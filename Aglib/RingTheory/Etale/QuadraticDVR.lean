/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Quadratic finite étale polynomial algebras and their local DVRs

Qualified declaration names and the stated theorem premises are retained from
the original unramified-descent source. This object module supplies the
corresponding construction; library placement adds no mathematical conclusion.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/QuadraticDVR.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e2c209e1eeb97dda5c30874dcce1edc3b6dbf15d723050eda68cd86fc146a146`.
-/

@[expose] public section

universe u

/- F3 source: QuadraticEtale.lean; SHA256
2073e6d0c097636172f4fc67d0251ac27f4cdb79c7cded6c3425a98b63a001c2. -/
section F3_QuadraticEtale

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace Algebra.QuadraticEtale
variable {R : Type u} [CommRing R]

/-- The monic quadratic polynomial `X² + aX - b`. -/
def polynomial (a b : R) : R[X] := X ^ 2 + C a * X - C b
/-- The algebra obtained by adjoining a root of `X² + aX - b`. -/
abbrev Quadratic (a b : R) := AdjoinRoot (polynomial a b)
/-- The universal root of `X² + aX - b` in its quotient algebra. -/
abbrev root (a b : R) : Quadratic a b := AdjoinRoot.root (polynomial a b)

lemma polynomial_monic (a b : R) : (polynomial a b).Monic := by
  simpa [polynomial, sub_eq_add_neg, add_assoc] using
    (monic_X_pow_add (p := C a * X + C (-b)) (n := 2) (by compute_degree; norm_num))

lemma polynomial_natDegree [Nontrivial R] (a b : R) : (polynomial a b).natDegree = 2 := by
  unfold polynomial
  compute_degree <;> norm_num

lemma polynomial_derivative (a b : R) : (polynomial a b).derivative = 2 * X + C a := by
  simp [polynomial, derivative_sub, derivative_add, derivative_mul, derivative_pow, map_ofNat]

lemma root_relation (a b : R) :
    root a b ^ 2 + algebraMap R _ a * root a b - algebraMap R _ b = 0 := by
  have h := AdjoinRoot.eval₂_root (polynomial a b)
  change (X ^ 2 + C a * X - C b).eval₂ (algebraMap R (Quadratic a b)) (root a b) = 0 at h
  simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using h

lemma derivative_square (a b : R) :
    (2 * root a b + algebraMap R _ a) ^ 2 = algebraMap R _ (a ^ 2 + 4 * b) := by
  simp only [map_add, map_mul, map_pow, map_ofNat]
  linear_combination 4 * root_relation a b

lemma derivative_isUnit (a b : R) (h : IsUnit (a ^ 2 + 4 * b)) :
    IsUnit (2 * root a b + algebraMap R _ a) := by
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [derivative_square]
  exact h.map (algebraMap R _)

/-- The standard étale presentation uses no inverse of 2. -/
def standardPair (a b : R) (h : IsUnit (a ^ 2 + 4 * b)) : StandardEtalePair R where
  f := polynomial a b
  monic_f := polynomial_monic a b
  g := 1
  cond := by
    refine ⟨(2 * X + C a) * C (↑h.unit⁻¹ : R), C (-4 * (↑h.unit⁻¹ : R)), 0, ?_⟩
    have hi : (a ^ 2 + 4 * b) * (↑h.unit⁻¹ : R) = 1 := by
      simpa only [h.unit_spec] using h.unit.mul_inv
    rw [polynomial_derivative]
    calc
      _ = C ((a ^ 2 + 4 * b) * (↑h.unit⁻¹ : R)) := by
        simp only [polynomial, map_add, map_mul, map_pow, map_neg, map_ofNat]
        ring
      _ = _ := by rw [hi]; simp

/-- The algebra equivalence from the standard-étale presentation to the quadratic quotient when
`a² + 4b` is a unit. -/
def standardEquiv (a b : R) (h : IsUnit (a ^ 2 + 4 * b)) :
    (standardPair a b h).Ring ≃ₐ[R] Quadratic a b := by
  let P := standardPair a b h
  let f := P.lift (root a b)
    ⟨by simp [P, standardPair, AdjoinRoot.aeval_eq],
      by simp [P, standardPair]⟩
  let g : Quadratic a b →ₐ[R] P.Ring := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) P.X P.hasMap_X.1
  have hf : f P.X = root a b := P.lift_X _ _
  have hg : g (root a b) = P.X := AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change f (g (root a b)) = root a b
    rw [hg, hf]
  · apply P.hom_ext
    change g (f P.X) = P.X
    rw [hf, hg]

lemma quadratic_etale (a b : R) (h : IsUnit (a ^ 2 + 4 * b)) :
    Algebra.Etale R (Quadratic a b) := Algebra.Etale.of_equiv (standardEquiv a b h)

lemma quadratic_free (a b : R) : Module.Free R (Quadratic a b) :=
  (polynomial_monic a b).free_adjoinRoot
lemma quadratic_finite (a b : R) : Module.Finite R (Quadratic a b) :=
  (polynomial_monic a b).finite_adjoinRoot

end Algebra.QuadraticEtale

end -- closes the source module's noncomputable section
end F3_QuadraticEtale

/- F3 source: QuadraticDVR.lean; SHA256
0ada2f9820b8b5a5f49f4dcc1b8238635b09b3d5bbda84ed57191f9b247f58fb. -/
section F3_QuadraticDVR

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsLocalRing
namespace Algebra.QuadraticEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (a b : R) (hirr : Irreducible ((polynomial a b).map (residue R)))

include hirr

lemma polynomial_irreducible : Irreducible (polynomial a b) :=
  (polynomial_monic a b).irreducible_of_irreducible_map (residue R) _ hirr

lemma quadratic_domain : IsDomain (Quadratic a b) :=
  AdjoinRoot.isDomain_of_prime (polynomial_irreducible a b hirr).prime

lemma quadratic_closedFiber_field :
    IsField (Quadratic a b ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R (Quadratic a b))) := by
  let : Fact (Irreducible ((polynomial a b).map (residue R))) := ⟨hirr⟩
  let e : (Quadratic a b ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R (Quadratic a b))) ≃+*
      AdjoinRoot ((polynomial a b).map (residue R)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (IsLocalRing.maximalIdeal R) (polynomial a b)
  exact e.isField (Field.toIsField _)

lemma quadratic_local : IsLocalRing (Quadratic a b) := by
  let : Module.Finite R (Quadratic a b) := quadratic_finite a b
  let m := (IsLocalRing.maximalIdeal R).map (algebraMap R (Quadratic a b))
  have hm : m.IsMaximal :=
    Ideal.Quotient.maximal_of_isField m (quadratic_closedFiber_field a b hirr)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, ?_⟩
  intro n hn
  let := hn
  have hc : n.comap (algebraMap R (Quadratic a b)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal n)
  have hmle : m ≤ n := Ideal.map_le_iff_le_comap.mpr hc.symm.le
  exact (hm.eq_of_le hn.ne_top hmle).symm

lemma quadratic_dvr (hd : IsUnit (a ^ 2 + 4 * b)) :
    letI := quadratic_domain a b hirr
    IsDiscreteValuationRing (Quadratic a b) := by
  let := quadratic_domain a b hirr
  let := quadratic_local a b hirr
  let := quadratic_finite a b
  let := quadratic_etale a b hd
  let : IsDedekindDomain (Quadratic a b) := IsDedekindDomain.of_formallyUnramified R _
  have hinj : Function.Injective (algebraMap R (Quadratic a b)) := by
    exact AdjoinRoot.of.injective_of_monic_of_degree_pos (polynomial_monic a b) (by
      rw [Polynomial.degree_eq_natDegree (polynomial_monic a b).ne_zero, polynomial_natDegree]
      norm_num)
  have hnf : ¬ IsField (Quadratic a b) := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj h)
  exact ((IsDiscreteValuationRing.TFAE (Quadratic a b) hnf).out 3 1).mp
    (inferInstance : IsDedekindDomain (Quadratic a b))

end Algebra.QuadraticEtale

end -- closes the source module's noncomputable section
end F3_QuadraticDVR
