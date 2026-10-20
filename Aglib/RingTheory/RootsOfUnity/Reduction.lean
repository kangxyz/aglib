/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois

/-!
# Power reduction of actual roots of unity

The power map between product levels, its Galois equivariance, and its
composition law use the actual root groups at every natural level.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.Reduction
open Field.absoluteGaloisGroup.RootsOfUnity
universe u
variable (K : Type u) [Field K] (d e : ℕ)

/-- The actual power map `μ_(d*e) → μ_d`. -/
def rootsReduction : rootsOfUnity (d * e) (AlgebraicClosure K) →*
    rootsOfUnity d (AlgebraicClosure K) where
  toFun x := ⟨(x : (AlgebraicClosure K)ˣ) ^ e, by
    rw [mem_rootsOfUnity, ← pow_mul, Nat.mul_comm e d]
    exact (mem_rootsOfUnity _ _).mp x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_pow]

/-- Additive linear form of the power map on roots of unity. -/
def muReduction : Mu K (d * e) →ₗ[ℤ] Mu K d :=
  (rootsReduction K d e).toAdditive.toIntLinearMap

@[simp] theorem muReduction_value (x : Mu K (d * e)) :
    ((muReduction K d e x).toMul : (AlgebraicClosure K)ˣ) =
      (x.toMul : (AlgebraicClosure K)ˣ) ^ e := rfl

/-- Power maps commute with every actual absolute-Galois automorphism. -/
theorem muReduction_smul (g : Field.absoluteGaloisGroup K) (x : Mu K (d * e)) :
    muReduction K d e (g • x) = g • muReduction K d e x := by
  ext
  change ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
    ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ e =
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      (((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ e)
  exact (map_pow (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) _ e).symm


/-- Transport between literally equal root levels. This map only reindexes a type. -/
def muCast {a b : ℕ} (h : a = b) : Mu K a →ₗ[ℤ] Mu K b := by
  subst b
  exact LinearMap.id

@[simp] theorem muCast_value {a b : ℕ} (h : a = b) (x : Mu K a) :
    ((muCast K h x).toMul : (AlgebraicClosure K)ˣ) =
      (x.toMul : (AlgebraicClosure K)ˣ) := by
  subst b
  rfl


/-- At ratio one, the power map is just transport of `d * 1 = d`. -/
theorem muReduction_one : muReduction K d 1 = muCast K (Nat.mul_one d) := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [muReduction_value, muCast_value, pow_one]

/-- Composing power reductions multiplies their ratios. -/
theorem muReduction_comp (f : ℕ) :
    (muReduction K d e).comp (muReduction K (d * e) f) =
      (muReduction K d (e * f)).comp (muCast K (Nat.mul_assoc d e f)) := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [LinearMap.comp_apply, muReduction_value, muCast_value, ← pow_mul,
    Nat.mul_comm f e]

end Field.absoluteGaloisGroup.RootsOfUnity.Reduction
