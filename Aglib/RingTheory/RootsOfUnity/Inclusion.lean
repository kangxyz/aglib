/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Reduction
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Inclusion and lifts between root levels

The literal inclusion of roots and the actual power reduction satisfy their
composition formulas. Surjectivity requires a positive reduction ratio.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.Inclusion
open Field.absoluteGaloisGroup.RootsOfUnity Field.absoluteGaloisGroup.RootsOfUnity.Reduction
universe u
variable (K : Type u) [Field K] (d e : ℕ)

/-- The actual inclusion of d-th roots among (d*e)-th roots. -/
def rootsInclusion : rootsOfUnity d (AlgebraicClosure K) →*
    rootsOfUnity (d * e) (AlgebraicClosure K) where
  toFun x := ⟨(x : (AlgebraicClosure K)ˣ), by
    rw [mem_rootsOfUnity, pow_mul, (mem_rootsOfUnity _ _).mp x.property, one_pow]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Additive linear form of the inclusion. -/
def muInclusion : Mu K d →ₗ[ℤ] Mu K (d * e) :=
  (rootsInclusion K d e).toAdditive.toIntLinearMap

@[simp]
theorem muInclusion_value (x : Mu K d) :
    ((muInclusion K d e x).toMul : (AlgebraicClosure K)ˣ) =
      (x.toMul : (AlgebraicClosure K)ˣ) := rfl

@[simp]
theorem muInclusion_muReduction (x : Mu K (d * e)) :
    muInclusion K d e (muReduction K d e x) = e • x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

@[simp]
theorem muReduction_muInclusion (x : Mu K d) :
    muReduction K d e (muInclusion K d e x) = e • x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- Inclusion commutes with every actual absolute-Galois automorphism. -/
theorem muInclusion_smul (g : Field.absoluteGaloisGroup K) (x : Mu K d) :
    muInclusion K d e (g • x) = g • muInclusion K d e x := by
  ext
  rfl

/-- The power reduction is surjective, by taking e-th roots in the algebraic closure. -/
theorem rootsReduction_surjective (he : 0 < e) :
    Function.Surjective (rootsReduction K d e) := by
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (((x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) he
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt he)] at hz
    exact Units.ne_zero (x : (AlgebraicClosure K)ˣ) hz.symm
  let a : (AlgebraicClosure K)ˣ := Units.mk0 z hz0
  have ha : a ^ e = (x : (AlgebraicClosure K)ˣ) := by
    apply Units.ext
    exact hz
  have har : a ∈ rootsOfUnity (d * e) (AlgebraicClosure K) := by
    rw [mem_rootsOfUnity, Nat.mul_comm d e, pow_mul, ha]
    exact (mem_rootsOfUnity _ _).mp x.property
  refine ⟨⟨a, har⟩, ?_⟩
  apply Subtype.ext
  exact ha

/-- Additive power reduction is surjective. -/
theorem muReduction_surjective (he : 0 < e) :
    Function.Surjective (muReduction K d e) := by
  intro x
  obtain ⟨a, ha⟩ := rootsReduction_surjective K d e he x.toMul
  exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩

/-- A temporary choice of a lift; the resulting tensor insertion is independent of it. -/
def rootLift (he : 0 < e) (x : Mu K d) : Mu K (d * e) :=
  (muReduction_surjective K d e he x).choose

@[simp]
theorem muReduction_rootLift (he : 0 < e) (x : Mu K d) :
    muReduction K d e (rootLift K d e he x) = x :=
  (muReduction_surjective K d e he x).choose_spec

/-- Multiplying a lift by e recovers the genuine inclusion. -/
theorem nsmul_rootLift (he : 0 < e) (x : Mu K d) :
    e • rootLift K d e he x = muInclusion K d e x := by
  rw [← muInclusion_muReduction, muReduction_rootLift]



/-- At ratio one, actual root inclusion is transport of the equal levels. -/
theorem muInclusion_one : muInclusion K d 1 = muCast K (Nat.mul_one d).symm := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [muInclusion_value, muCast_value]

end Field.absoluteGaloisGroup.RootsOfUnity.Inclusion
