/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Algebra.Group.TypeTags.Finite

/-! Actual roots of unity with their discrete continuous absolute-Galois action.
Source: generic roots-of-unity cuts of `R5Lab.KTheory.WeightTwo.Coefficients.Basic`;
its original K2-018 provenance and finite-level hypotheses are unchanged. -/
@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity
universe u
variable (K : Type u) [Field K] (n : ℕ)

/-- The additive group underlying the `n`th roots of unity. -/
abbrev Mu := Additive (rootsOfUnity n (AlgebraicClosure K))


/-- The action on roots of unity obtained by restricting a field automorphism. -/
def rootAction (g : Field.absoluteGaloisGroup K) : Mu K n →ₗ[ℤ] Mu K n :=
  (restrictRootsOfUnity (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
    n).toAdditive.toIntLinearMap

@[simp] theorem rootAction_one : rootAction K n 1 = LinearMap.id := by
  ext x
  rfl

@[simp] theorem rootAction_mul (g h : Field.absoluteGaloisGroup K) :
    rootAction K n (g * h) = (rootAction K n g).comp (rootAction K n h) := by
  ext x
  rfl

instance muDistribMulAction : DistribMulAction (Field.absoluteGaloisGroup K) (Mu K n) where
  smul g x := rootAction K n g x
  one_smul x := by
    change rootAction K n 1 x = x
    simp
  mul_smul g h x := by
    change rootAction K n (g * h) x = rootAction K n g (rootAction K n h x)
    simp
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _


/-- Every root of unity is annihilated by its level. -/
theorem mu_nsmul (x : Mu K n) : n • x = 0 := by
  apply Additive.toMul.injective
  change x.toMul ^ n = 1
  apply Subtype.ext
  exact (mem_rootsOfUnity _ _).mp x.toMul.property


instance muFinite [NeZero n] : Finite (Mu K n) := inferInstance


instance muTopology : TopologicalSpace (Mu K n) := ⊥
instance muDiscreteTopology : DiscreteTopology (Mu K n) := ⟨rfl⟩

/-- The restricted Galois action on roots of unity is continuous for the
Krull topology on the absolute Galois group and the discrete coefficient topology. -/
instance muContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup K) (Mu K n) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have hopen := stabilizer_isOpen_of_isIntegral (K := K)
    (((x.toMul : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
  have hset : (MulAction.stabilizer (Field.absoluteGaloisGroup K) x : Set (Field.absoluteGaloisGroup
    K)) =
      {g : Field.absoluteGaloisGroup K | (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)} := by
    ext g
    change (rootAction K n g x = x) ↔
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
        (((x.toMul : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K) =
        (((x.toMul : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)
    constructor
    · intro h
      exact congrArg (fun z : Mu K n => ((z.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) h
    · intro h
      ext
      exact h
  rw [hset]
  exact hopen

end Field.absoluteGaloisGroup.RootsOfUnity
