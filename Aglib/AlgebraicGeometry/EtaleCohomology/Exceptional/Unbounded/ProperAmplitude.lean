/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CohomologicalBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperFiniteDimension
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Amplitude

/-! # Actual finite amplitude of proper unbounded direct image

A proper morphism with quasi-compact target has a genuine uniform relative
bound. For a ring annihilated by a positive integer, every original module
sheaf is torsion, so the bound applies to all module coefficients. The actual
unbounded derived functor then has finite amplitude on native derived objects.
No coefficient invertibility or absolute dimension of the base is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The genuine proper relative bound is an all-object bound for module
coefficients over a ring killed by a positive integer. -/
theorem exists_moduleRightDerived_bound_of_proper
    [CompactSpace S] (f : X ⟶ S) [IsProper f]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    ∃ d : ℕ, ∀ M : ModuleSheaf X Λ,
      IsZero (((moduleDirectImage f Λ).rightDerived (d + 1)).obj M) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  obtain ⟨d, hd, _⟩ := Vanishing.exists_universal_higherDirectImage_torsion_bound f
  refine ⟨d, ?_⟩
  exact moduleRightDerived_bound_of_torsion_bound Λ f N hN hΛ d
    (fun M hM => hd M hM (d + 1) (Nat.lt_succ_self d))

/-- One finite bound works for every native derived object under the original
proper direct image. No lower bound is required for the upper-amplitude part. -/
theorem exists_moduleUnboundedDerivedDirectImage_amplitude_of_proper
    [CompactSpace S] (f : X ⟶ S) [IsProper f]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    ∃ d : ℕ,
      (∀ (K : DerivedCategory (ModuleSheaf X Λ)) (m : ℤ), K.IsGE m →
        ((moduleUnboundedDerivedDirectImage Λ f).obj K).IsGE m) ∧
      (∀ (K : DerivedCategory (ModuleSheaf X Λ)) (n : ℤ), K.IsLE n →
        ((moduleUnboundedDerivedDirectImage Λ f).obj K).IsLE (n + (d : ℤ))) := by
  obtain ⟨d, hd⟩ := exists_moduleRightDerived_bound_of_proper Λ f N hN hΛ
  refine ⟨d, ?_, ?_⟩
  · intro K m hm
    let : K.IsGE m := hm
    exact (moduleDirectImage f Λ).unboundedRightDerivedFunctor_isGE_of_bound d hd K m
  · intro K n hn
    let : K.IsLE n := hn
    exact (moduleDirectImage f Λ).unboundedRightDerivedFunctor_isLE_of_bound d hd K n

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
