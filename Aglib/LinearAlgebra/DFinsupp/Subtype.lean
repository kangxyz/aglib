/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Removing zero fibers from a dependent finitely supported sum

The original subtype-domain restriction is surjective. When the omitted
fibers are subsingleton, it is an actual scalar-linear equivalence. The
comparison retains every original coefficient on the indicated subtype.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DFinsupp

variable {R ι : Type*} [Semiring R] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Restricting the original dependent sum to a subtype is surjective. -/
theorem subtypeDomainLinearMap_surjective (p : ι → Prop) [DecidablePred p] :
    Function.Surjective (subtypeDomainLinearMap R (β := M) p) := by
  classical
  let l : (Π₀ i : Subtype p, M i.val) →ₗ[R] Π₀ i, M i :=
    lsum ℕ (fun i : Subtype p => lsingle i.val)
  have hl : (subtypeDomainLinearMap R M p).comp l = LinearMap.id := by
    apply DFinsupp.lhom_ext
    intro i x
    simp only [LinearMap.comp_apply, l, lsum_single, lsingle_apply, LinearMap.id_apply]
    ext j
    simp only [subtypeDomainLinearMap_apply, subtypeDomain_apply]
    by_cases h : j = i
    · subst j
      simp
    · rw [single_eq_of_ne h, single_eq_of_ne (fun he => h (Subtype.ext he))]
  intro x
  exact ⟨l x, LinearMap.congr_fun hl x⟩

/-- The native subtype restriction is an equivalence when every omitted
fiber is zero. No finiteness of the ambient or retained index type is assumed. -/
def subtypeDomainLinearEquiv (p : ι → Prop) [DecidablePred p]
    (h : ∀ i, ¬ p i → Subsingleton (M i)) :
    (Π₀ i, M i) ≃ₗ[R] Π₀ i : Subtype p, M i.val :=
  LinearEquiv.ofBijective (subtypeDomainLinearMap R M p) ⟨by
    intro x y hxy
    ext i
    by_cases hi : p i
    · exact congrArg (fun z : Π₀ i : Subtype p, M i.val => z ⟨i, hi⟩) hxy
    · exact (h i hi).elim _ _, subtypeDomainLinearMap_surjective (R := R) p⟩

/-- The subtype equivalence is the original coefficient restriction. -/
@[simp]
theorem subtypeDomainLinearEquiv_apply (p : ι → Prop) [DecidablePred p]
    (h : ∀ i, ¬ p i → Subsingleton (M i)) (x : Π₀ i, M i) (i : Subtype p) :
    subtypeDomainLinearEquiv (R := R) p h x i = x i.val := rfl

end DFinsupp
