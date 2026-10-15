/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Finrank
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring

/-!
# The Euler characteristic of a bounded finite-dimensional complex

Termwise bounds give finite support for the native rank function of an
integer-indexed complex. Over a field, the original homology and the two
adjacent differential images satisfy the native dimension identity. These
facts prove equality of the existing homological and termwise Euler
characteristics. The proof sums the original dimension identities; the
adjacent image contributions cancel by the native alternating signs.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace CochainComplex

universe u v

section Ring

variable {R : Type u} [Ring R] [Nontrivial R] (C : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The native rank support of a termwise bounded complex lies in its original interval,
without a finiteness hypothesis on its terms. -/
theorem finrankSupport_subset_Icc_of_bounds (a b : ℤ) [C.IsStrictlyGE a]
    [C.IsStrictlyLE b] : GradedObject.finrankSupport C.X ⊆ Set.Icc a b := by
  intro i hi
  change finrank R (C.X i) ≠ 0 at hi
  constructor
  · by_contra h
    let : Subsingleton (C.X i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyGE a i (by omega))
    exact hi (Module.finrank_zero_of_subsingleton)
  · by_contra h
    let : Subsingleton (C.X i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE b i (by omega))
    exact hi (Module.finrank_zero_of_subsingleton)

/-- A termwise bounded complex has finite native rank support, without a finiteness
hypothesis on its terms. -/
theorem finite_finrankSupport_of_bounds (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b] :
    (GradedObject.finrankSupport C.X).Finite :=
  (Set.finite_Icc a b).subset (C.finrankSupport_subset_Icc_of_bounds a b)

end Ring

section Field

variable {k : Type u} [Field k] (C : CochainComplex (ModuleCat.{v} k) ℤ)

/-- The original homology and adjacent differential images balance the middle term in
each integer degree; only that term needs to be finite. -/
theorem finrank_homology_add_finrank_d_ranges (i : ℤ) [Module.Finite k (C.X i)] :
    finrank k (C.homology i) + finrank k (C.d (i - 1) i).hom.range +
      finrank k (C.d i (i + 1)).hom.range = finrank k (C.X i) := by
  let : Module.Finite k (C.sc i).X₂ := by
    change Module.Finite k (C.X i)
    infer_instance
  have hp : (ComplexShape.up ℤ).prev i = i - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change (i - 1) + 1 = i; omega)
  have hn : (ComplexShape.up ℤ).next i = i + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have h := (C.sc i).finrank_homology_add_finrank_ranges
  change finrank k (C.homology i) +
    finrank k (C.d ((ComplexShape.up ℤ).prev i) i).hom.range +
      finrank k (C.d i ((ComplexShape.up ℤ).next i)).hom.range = finrank k (C.X i) at h
  rwa [hp, hn] at h

/-- A bounded complex of finite-dimensional vector spaces has equal original homological
and termwise Euler characteristics, using the native signs and native finite sums. -/
theorem homologyEulerChar_eq_eulerChar (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.Finite k (C.X i)] :
    HomologicalComplex.homologyEulerChar C = HomologicalComplex.eulerChar C := by
  classical
  let χ : ℤ → ℤ := fun i => ((ComplexShape.up ℤ).χ i : ℤ)
  let h : ℤ → ℤ := fun i => χ i * (finrank k (C.homology i) : ℤ)
  let t : ℤ → ℤ := fun i => χ i * (finrank k (C.X i) : ℤ)
  let r : ℤ → ℤ := fun i => χ i * (finrank k (C.d i (i + 1)).hom.range : ℤ)
  have hX : (fun i : ℤ => finrank k (C.X i)).HasFiniteSupport :=
    C.finite_finrankSupport_of_bounds a b
  have hsupport (f : ℤ → ℤ) (hf : ∀ i, finrank k (C.X i) = 0 → f i = 0) :
      f.HasFiniteSupport := by
    apply hX.subset
    intro i hi hz
    exact hi (hf i hz)
  have hh : h.HasFiniteSupport := hsupport h (by
    intro i hz
    have hd := C.finrank_homology_add_finrank_d_ranges i
    have hzero : finrank k (C.homology i) = 0 := by omega
    simp only [h, hzero, Nat.cast_zero, mul_zero])
  have hr : r.HasFiniteSupport := hsupport r (by
    intro i hz
    have hd := LinearMap.finrank_range_le (C.d i (i + 1)).hom
    have hzero : finrank k (C.d i (i + 1)).hom.range = 0 := by omega
    simp only [r, hzero, Nat.cast_zero, mul_zero])
  have hpointwise (i : ℤ) : t i = h i + r i - r (i - 1) := by
    have hd := C.finrank_homology_add_finrank_d_ranges i
    have hz : (finrank k (C.homology i) : ℤ) +
        (finrank k (C.d (i - 1) i).hom.range : ℤ) +
          (finrank k (C.d i (i + 1)).hom.range : ℤ) = (finrank k (C.X i) : ℤ) := by
      exact_mod_cast hd
    have hs : χ i = -χ (i - 1) := by
      have hs' : (ComplexShape.up ℤ).χ i = -(ComplexShape.up ℤ).χ (i - 1) :=
        (ComplexShape.up ℤ).χ_next (by change (i - 1) + 1 = i; omega)
      exact congrArg (fun z : ℤˣ => (z : ℤ)) hs'
    dsimp only [t, h, r]
    rw [sub_add_cancel, ← hz, hs]
    ring
  have hrshift : (fun i : ℤ => r (i - 1)).HasFiniteSupport :=
    hr.fun_comp_of_injective (by
      intro i j hij
      change i - 1 = j - 1 at hij
      omega)
  have hsum : (∑ᶠ i, t i) = (∑ᶠ i, h i) + (∑ᶠ i, r i) - ∑ᶠ i, r (i - 1) := by
    calc
      (∑ᶠ i, t i) = ∑ᶠ i, ((h + r) i - r (i - 1)) := by
        congr 1
        funext i
        exact hpointwise i
      _ = (∑ᶠ i, (h + r) i) - ∑ᶠ i, r (i - 1) :=
        finsum_sub_distrib (hh.add hr) hrshift
      _ = _ := by
        simpa only [Pi.add_apply] using
          congrArg (fun z => z - ∑ᶠ i, r (i - 1)) (finsum_add_distrib hh hr)
  have hshift : (∑ᶠ i : ℤ, r (i - 1)) = ∑ᶠ i : ℤ, r i :=
    finsum_comp (fun i : ℤ => i - 1)
      ⟨by
        intro i j hij
        change i - 1 = j - 1 at hij
        omega,
      fun i => ⟨i + 1, by change (i + 1) - 1 = i; omega⟩⟩
  change (∑ᶠ i, h i) = ∑ᶠ i, t i
  rw [hsum, hshift]
  ring

end Field

end CochainComplex
