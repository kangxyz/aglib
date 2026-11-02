/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.IdealBaseChange
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The torsion kernel of the original scalar-extended ideal inclusion

An actual element of the ideal annihilates the kernel of the existing tensor
inclusion. If its image in the target algebra is regular, that kernel is
exactly the native torsion submodule. No flatness, domain or finiteness
assumption is used, and no alternative inclusion or localization is built.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open TensorProduct
open scoped nonZeroDivisors

universe u v

namespace Algebra

variable (S : Type u) (T : Type v) [CommRing S] [CommRing T] [Algebra S T]
  (I : Ideal S)

/-- An original ideal element acts on its scalar extension through the actual
extended ideal inclusion. -/
theorem smul_eq_extendedIdealInclusion_tmul (c : I) (z : T ⊗[S] I) :
    algebraMap S T (c : S) • z =
      extendedIdealInclusion S T I z ⊗ₜ[S] c := by
  induction z using TensorProduct.inductionOn with
  | tmul t i =>
      calc
        algebraMap S T (c : S) • (t ⊗ₜ[S] i) = ((c : S) • t) ⊗ₜ[S] i := by
          simp only [TensorProduct.smul_tmul', Algebra.smul_def, Algebra.algebraMap_self_apply]
        _ = t ⊗ₜ[S] ((c : S) • i) := TensorProduct.smul_tmul _ _ _
        _ = t ⊗ₜ[S] ((i : S) • c) := by
          congr 1
          apply Subtype.ext
          exact mul_comm _ _
        _ = ((i : S) • t) ⊗ₜ[S] c := (TensorProduct.smul_tmul _ _ _).symm
        _ = extendedIdealInclusion S T I (t ⊗ₜ[S] i) ⊗ₜ[S] c := rfl
  | add z w hz hw =>
      simp only [smul_add, map_add, TensorProduct.add_tmul, hz, hw]

/-- A regular image of one original ideal element identifies the exact kernel
of the original tensor inclusion with the native torsion submodule. -/
theorem extendedIdealInclusion_ker_eq_torsion (c : I)
    (hc : IsRegular (algebraMap S T (c : S))) :
    LinearMap.ker (extendedIdealInclusion S T I) =
      Submodule.torsion T (T ⊗[S] I) := by
  ext z
  change extendedIdealInclusion S T I z = 0 ↔ z ∈ Submodule.torsion T (T ⊗[S] I)
  constructor
  · intro hz
    refine (Submodule.mem_torsion_iff z).mpr ?_
    refine ⟨⟨algebraMap S T (c : S), isRegular_iff_mem_nonZeroDivisors.mp hc⟩, ?_⟩
    change algebraMap S T (c : S) • z = 0
    rw [smul_eq_extendedIdealInclusion_tmul, hz, TensorProduct.zero_tmul]
  · intro hz
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff z).mp hz
    apply ((isRegular_iff_mem_nonZeroDivisors.mpr r.property).smul_eq_zero_iff_right).mp
    exact ((extendedIdealInclusion S T I).map_smul (r : T) z).symm.trans
      ((congrArg (extendedIdealInclusion S T I) hr).trans (map_zero _))

end Algebra
