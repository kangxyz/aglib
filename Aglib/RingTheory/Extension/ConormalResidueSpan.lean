/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Transporting conormal generators to the original ideal fiber

The original extension's tensor equivalence identifies the residue fiber of
its kernel with the base change of its conormal module. The spanning statement
below retains the same kernel elements and original scalar actions.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Algebra.Extension

variable {R B K ι : Type*} [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] (P : Extension R B) [Algebra B K] [Algebra P.Ring K]
  [IsScalarTower P.Ring B K]

/-- Spanning by specified conormal classes is equivalent to spanning the
actual tensor product of the original kernel ideal by the same elements. -/
theorem span_kernel_tmul_eq_top_iff (v : ι → P.ker) :
    Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[P.Ring] v i) = ⊤ ↔
      Submodule.span K (Set.range fun i =>
        (1 : K) ⊗ₜ[B] Cotangent.mk (v i)) = ⊤ := by
  let e : K ⊗[P.Ring] P.ker ≃ₗ[K] K ⊗[B] P.Cotangent :=
    (AlgebraTensorModule.cancelBaseChange P.Ring B K K P.ker).symm.trans
      (P.cotangentEquiv.baseChange B K _ _)
  have he (i : ι) : e ((1 : K) ⊗ₜ[P.Ring] v i) =
      (1 : K) ⊗ₜ[B] Cotangent.mk (v i) := by
    simp only [e, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul, contangentEquiv_tmul, one_smul]
  have hmap : (Submodule.span K
      (Set.range fun i => (1 : K) ⊗ₜ[P.Ring] v i)).map e.toLinearMap =
      Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] Cotangent.mk (v i)) := by
    rw [Submodule.map_span, ← Set.range_comp']
    congr 1
    ext x
    simp only [LinearEquiv.coe_coe, he]
  constructor
  · intro h
    rw [← hmap, h, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  · intro h
    apply Submodule.map_injective_of_injective e.injective
    rw [hmap, h, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

end Algebra.Extension
