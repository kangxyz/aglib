/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The original torsion quotient onto a rank-one module

An original surjection onto a framed rank-one module with torsion kernel
factors every original map to a torsion-free module. If that map is
surjective and its target is nonzero, the SAME factor is an isomorphism.
Native quotient maps and the native rank-one kernel theorem are reused.
-/

@[expose] public section

universe u v w z

namespace LinearMap

/-- An original surjection with torsion kernel onto a framed rank-one module
has the SAME torsion-free nonzero quotient as any other original surjection.
The actual factor retains the exact composite equation. No finiteness,
locality or target-rank premise is required. -/
theorem exists_linearEquiv_of_surjective_of_ker_le_torsion
    {B : Type u} [CommRing B] [IsDomain B]
    {M : Type v} {L : Type w} {N : Type z}
    [AddCommGroup M] [AddCommGroup L] [AddCommGroup N]
    [Module B M] [Module B L] [Module B N]
    [Module.IsTorsionFree B N] [Nontrivial N]
    (q : M →ₗ[B] L) (hq : Function.Surjective q)
    (hk : ker q ≤ Submodule.torsion B M) (eL : L ≃ₗ[B] B)
    (v : M →ₗ[B] N) (hv : Function.Surjective v) :
    ∃ e : L ≃ₗ[B] N, e.toLinearMap.comp q = v := by
  have hkv : ker q ≤ ker v := by
    intro m hm
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff m).mp (hk hm)
    have hz : (r : B) • v m = 0 :=
      (v.map_smul (r : B) m).symm.trans ((congrArg v hr).trans v.map_zero)
    exact (smul_eq_zero.mp hz).resolve_left (nonZeroDivisors.coe_ne_zero r)
  let d : L →ₗ[B] N :=
    ((ker q).liftQ v hkv).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hfactor : d.comp q = v := by
    ext m
    change (ker q).liftQ v hkv ((q.quotKerEquivOfSurjective hq).symm (q m)) = v m
    rw [quotKerEquivOfSurjective_symm_apply]
    rfl
  have hd : Function.Surjective d := by
    intro n
    obtain ⟨m, rfl⟩ := hv n
    exact ⟨q m, DFunLike.congr_fun hfactor m⟩
  let g : B →ₗ[B] N := d.comp eL.symm.toLinearMap
  have hg : Function.Surjective g := hd.comp eL.symm.surjective
  have hg1 : g 1 ≠ 0 := by
    intro h
    exact ne_zero_of_surjective hg (LinearMap.ext_ring h)
  have hspan : g = toSpanSingleton B N (g 1) :=
    LinearMap.ext_ring (toSpanSingleton_apply_one B N (g 1)).symm
  have hginj : Function.Injective g := ker_eq_bot.mp (by
    rw [hspan]
    exact ker_toSpanSingleton B hg1)
  have hdinj : Function.Injective d := by
    intro l l' h
    apply eL.injective
    apply hginj
    change d (eL.symm (eL l)) = d (eL.symm (eL l'))
    simpa only [LinearEquiv.symm_apply_apply] using h
  exact ⟨LinearEquiv.ofBijective d ⟨hdinj, hd⟩, hfactor⟩

end LinearMap
