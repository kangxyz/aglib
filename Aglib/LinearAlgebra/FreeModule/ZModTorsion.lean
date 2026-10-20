/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Multiples and annihilated vectors in free cyclic-coefficient modules


Source: `R5Lab.Aglib.LinearAlgebra.FreeModule.ZModTorsion`.
Packet SHA-256:
`7ecb7db822d28c62cd21aab174101f4d23f941b52b320cdf53f4d9b19419c2e0`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace ZMod
/-- The elementary divisibility calculation used internally in native torsion
coordinates. This is a theorem about every element, not finite testing. -/
theorem zmod_killed_iff_multiple (d e : ℕ) (hd : 0 < d)
    (x : ZMod (d * e)) : d • x = 0 ↔ ∃ y : ZMod (d * e), e • y = x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  constructor
  · intro h
    have hdiv : ((d * e : ℕ) : ℤ) ∣ (d : ℤ) * k := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul] using h
    rw [Nat.cast_mul] at hdiv
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    obtain ⟨l, hl⟩ := (mul_dvd_mul_iff_left hd0).mp hdiv
    refine ⟨(l : ZMod (d * e)), ?_⟩
    rw [hl]
    simp [nsmul_eq_mul]
  · rintro ⟨y, hy⟩
    rw [← hy, ← mul_smul]
    exact ZModModule.char_nsmul_eq_zero (d * e) y

/-- A native finite free module has its d-killed subgroup equal to its
e-multiples when the scalar ring is Z/(d*e). -/
theorem basis_killed_iff_multiple {M : Type*} [AddCommGroup M]
    (d e : ℕ) (hd : 0 < d) [Module (ZMod (d * e)) M]
    (b : Module.Basis (Fin 2) (ZMod (d * e)) M) (x : M) :
    d • x = 0 ↔ ∃ y : M, e • y = x := by
  constructor
  · intro hx
    have hc (i : Fin 2) : d • b.equivFun x i = 0 := by
      have h := congrArg (fun z => b.equivFun z i) hx
      simpa only [map_nsmul, Pi.smul_apply, map_zero, Pi.zero_apply] using h
    choose y hy using fun i => (zmod_killed_iff_multiple d e hd _).mp (hc i)
    refine ⟨b.equivFun.symm y, ?_⟩
    apply b.equivFun.injective
    rw [map_nsmul, b.equivFun.apply_symm_apply]
    exact funext hy
  · rintro ⟨y, rfl⟩
    rw [← mul_smul]
    exact ZModModule.char_nsmul_eq_zero (d * e) y


end ZMod
