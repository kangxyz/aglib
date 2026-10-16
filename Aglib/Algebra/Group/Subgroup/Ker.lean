/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Transporting range-kernel exactness

Range-kernel exactness transports across three multiplicative equivalences satisfying the two
displayed commuting equations. All six groups retain the source's common universe.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/GlobalLocalization.lean`.
SHA-256: `f92ecc4ad2506e2fd4c98716cfbf4a983e8a4492685c754e9995ed4eca37d54a`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w
namespace MonoidHom

/-- Transport range-kernel exactness across the three given commuting group isomorphisms. -/
theorem range_eq_ker_of_equiv
    {A B C A' B' C' : Type w}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

end MonoidHom
