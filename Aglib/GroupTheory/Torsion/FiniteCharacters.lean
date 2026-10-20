/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Levels
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Finiteness from an injective finite-level character detector

All detector maps and their injectivity inputs remain explicit.

Source: `R5Lab.Aglib.GroupTheory.Torsion.FiniteCharacters`.
Packet SHA-256:
`ee4bacd0de318e9f7c4b39dcc339754986c9974638d1ae01f66517324b3658fa`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace AddSubgroup
variable {T : Type*} [AddCommGroup T]
variable {V : Type*} [AddCommGroup V] [Finite V]
/-- An annihilated torsion group is finite from an injective realization at that finite level.
Only the finite domain `V` and the standard coefficient realization are background;
global finiteness of `T` is a conclusion.
Source: the finite-character deduction after `K2-015#lem:k2015-frobenius`, at the module snapshot.
-/
theorem finite_of_finite_character_level (n : ℕ) (hn : 0 < n)
    (annihilated : ∀ x : T, n • x = 0)
    (realization : torsionBy T n → (V →+ ZMod n))
    (injective : Function.Injective realization) : Finite T := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  have hfunc : Function.Injective (fun x : torsionBy T n => (realization x : V → ZMod n)) :=
    DFunLike.coe_injective.comp injective
  let : Finite (torsionBy T n) := Finite.of_injective _ hfunc
  exact Finite.of_injective
    (fun x : T => (⟨x, torsionBy.nsmul_iff.mpr (annihilated x)⟩ : torsionBy T n))
    (fun x y h => congrArg Subtype.val h)

end AddSubgroup
