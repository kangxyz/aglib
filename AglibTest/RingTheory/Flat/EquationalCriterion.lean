/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Flat.EquationalCriterion

/-! Focused consumer of flatness from lifted relations, with an axiom guard. -/

@[expose] public section

/-- A module whose finite relations all lift through one linear map from a flat module is flat. -/
example {R M E : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]
    [Module.Flat R E] (g : E →ₗ[R] M)
    (h : ∀ {l : ℕ} (f : Fin l → R) (x : Fin l → M), ∑ i, f i • x i = 0 →
      ∃ y : Fin l → E, (∀ i, g (y i) = x i) ∧ ∑ i, f i • y i = 0) :
    Module.Flat R M :=
  Module.Flat.of_forall_exists_lift_relation (κ := Unit) (E := fun _ => E) (fun _ => inferInstance)
    (fun _ => g) fun f x hfx => let ⟨y, hy⟩ := h f x hfx; ⟨(), y, hy⟩

/--
info: 'Module.Flat.of_forall_exists_lift_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Flat.of_forall_exists_lift_relation
