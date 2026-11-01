/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.CoprimeScalar
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite generation from an original coprime trace

The native categorical retract, including its original forward arrow, descends
finite generation through any module-valued functor. No exactness, additive
functor, Noetherian ring or finite underlying set is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat

universe c h r v

variable {R : Type r} [Ring R]

/-- A retract of a finitely generated module is finitely generated over the
same ring, using the actual retraction maps. -/
theorem finite_of_retract {A B : ModuleCat.{v} R} (h : Retract A B)
    [Module.Finite R B] : Module.Finite R A := by
  apply Module.Finite.of_surjective h.r.hom
  intro x
  exact ⟨h.i x, congrArg (fun a => a x) h.retract⟩

/-- Any module-valued functor descends finite generation across an original
trace of rank coprime to an annihilator. The functor need not be additive. -/
theorem finite_obj_of_coprime_trace {C : Type c} [Category.{h} C] [Preadditive C]
    {A B : C} (i : A ⟶ B) (t : B ⟶ A) (n p : ℕ)
    (ht : i ≫ t = n • 𝟙 A) (hcop : n.Coprime p) (hp : p • 𝟙 A = 0)
    (G : C ⥤ ModuleCat.{v} R) [Module.Finite R (G.obj B)] :
    Module.Finite R (G.obj A) :=
  finite_of_retract ((Preadditive.retractOfCoprimeTrace i t n p ht hcop hp).map G)

end ModuleCat
