/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystem
public import Aglib.RingTheory.AdicCompletion.Powers

/-! # The canonical completed-ring action on compatible finite systems -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} (hF : IsCompatibleSystem I F)

/-- The quotient-ring action supplied by the actual annihilation condition. -/
abbrev stageQuotientModule (n : ℕ) : Module (R ⧸ I ^ n) (F.obj (op n)) :=
  (show Module.IsTorsionBySet R (F.obj (op n)) (↑(I ^ n) : Set R) from
    fun {x} {a} => hF.annihilated n a x).module

/-- The completion acts at level `n` through its original evaluation modulo `Iⁿ`. -/
abbrev stageCompletionModule (n : ℕ) : Module (AdicCompletion I R) (F.obj (op n)) :=
  let := hF.stageQuotientModule n
  Module.compHom (F.obj (op n)) (evalₐ I n).toRingHom

/-- The completed action restricts to the original coefficient action. -/
theorem stageCompletionModule_of_smul (n : ℕ) (a : R) (x : F.obj (op n)) :
    let := hF.stageCompletionModule n
    of I R a • x = a • x := by
  let := hF.stageQuotientModule n
  change evalₐ I n (of I R a) • x = a • x
  rw [evalₐ_of]
  rfl

/-- Every original transition is linear for the canonical completed-ring actions. -/
theorem transition_completion_smul {n m : ℕ} (h : n ≤ m)
    (a : AdicCompletion I R) (x : F.obj (op m)) :
    let := hF.stageCompletionModule m
    let := hF.stageCompletionModule n
    F.map (homOfLE h).op (a • x) = a • F.map (homOfLE h).op x := by
  let := hF.stageQuotientModule m
  let := hF.stageQuotientModule n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m a)
  have hn : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factor_evalₐ I h a, ← hr]
    rfl
  change F.map (homOfLE h).op (evalₐ I m a • x) =
    evalₐ I n a • F.map (homOfLE h).op x
  rw [← hr, hn]
  exact (F.map (homOfLE h).op).hom.map_smul r x

/-- The native section predicate is stable under the completed-ring action.
Only the scalar structure changes; the compatible families are unchanged. -/
def completionSectionsSubmodule :
    let (j : ℕᵒᵖ) := hF.stageCompletionModule j.unop
    Submodule (AdicCompletion I R) (∀ j, F.obj j) := by
  let (j : ℕᵒᵖ) := hF.stageCompletionModule j.unop
  exact
    { (ModuleCat.sectionsSubmodule F).toAddSubmonoid with
      carrier := (ModuleCat.sectionsSubmodule F : Set (∀ j, F.obj j))
      smul_mem' := by
        intro a x hx j k f
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        change F.map f (a • x j) = a • x k
        rw [hf, hF.transition_completion_smul (leOfHom f.unop)]
        exact congrArg (a • ·) (hx f) }

/-- The actual native inverse limit, equipped with its canonical completed-ring module structure. -/
abbrev sectionsCompletionModule : Module (AdicCompletion I R) (ModuleCat.sectionsSubmodule F) :=
  let (j : ℕᵒᵖ) := hF.stageCompletionModule j.unop
  inferInstanceAs (Module (AdicCompletion I R) hF.completionSectionsSubmodule)

end AdicCompletion.IsCompatibleSystem
