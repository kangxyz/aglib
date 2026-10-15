/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final

/-! Actual finite-tail colimit isomorphisms with both original stage-inclusion formulas.

Source: `Quillen/CategoryTheory/Limits/SequentialTailColimit.lean`
from the supplied Quillen archive.
Source SHA-256: `fa9a171ed0c0046c10403972c5b614adf30b4c9b32d7a54d9d22b603177e3e1c`.
All declarations are migrated with their original hypotheses and maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits.SequentialSystem

/-- The actual shift of the original natural-number indexing category. -/
def shiftFunctor (t : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ ↦ t+n) from fun _ _ h ↦ Nat.add_le_add_left h t).functor

instance instFinalShiftFunctor (t : ℕ) : (shiftFunctor t).Final :=
  (Monotone.final_functor_iff _).mpr (fun n ↦ ⟨n,Nat.le_add_left n t⟩)

/-- Dropping finitely many original stages preserves the actual sequential colimit. -/
def tailColimitIso {C : Type u} [Category.{v} C]
    (F : ℕ ⥤ C) [HasColimit F] (t : ℕ) :
    colimit (shiftFunctor t ⋙ F) ≅ colimit F :=
  Functor.Final.colimitIso (shiftFunctor t) F

@[reassoc (attr := simp)] theorem tailColimitIso_ι_hom
    {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι (shiftFunctor t ⋙ F) n ≫ (tailColimitIso F t).hom =
      colimit.ι F (t+n) :=
  Functor.Final.ι_colimitIso_hom (shiftFunctor t) F n

@[reassoc (attr := simp)] theorem tailColimitIso_ι_inv
    {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι F (t+n) ≫ (tailColimitIso F t).inv =
      colimit.ι (shiftFunctor t ⋙ F) n :=
  Functor.Final.ι_colimitIso_inv (shiftFunctor t) F n

end CategoryTheory.Limits.SequentialSystem
