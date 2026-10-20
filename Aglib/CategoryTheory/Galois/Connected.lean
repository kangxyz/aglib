/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Connected objects are preserved by actual categorical equivalences.

Source: `lean/R5Lab/Aglib/CategoryTheory/Galois/Connected.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `4bd9614ca90392c341c01a87f8dd1587d15fabb2a286d2bdedcf6d74f6918956`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

universe u

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
universe v w z
namespace CategoryTheory.PreGaloisCategory

/-- An actual categorical equivalence preserves the usual connected-object
property. Both initiality and monomorphisms are reflected by its inverse. -/
theorem isConnected_obj_of_equivalence {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] (F : C ⥤ D) [F.IsEquivalence]
    (X : C) [IsConnected X] : IsConnected (F.obj X) := by
  let e := F.asEquivalence
  constructor
  · intro h
    exact IsConnected.notInitial (h.isInitialOfObj F)
  · intro Y i hi hY
    let := hi
    let j : e.inverse.obj Y ⟶ X := e.inverse.map i ≫ (e.unitIso.app X).inv
    have hn : IsInitial (e.inverse.obj Y) → False :=
      fun h => hY (h.isInitialOfObj e.inverse)
    have : Mono j := by dsimp [j]; infer_instance
    have : IsIso j := IsConnected.noTrivialComponent _ _ hn
    have : IsIso (e.inverse.map i) := IsIso.of_isIso_comp_right _ (e.unitIso.app X).inv
    exact isIso_of_reflects_iso i e.inverse

end CategoryTheory.PreGaloisCategory

end -- original noncomputable section
end
