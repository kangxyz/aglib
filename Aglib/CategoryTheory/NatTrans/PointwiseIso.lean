/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Whole original natural isomorphisms from explicit component proofs -/

@[expose] public noncomputable section

namespace CategoryTheory.NatTrans

universe u v w t

/-- Bundle the original transformation before specializing concrete functor heads. -/
def isoOfIsIsoComponents {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{t} D] {F G : C ⥤ D}
    (α : F ⟶ G) (h : ∀ X, IsIso (α.app X)) : F ≅ G := by
  let : ∀ X, IsIso (α.app X) := h
  let : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The bundled natural iso retains the literal original transformation. -/
theorem isoOfIsIsoComponents_hom {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{t} D] {F G : C ⥤ D}
    (α : F ⟶ G) (h : ∀ X, IsIso (α.app X)) :
    (isoOfIsIsoComponents α h).hom = α := rfl

end CategoryTheory.NatTrans
