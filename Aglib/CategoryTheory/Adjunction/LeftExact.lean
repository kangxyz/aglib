/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Actual left-exact adjunctions

This package retains a native left-exact functor, its actual right adjoint and
its original adjunction. It imposes no topos property on the categories.
Identity, composition, equivalences and mates use the native constructions.
The terminal-Hom comparison is the categorical global-section law used by
presented sheaf topoi; no point or site presentation is chosen here.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- One actual adjunction with a native bundled left-exact inverse-image functor. -/
structure LeftExactAdjunction (C : Type u₁) (D : Type u₂)
    [Category.{v₁} C] [Category.{v₂} D] where
  /-- The actual left adjoint, with its native finite-limit preservation. -/
  left : C ⥤ₗ D
  /-- The actual right adjoint. -/
  right : D ⥤ C
  /-- The original unit and counit, rather than a reselected adjunction. -/
  adj : left.obj ⊣ right

namespace LeftExactAdjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Package the given native adjunction without changing either functor or its unit. -/
def ofAdjunction {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    [PreservesFiniteLimits L] : LeftExactAdjunction C D where
  left := LeftExactFunctor.of L
  right := R
  adj := a

/-- The native identity adjunction. -/
def id (C : Type u₁) [Category.{v₁} C] : LeftExactAdjunction C C :=
  ofAdjunction (Adjunction.id (C := C))

/-- Composition retains the native composite unit and counit. -/
def comp (a : LeftExactAdjunction C D) (b : LeftExactAdjunction D E) :
    LeftExactAdjunction C E :=
  ofAdjunction (a.adj.comp b.adj)

/-- A proved category equivalence supplies its original native adjunction. -/
def ofEquivalence (e : C ≌ D) : LeftExactAdjunction C D :=
  ofAdjunction e.toAdjunction

@[simp]
theorem ofEquivalence_left (e : C ≌ D) : (ofEquivalence e).left.obj = e.functor := rfl

@[simp]
theorem ofEquivalence_right (e : C ≌ D) : (ofEquivalence e).right = e.inverse := rfl

@[simp]
theorem ofEquivalence_unit (e : C ≌ D) : (ofEquivalence e).adj.unit = e.unit := rfl

@[simp]
theorem ofEquivalence_counit (e : C ≌ D) : (ofEquivalence e).adj.counit = e.counit := rfl

@[simp]
theorem id_unit_app (X : C) : (id C).adj.unit.app X = 𝟙 X := rfl

@[simp]
theorem id_counit_app (X : C) : (id C).adj.counit.app X = 𝟙 X := rfl

/-- The composite unit is exactly the original pair of units. -/
theorem comp_unit_app (a : LeftExactAdjunction C D) (b : LeftExactAdjunction D E) (X : C) :
    (a.comp b).adj.unit.app X =
      a.adj.unit.app X ≫ a.right.map (b.adj.unit.app (a.left.obj.obj X)) :=
  Adjunction.comp_unit_app a.adj b.adj X

/-- The composite counit is exactly the original pair of counits. -/
theorem comp_counit_app (a : LeftExactAdjunction C D) (b : LeftExactAdjunction D E) (X : E) :
    (a.comp b).adj.counit.app X =
      b.left.obj.map (a.adj.counit.app (b.right.obj X)) ≫ b.adj.counit.app X :=
  Adjunction.comp_counit_app a.adj b.adj X

/-- Mates are the native equivalence for the actual two adjunctions. -/
abbrev mateEquiv (a b : LeftExactAdjunction C D) :
    (b.left.obj ⟶ a.left.obj) ≃ (a.right ⟶ b.right) :=
  conjugateEquiv a.adj b.adj

/-- The native mate retains the original units. -/
theorem mateEquiv_unit (a b : LeftExactAdjunction C D)
    (α : b.left.obj ⟶ a.left.obj) (X : C) :
    a.adj.unit.app X ≫ (mateEquiv a b α).app (a.left.obj.obj X) =
      b.adj.unit.app X ≫ b.right.map (α.app X) :=
  unit_conjugateEquiv a.adj b.adj α X

/-- The native mate retains the original counits. -/
theorem mateEquiv_counit (a b : LeftExactAdjunction C D)
    (α : b.left.obj ⟶ a.left.obj) (Y : D) :
    b.left.obj.map ((mateEquiv a b α).app Y) ≫ b.adj.counit.app Y =
      α.app (a.right.obj Y) ≫ a.adj.counit.app Y :=
  conjugateEquiv_counit a.adj b.adj α Y

/-- The actual inverse image sends a terminal object to a terminal object. -/
def terminalIso (a : LeftExactAdjunction C D) {X : C} {Y : D}
    (hX : IsTerminal X) (hY : IsTerminal Y) : a.left.obj.obj X ≅ Y :=
  (hX.isTerminalObj a.left.obj).uniqueUpToIso hY

/-- Direct image preserves intrinsic global points through the original adjunction. -/
def terminalHomEquiv (a : LeftExactAdjunction C D) {X : C} {Y : D}
    (hX : IsTerminal X) (hY : IsTerminal Y) (Z : D) :
    (X ⟶ a.right.obj Z) ≃ (Y ⟶ Z) :=
  (a.adj.homEquiv X Z).symm.trans
    (Iso.homCongr (a.terminalIso hX hY) (Iso.refl Z))

/-- The point comparison is the original counit transpose and terminal comparison. -/
theorem terminalHomEquiv_apply (a : LeftExactAdjunction C D) {X : C} {Y : D}
    (hX : IsTerminal X) (hY : IsTerminal Y) (Z : D) (s : X ⟶ a.right.obj Z) :
    a.terminalHomEquiv hX hY Z s =
      (a.terminalIso hX hY).inv ≫ a.left.obj.map s ≫ a.adj.counit.app Z := by
  simp only [terminalHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Adjunction.homEquiv_counit]

/-- The inverse point comparison retains the original adjunction unit. -/
theorem terminalHomEquiv_symm_apply (a : LeftExactAdjunction C D) {X : C} {Y : D}
    (hX : IsTerminal X) (hY : IsTerminal Y) (Z : D) (s : Y ⟶ Z) :
    (a.terminalHomEquiv hX hY Z).symm s =
      a.adj.unit.app X ≫ a.right.map ((a.terminalIso hX hY).hom ≫ s) := by
  change a.adj.homEquiv X Z
    ((a.terminalIso hX hY).hom ≫ s ≫ (Iso.refl Z).inv) = _
  simp only [Iso.refl_inv, Category.comp_id, Adjunction.homEquiv_unit]

/-- The point comparison preserves every actual coefficient arrow. -/
theorem terminalHomEquiv_naturality (a : LeftExactAdjunction C D) {X : C} {Y : D}
    (hX : IsTerminal X) (hY : IsTerminal Y) {Z Z' : D}
    (s : X ⟶ a.right.obj Z) (f : Z ⟶ Z') :
    a.terminalHomEquiv hX hY Z' (s ≫ a.right.map f) =
      a.terminalHomEquiv hX hY Z s ≫ f := by
  simp only [terminalHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id]
  rw [a.adj.homEquiv_naturality_right_symm, Category.assoc]

end LeftExactAdjunction
end CategoryTheory
