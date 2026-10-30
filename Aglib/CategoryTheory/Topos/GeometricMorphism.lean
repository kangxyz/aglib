/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LeftExact
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Ordinary geometric-morphism language on actual categories

The data are the existing single left-exact adjunction, with its actual
functors, unit and counit. They have geometric-morphism interpretation when
the actual categories are topoi; no topos-existence assertion is made here.

Composition follows geometric direction. Two-morphisms are native direct-
image natural transformations, conjugate to reverse inverse-image natural
transformations. Squares and their mates are the native `TwoSquare` and
`mateEquiv`; their existing identity and pasting laws apply without a second
square construction. No exchange map is asserted to be invertible.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Topos

universe uE vE uF vF uG vG uH vH

/-- Native left-exact adjunction data directed from the actual category `E` to `F`.
These are geometric-morphism data when the actual categories are topoi. -/
abbrev GeometricMorphism (E : Type uE) [Category.{vE} E]
    (F : Type uF) [Category.{vF} F] :=
  LeftExactAdjunction F E

namespace GeometricMorphism

variable {E : Type uE} [Category.{vE} E] {F : Type uF} [Category.{vF} F]
  {G : Type uG} [Category.{vG} G] {H : Type uH} [Category.{vH} H]

/-- The original inverse-image functor. -/
abbrev inverseImage (f : GeometricMorphism E F) : F ⥤ E := f.left.obj

/-- The original direct-image functor. -/
abbrev directImage (f : GeometricMorphism E F) : E ⥤ F := f.right

/-- The original adjunction, including its literal unit and counit. -/
abbrev adjunction (f : GeometricMorphism E F) : inverseImage f ⊣ directImage f := f.adj

/-- Identity in geometric direction is the native identity adjunction. -/
def id (E : Type uE) [Category.{vE} E] : GeometricMorphism E E :=
  LeftExactAdjunction.id E

@[simp]
theorem id_inverseImage : inverseImage (id E) = 𝟭 E := rfl

@[simp]
theorem id_directImage : directImage (id E) = 𝟭 E := rfl

@[simp]
theorem id_unit_app (X : E) : (adjunction (id E)).unit.app X = 𝟙 X := rfl

@[simp]
theorem id_counit_app (X : E) : (adjunction (id E)).counit.app X = 𝟙 X := rfl

/-- Compose E to F and F to G in geometric direction, using the original adjunctions. -/
def comp (f : GeometricMorphism E F) (g : GeometricMorphism F G) :
    GeometricMorphism E G :=
  LeftExactAdjunction.comp g f

@[simp]
theorem comp_inverseImage (f : GeometricMorphism E F) (g : GeometricMorphism F G) :
    inverseImage (comp f g) = inverseImage g ⋙ inverseImage f := rfl

@[simp]
theorem comp_directImage (f : GeometricMorphism E F) (g : GeometricMorphism F G) :
    directImage (comp f g) = directImage f ⋙ directImage g := rfl

@[simp]
theorem comp_adjunction (f : GeometricMorphism E F) (g : GeometricMorphism F G) :
    adjunction (comp f g) = (adjunction g).comp (adjunction f) := rfl

/-- The native composite unit, with the geometric ordering of the two adjunctions. -/
theorem comp_unit_app (f : GeometricMorphism E F) (g : GeometricMorphism F G) (X : G) :
    (adjunction (comp f g)).unit.app X =
      (adjunction g).unit.app X ≫
        (directImage g).map ((adjunction f).unit.app ((inverseImage g).obj X)) :=
  LeftExactAdjunction.comp_unit_app g f X

/-- The native composite counit, with no reselected adjunction. -/
theorem comp_counit_app (f : GeometricMorphism E F) (g : GeometricMorphism F G) (X : E) :
    (adjunction (comp f g)).counit.app X =
      (inverseImage f).map ((adjunction g).counit.app ((directImage f).obj X)) ≫
        (adjunction f).counit.app X :=
  LeftExactAdjunction.comp_counit_app g f X

/-- An actual equivalence in geometric direction uses its native opposite adjunction. -/
def ofEquivalence (e : E ≌ F) : GeometricMorphism E F :=
  LeftExactAdjunction.ofEquivalence e.symm

@[simp]
theorem ofEquivalence_inverseImage (e : E ≌ F) :
    inverseImage (ofEquivalence e) = e.inverse := rfl

@[simp]
theorem ofEquivalence_directImage (e : E ≌ F) :
    directImage (ofEquivalence e) = e.functor := rfl

@[simp]
theorem ofEquivalence_adjunction (e : E ≌ F) :
    adjunction (ofEquivalence e) = e.symm.toAdjunction := rfl

theorem ofEquivalence_unit (e : E ≌ F) :
    (adjunction (ofEquivalence e)).unit = e.counitInv := rfl

theorem ofEquivalence_counit (e : E ≌ F) :
    (adjunction (ofEquivalence e)).counit = e.unitInv := rfl

/-- A two-morphism is the native direct-image natural transformation. -/
abbrev TwoMorphism (f g : GeometricMorphism E F) := directImage f ⟶ directImage g

/-- Native conjugation views two-morphisms as reverse inverse-image transformations. -/
abbrev conjugateEquiv (f g : GeometricMorphism E F) :
    (inverseImage g ⟶ inverseImage f) ≃ TwoMorphism f g :=
  CategoryTheory.conjugateEquiv (adjunction f) (adjunction g)

/-- The two-morphism view retains the original units. -/
theorem conjugateEquiv_unit (f g : GeometricMorphism E F)
    (α : inverseImage g ⟶ inverseImage f) (X : F) :
    (adjunction f).unit.app X ≫ (conjugateEquiv f g α).app ((inverseImage f).obj X) =
      (adjunction g).unit.app X ≫ (directImage g).map (α.app X) :=
  CategoryTheory.unit_conjugateEquiv (adjunction f) (adjunction g) α X

/-- The two-morphism view retains the original counits. -/
theorem conjugateEquiv_counit (f g : GeometricMorphism E F)
    (α : inverseImage g ⟶ inverseImage f) (X : E) :
    (inverseImage g).map ((conjugateEquiv f g α).app X) ≫ (adjunction g).counit.app X =
      α.app ((directImage f).obj X) ≫ (adjunction f).counit.app X :=
  CategoryTheory.conjugateEquiv_counit (adjunction f) (adjunction g) α X

/-- The square mate is the native equivalence on the original TwoSquare frame. -/
abbrev mateEquiv (f : GeometricMorphism E F) (g : GeometricMorphism G H)
    (a : F ⥤ H) (b : E ⥤ G) :
    TwoSquare a (inverseImage f) (inverseImage g) b ≃
      TwoSquare (directImage f) b a (directImage g) :=
  CategoryTheory.mateEquiv (adjunction f) (adjunction g)

/-- Its component is the actual target unit, square, and source counit. -/
theorem mateEquiv_app (f : GeometricMorphism E F) (g : GeometricMorphism G H)
    (a : F ⥤ H) (b : E ⥤ G) (α : TwoSquare a (inverseImage f) (inverseImage g) b) (X : E) :
    (mateEquiv f g a b α).app X =
      (adjunction g).unit.app (a.obj ((directImage f).obj X)) ≫
        (directImage g).map (α.app ((directImage f).obj X)) ≫
          (directImage g).map (b.map ((adjunction f).counit.app X)) :=
  CategoryTheory.mateEquiv_app_eq (adjunction f) (adjunction g) α X

/-- The native counit equation determines this same square mate. -/
theorem eq_mateEquiv_iff (f : GeometricMorphism E F) (g : GeometricMorphism G H)
    (a : F ⥤ H) (b : E ⥤ G) (α : TwoSquare a (inverseImage f) (inverseImage g) b)
    (β : directImage f ⋙ a ⟶ b ⋙ directImage g) :
    β = (mateEquiv f g a b α).natTrans ↔
      ∀ X : E, (inverseImage g).map (β.app X) ≫ (adjunction g).counit.app (b.obj X) =
        α.app ((directImage f).obj X) ≫ b.map ((adjunction f).counit.app X) :=
  CategoryTheory.eq_mateEquiv_iff (adjunction f) (adjunction g) α β

end GeometricMorphism
end CategoryTheory.Topos
