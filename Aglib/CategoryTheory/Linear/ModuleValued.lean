/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Canonical scalars on additive functor values

An additive functor from an `R`-linear category to abelian groups canonically
lifts to `R`-modules. The carrier and additive maps are unchanged: multiplication
by `r` is the image of the original coefficient endomorphism `r • 𝟙 X`.
The lift is linear. This supplies scalars on original sheaf cohomology without
replacing its cohomology objects or choosing a resolution comparison.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe r u v w

variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear R C]
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]

/-- The original scalar endomorphisms act on the unchanged additive functor value. -/
@[instance_reducible]
def moduleObj (X : C) : Module R (F.obj X) where
  smul r x := F.map (r • 𝟙 X) x
  one_smul x := by
    change F.map ((1 : R) • 𝟙 X) x = x
    simp
  mul_smul r s x := by
    have h : (r * s) • 𝟙 X = (s • 𝟙 X) ≫ (r • 𝟙 X) := by
      simp [smul_smul]
    change F.map ((r * s) • 𝟙 X) x = F.map (r • 𝟙 X) (F.map (s • 𝟙 X) x)
    rw [h, F.map_comp]
    rfl
  smul_zero r := (F.map (r • 𝟙 X)).hom.map_zero
  smul_add r x y := (F.map (r • 𝟙 X)).hom.map_add x y
  add_smul r s x := by
    change F.map ((r + s) • 𝟙 X) x = _
    rw [add_smul, F.map_add]
    rfl
  zero_smul x := by
    change F.map ((0 : R) • 𝟙 X) x = 0
    simp

attribute [local instance] moduleObj

/-- The canonical scalar action is literally the original functor map. -/
@[simp]
theorem moduleObj_smul (X : C) (r : R) (x : F.obj X) :
    r • x = F.map (r • 𝟙 X) x := rfl

/-- Every original additive coefficient map is linear for the canonical action. -/
def moduleMap {X Y : C} (f : X ⟶ Y) : F.obj X →ₗ[R] F.obj Y where
  toAddHom := (F.map f).hom
  map_smul' r x := by
    change F.map f (F.map (r • 𝟙 X) x) = F.map (r • 𝟙 Y) (F.map f x)
    have h : F.map (r • 𝟙 X) ≫ F.map f = F.map f ≫ F.map (r • 𝟙 Y) := by
      simp only [← F.map_comp, CategoryTheory.Linear.smul_comp,
        CategoryTheory.Linear.comp_smul, Category.id_comp, Category.comp_id]
    exact ConcreteCategory.congr_hom h x

/-- The canonical module-valued lift retains the actual additive objects and maps. -/
def moduleValued : C ⥤ ModuleCat.{w} R where
  obj X := ModuleCat.of R (F.obj X)
  map f := ModuleCat.ofHom (moduleMap R F f)
  map_id X := by
    ext x
    exact ConcreteCategory.congr_hom (F.map_id X) x
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom (F.map_comp f g) x

/-- The lifted map has the original underlying function. -/
@[simp]
theorem moduleValued_map_apply {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    (moduleValued R F).map f x = F.map f x := rfl

instance moduleValued_additive : (moduleValued R F).Additive where
  map_add := by
    intro X Y f g
    ext x
    exact ConcreteCategory.congr_hom (F.map_add (f := f) (g := g)) x

instance moduleValued_linear : (moduleValued R F).Linear R where
  map_smul f r := by
    ext x
    change F.map (r • f) x = F.map (r • 𝟙 _) (F.map f x)
    have h : r • f = f ≫ (r • 𝟙 _) := by simp
    rw [h, F.map_comp]
    rfl

/-- Forgetting canonical scalars is naturally the original additive functor;
its components are identities on the original carriers. -/
def moduleValuedForgetIso :
    moduleValued R F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ≅ F :=
  NatIso.ofComponents (fun X => (AddEquiv.refl (F.obj X)).toAddCommGrpIso) (by
    intro X Y f
    ext x
    rfl)

end CategoryTheory.Functor
