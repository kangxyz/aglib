/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Center.Linear

/-!
# Actual global scalar multiplication in the center of a module-sheaf category

For a sheaf of commutative rings and an initial object of the presheaf indexing category,
its sections act by original restriction followed by module scalar multiplication on every
module sheaf. These actual module-linear endomorphisms form a ring map to the native
category center. Mathlib's native construction then supplies the corresponding linear
category. Ring, module-carrier, site-object and site-morphism universes are independent.
No sheafification, quasicoherence or finiteness hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe r m c h

namespace SheafOfModules

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r}) (T : Cᵒᵖ) (hT : IsInitial T)

include hT

/-- Actual module-linear multiplication by a section on the initial presheaf object. -/
def scalarEndomorphismOfInitial
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (a : R.obj.obj T) : M ⟶ M where
  val.app U := ModuleCat.ofHom ((R.obj.map (hT.to U) a) •
    (LinearMap.id : M.val.obj U →ₗ[R.obj.obj U] M.val.obj U))
  val.naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (R.obj.map (hT.to V) a) • M.val.map f x =
      M.val.map f ((R.obj.map (hT.to U) a) • x)
    rw [M.val.map_smul]
    congr 1
    change R.obj.map (hT.to V) a = R.obj.map f (R.obj.map (hT.to U) a)
    have hcomp : hT.to U ≫ f = hT.to V := hT.hom_ext _ _
    rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp, hcomp]

/-- The endomorphism retains the original restriction and original module action on sections. -/
theorem scalarEndomorphismOfInitial_app
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (a : R.obj.obj T)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (scalarEndomorphismOfInitial R T hT M a).val.app U x =
      R.obj.map (hT.to U) a • x := rfl

/-- Original global scalar multiplication is natural in actual module-sheaf morphisms. -/
theorem scalarEndomorphismOfInitial_naturality
    {M N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (φ : M ⟶ N) (a : R.obj.obj T) :
    φ ≫ scalarEndomorphismOfInitial R T hT N a =
      scalarEndomorphismOfInitial R T hT M a ≫ φ := by
  ext U x
  change R.obj.map (hT.to U) a • φ.val.app U x =
    φ.val.app U (R.obj.map (hT.to U) a • x)
  exact ((φ.val.app U).hom.map_smul _ _).symm

/-- The actual ring map from initial-object sections to the native category center. -/
def scalarCenterOfInitial : R.obj.obj T →+*
    CatCenter (SheafOfModules.{m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) where
  toFun a := {
    app M := scalarEndomorphismOfInitial R T hT M a
    naturality := by
      intro M N φ
      exact scalarEndomorphismOfInitial_naturality R T hT φ a }
  map_zero' := by
    apply CatCenter.ext
    intro M
    ext U x
    change R.obj.map (hT.to U) 0 • x = 0
    rw [map_zero, zero_smul]
  map_one' := by
    apply CatCenter.ext
    intro M
    ext U x
    change R.obj.map (hT.to U) 1 • x = x
    rw [map_one, one_smul]
  map_add' a b := by
    apply CatCenter.ext
    intro M
    ext U x
    change R.obj.map (hT.to U) (a + b) • x =
      R.obj.map (hT.to U) a • x + R.obj.map (hT.to U) b • x
    rw [map_add, add_smul]
  map_mul' a b := by
    apply CatCenter.ext
    intro M
    ext U x
    change R.obj.map (hT.to U) (a * b) • x =
      R.obj.map (hT.to U) a • (R.obj.map (hT.to U) b • x)
    rw [map_mul, mul_smul]

/-- The native linear-category structure associated to original global scalar multiplication. -/
abbrev linearOfInitial : Linear (R.obj.obj T)
    (SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  Linear.ofRingMorphism (scalarCenterOfInitial R T hT)

/-- The induced scalar multiplication of morphisms uses the original component scalar action. -/
theorem linearOfInitial_smul_app
    {M N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (φ : M ⟶ N)
    (a : R.obj.obj T) (U : Cᵒᵖ) (x : M.val.obj U) :
    letI : Linear (R.obj.obj T)
      (SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      linearOfInitial R T hT
    (a • φ).val.app U x = R.obj.map (hT.to U) a • φ.val.app U x := by
  let : Linear (R.obj.obj T)
      (SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    linearOfInitial R T hT
  change φ.val.app U (R.obj.map (hT.to U) a • x) =
    R.obj.map (hT.to U) a • φ.val.app U x
  exact (φ.val.app U).hom.map_smul _ _

end SheafOfModules
