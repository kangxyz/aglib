/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
/-! # Original short exact complex triangles in D+

Lift Mathlib's canonical short-exact-complex triangle through the fully faithful
bounded-below inclusion. The incidence, quotient, cone sign, and connecting map
are retained. No choice of injective resolution is needed for this construction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Pretriangulated
namespace DerivedCategory.Plus
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex (CochainComplex.Plus C)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)

/-- The canonical original short-exact-complex triangle inside D+. -/
def triangleOfSESPlus : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk (DerivedCategory.Plus.Q.map S.f) (DerivedCategory.Plus.Q.map S.g)
    (DerivedCategory.Plus.ι.preimage
      (DerivedCategory.triangleOfSESδ hS ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
          (DerivedCategory.Plus.Q.obj S.X₁)))

/-- Forgetting the bound gives the literal original Mathlib short-exact-complex triangle. -/
def triangleOfSESPlusιIso :
    DerivedCategory.Plus.ι.mapTriangle.obj (triangleOfSESPlus hS) ≅
      DerivedCategory.triangleOfSES hS := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [triangleOfSESPlus, Functor.mapTriangle, DerivedCategory.triangleOfSES]
    rfl
  · simp [triangleOfSESPlus, Functor.mapTriangle, DerivedCategory.triangleOfSES]
    rfl
  · simp only [Functor.mapTriangle_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      Triangle.mk_obj₃, DerivedCategory.triangleOfSES_obj₁, Triangle.mk_obj₁,
      Triangle.mk_mor₃, Iso.refl_hom,
      DerivedCategory.triangleOfSES_obj₃, DerivedCategory.triangleOfSES_mor₃,
      Category.id_comp]
    dsimp only [triangleOfSESPlus, Triangle.mk_mor₃, Triangle.mk_obj₁]
    erw [(shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id
      ((DerivedCategory.Plus.Q.obj S.X₁).obj), Category.comp_id]
    change (DerivedCategory.Plus.ι (C := C)).map
      ((DerivedCategory.Plus.ι (C := C)).preimage _) ≫ _ = _
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _


/-- The triangle with original arrows and cone connecting map is distinguished in D+. -/
theorem triangleOfSESPlus_distinguished :
    triangleOfSESPlus hS ∈ distTriang (DerivedCategory.Plus C) := by
  apply DerivedCategory.Plus.ι.map_distinguished_iff _ |>.mp
  exact isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (triangleOfSESPlusιIso hS)

variable {S₁ S₂ : ShortComplex (CochainComplex.Plus C)}
  (h₁ : (S₁.map (CochainComplex.Plus.ι C)).ShortExact)
  (h₂ : (S₂.map (CochainComplex.Plus.ι C)).ShortExact) (f : S₁ ⟶ S₂)

/-- Chain maps of original sequences induce the actual connecting-morphism square. -/
def triangleOfSESPlusMap : triangleOfSESPlus h₁ ⟶ triangleOfSESPlus h₂ :=
  DerivedCategory.Plus.ι.mapTriangle.preimage
    ((triangleOfSESPlusιIso h₁).hom ≫
      DerivedCategory.triangleOfSES.map h₁ h₂
        ((CochainComplex.Plus.ι C).mapShortComplex.map f) ≫
      (triangleOfSESPlusιIso h₂).inv)

@[simp] theorem triangleOfSESPlusMap_hom₁ :
    (triangleOfSESPlusMap h₁ h₂ f).hom₁ = DerivedCategory.Plus.Q.map f.τ₁ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₁
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      ((triangleOfSESPlusιIso h₁).hom ≫
        DerivedCategory.triangleOfSES.map h₁ h₂
          ((CochainComplex.Plus.ι C).mapShortComplex.map f) ≫
        (triangleOfSESPlusιIso h₂).inv))
  refine h.trans ?_
  dsimp [triangleOfSESPlusιIso]
  simp only [Category.id_comp]
  change DerivedCategory.Q.map f.τ₁.hom ≫ 𝟙 _ = DerivedCategory.Q.map f.τ₁.hom
  exact Category.comp_id _

@[simp] theorem triangleOfSESPlusMap_hom₂ :
    (triangleOfSESPlusMap h₁ h₂ f).hom₂ = DerivedCategory.Plus.Q.map f.τ₂ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₂
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      ((triangleOfSESPlusιIso h₁).hom ≫
        DerivedCategory.triangleOfSES.map h₁ h₂
          ((CochainComplex.Plus.ι C).mapShortComplex.map f) ≫
        (triangleOfSESPlusιIso h₂).inv))
  refine h.trans ?_
  dsimp [triangleOfSESPlusιIso]
  simp only [Category.id_comp]
  change DerivedCategory.Q.map f.τ₂.hom ≫ 𝟙 _ = DerivedCategory.Q.map f.τ₂.hom
  exact Category.comp_id _

@[simp] theorem triangleOfSESPlusMap_hom₃ :
    (triangleOfSESPlusMap h₁ h₂ f).hom₃ = DerivedCategory.Plus.Q.map f.τ₃ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₃
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      ((triangleOfSESPlusιIso h₁).hom ≫
        DerivedCategory.triangleOfSES.map h₁ h₂
          ((CochainComplex.Plus.ι C).mapShortComplex.map f) ≫
        (triangleOfSESPlusιIso h₂).inv))
  refine h.trans ?_
  dsimp [triangleOfSESPlusιIso]
  simp only [Category.id_comp]
  change DerivedCategory.Q.map f.τ₃.hom ≫ 𝟙 _ = DerivedCategory.Q.map f.τ₃.hom
  exact Category.comp_id _
end DerivedCategory.Plus
