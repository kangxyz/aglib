/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.NormalizedRestrictionMap

/-! # Values of the original complete normalized scalar restriction map

These value laws retain the original constructors and Ext classes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace CategoryTheory.Functor
universe u v u' v' i j k l r w

/-- The complete normalized map acts by its original transfer and both source maps. -/
theorem extScalarNormalizedRestrictionMap_apply
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{max r w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{max r w} D]
    {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (P : I ⥤ J) (e : F ⋙ L ≅ P ⋙ G)
    {R : Type r} [CommRing R] (A : C) (B : D)
    (ρ : R →+* End A) (τ : R →+* End B)
    (φ : L.obj A ⟶ B) (hφ : ∀ a : R, L.map (ρ a) ≫ φ = φ ≫ τ a)
    (n : ℕ) (a : Iᵒᵖ) {b : Jᵒᵖ} (κ : P.op.obj a ⟶ b)
    {Z : D} (eZ : G.obj b.unop ≅ Z)
    (x : Ext.{max r w} (F.obj a.unop) A n) :
    L.extScalarNormalizedRestrictionMap F G P e A B ρ τ φ hφ n a κ eZ x =
      (Ext.mk₀ eZ.inv).comp
        ((Ext.mk₀ (G.map κ.unop)).comp
          (L.extCoefficientTransfer (e.inv.app a.unop) φ n x) (Nat.zero_add n))
        (Nat.zero_add n) := by
  change ((𝟭 D).extModuleDiagram B τ n).map eZ.inv.op
      ((G.extModuleDiagram B τ n).map κ
        ((L.extScalarDiagramMap F G P e (RingHom.id R) A B ρ τ φ hφ n).app a x)) = _
  rw [extModuleDiagram_map_apply, extModuleDiagram_map_apply, extScalarDiagramMap_apply]
  rfl

end CategoryTheory.Functor
