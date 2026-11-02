/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.Transfer

/-! # The original normalized scalar restriction map

Construct the original scalar transfer, index map and source comparison once.
The normalized restriction square and its geometric consumers use this map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace CategoryTheory.Functor
universe u v u' v' i j k l r w

/-- The unchanged scalar transfer followed by the original index and source iso. -/
def extScalarNormalizedRestrictionMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{max r w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{max r w} D]
    {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (P : I ⥤ J) (e : F ⋙ L ≅ P ⋙ G)
    {R : Type r} [CommRing R] (A : C) (B : D)
    (ρ : R →+* End A) (τ : R →+* End B)
    (φ : L.obj A ⟶ B) (hφ : ∀ a : R, L.map (ρ a) ≫ φ = φ ≫ τ a)
    (n : ℕ) (a : Iᵒᵖ) {b : Jᵒᵖ} (κ : P.op.obj a ⟶ b)
    {Z : D} (eZ : G.obj b.unop ≅ Z) :
    (F.extModuleDiagram A ρ n).obj a ⟶
      (ModuleCat.restrictScalars (RingHom.id R)).obj
        (((𝟭 D).extModuleDiagram B τ n).obj (op Z)) :=
  (L.extScalarDiagramMap F G P e (RingHom.id R) A B ρ τ φ hφ n).app a ≫
    (ModuleCat.restrictScalars (RingHom.id R)).map
      ((G.extModuleDiagram B τ n).map κ) ≫
    (ModuleCat.restrictScalars (RingHom.id R)).map
      (((𝟭 D).extModuleDiagram B τ n).map eZ.inv.op)

end CategoryTheory.Functor
