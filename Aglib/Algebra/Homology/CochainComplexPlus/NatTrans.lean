/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Additive

/-! # Natural transformations on bounded-below complexes -/


/-!
Source: `Quillen/Algebra/Homology/CochainComplexPlusNatTrans.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 42]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.NatTrans
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  {B : Type u'} [Category.{v'} B] [HasZeroMorphisms B]
  {F G : A ⥤ B} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
/-- An original natural transformation acts componentwise on bounded-below complexes. -/
def mapCochainComplexPlus (α : F ⟶ G) :
    F.mapCochainComplexPlus ⟶ G.mapCochainComplexPlus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((NatTrans.mapHomologicalComplex α (.up ℤ)).naturality f.hom)
/-- The termwise map retains each original component. -/
theorem mapCochainComplexPlus_app_f (α : F ⟶ G) (K : CochainComplex.Plus A) (n : ℤ) :
    ((mapCochainComplexPlus α).app K).hom.f n = α.app (K.obj.X n) := rfl
/-- The induced map preserves identity transformations. -/
theorem mapCochainComplexPlus_id (F : A ⥤ B) [F.PreservesZeroMorphisms] :
    mapCochainComplexPlus (𝟙 F) = 𝟙 F.mapCochainComplexPlus := rfl
/-- The induced map preserves the original composition of transformations. -/
theorem mapCochainComplexPlus_comp {H : A ⥤ B} [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    mapCochainComplexPlus (α ≫ β) = mapCochainComplexPlus α ≫ mapCochainComplexPlus β := rfl
/-- Invertibility of all original components gives invertibility on the actual complex. -/
theorem isIso_mapCochainComplexPlus_app (α : F ⟶ G) (K : CochainComplex.Plus A)
    (h : ∀ n, IsIso (α.app (K.obj.X n))) : IsIso ((mapCochainComplexPlus α).app K) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  have (n : ℤ) : IsIso (((mapCochainComplexPlus α).app K).hom.f n) := h n
  exact HomologicalComplex.Hom.isIso_of_components _
end CategoryTheory.NatTrans
