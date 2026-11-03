/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-! # The original mapped short-complex isomorphism from whole arrow equations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- Preserve the first two original objects and change the third by its supplied native iso.
Both arrow squares are proved before the original short complex is specialized. -/
def mappedPairIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B E : C} (f : A ⟶ B) (g : B ⟶ E) (hfg : f ≫ g = 0)
    {N : D} (e : F.obj E ≅ N)
    (a : F.obj A ⟶ F.obj B) (b : F.obj B ⟶ N) (hab : a ≫ b = 0)
    (hf : F.map f = a) (hg : F.map g ≫ e.hom = b) :
    (ShortComplex.mk f g hfg).map F ≅ ShortComplex.mk a b hab :=
  ShortComplex.isoMk (Iso.refl (F.obj A)) (Iso.refl (F.obj B)) e
    (by
      change 𝟙 (F.obj A) ≫ a = F.map f ≫ 𝟙 (F.obj B)
      simpa only [Category.id_comp, Category.comp_id] using hf.symm)
    (by
      change 𝟙 (F.obj B) ≫ b = F.map g ≫ e.hom
      simpa only [Category.id_comp] using hg.symm)

end CategoryTheory.ShortComplex
