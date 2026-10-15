/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Additive
/-! # Original bounded-below complex functors under natural isomorphism and composition -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe v u v' u' v'' u''
namespace CategoryTheory
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]
  {F F' : A ⥤ B} [F.Additive] [F'.Additive]

/-- An original functor isomorphism induces its actual componentwise isomorphism
on bounded-below complexes. -/
def NatIso.mapCochainComplexPlus (e : F ≅ F') :
    F.mapCochainComplexPlus ≅ F'.mapCochainComplexPlus :=
  NatIso.ofComponents (fun K ↦ (CochainComplex.plus B).isoMk
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (NatIso.mapHomologicalComplex e (.up ℤ)).hom.naturality f.hom)

variable {C : Type u''} [Category.{v''} C] [Preadditive C]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]

/-- Composition of the original bounded-below termwise functors retains the actual complexes. -/
def Functor.mapCochainComplexPlusCompIso :
    (F ⋙ G).mapCochainComplexPlus ≅ F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl)

end CategoryTheory
