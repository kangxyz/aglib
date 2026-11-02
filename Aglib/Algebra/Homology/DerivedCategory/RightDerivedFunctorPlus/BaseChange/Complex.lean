/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Complex
public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-!
# Native mates on bounded-below complexes

The original square and its native mate act degreewise on bounded-below complexes.
The comparison retains the actual termwise composition isomorphisms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {L₂ : C ⥤ D}
  [G.Additive] [H.Additive] [L₁.Additive] [L₂.Additive]

/-- A square acts on complexes through the native termwise composition comparisons. -/
def TwoSquare.mapCochainComplexPlus (α : TwoSquare G L₁ L₂ H) :
    TwoSquare G.mapCochainComplexPlus L₁.mapCochainComplexPlus
      L₂.mapCochainComplexPlus H.mapCochainComplexPlus :=
  TwoSquare.mk _ _ _ _
    ((Functor.mapCochainComplexPlusCompIso G L₂).inv ≫
      α.natTrans.mapCochainComplexPlus ≫ (Functor.mapCochainComplexPlusCompIso L₁ H).hom)

variable {R₁ : B ⥤ A} {R₂ : D ⥤ C} [R₁.Additive] [R₂.Additive]

/-- Taking the native mate commutes with the actual degreewise complex construction. -/
theorem mateEquiv_mapCochainComplexPlus (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) :
    (mateEquiv adj₁.mapCochainComplexPlus adj₂.mapCochainComplexPlus
      α.mapCochainComplexPlus).natTrans =
        ((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).natTrans := by
  symm
  apply (eq_mateEquiv_iff adj₁.mapCochainComplexPlus adj₂.mapCochainComplexPlus
    α.mapCochainComplexPlus _).2
  intro K
  apply ObjectProperty.hom_ext
  ext n
  change L₂.map (𝟙 _ ≫ (mateEquiv adj₁ adj₂ α).app (K.obj.X n) ≫ 𝟙 _) ≫
      adj₂.counit.app (H.obj (K.obj.X n)) =
    (𝟙 _ ≫ α.app (R₁.obj (K.obj.X n)) ≫ 𝟙 _) ≫ H.map (adj₁.counit.app (K.obj.X n))
  simpa only [Category.id_comp, Category.comp_id] using
    mateEquiv_counit adj₁ adj₂ α (K.obj.X n)

end CategoryTheory
