/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Complex
public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.LocalizedConjugacy

/-! # Actual conjugacy of original comparisons on bounded-below complexes -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction
open CategoryTheory.Functor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [L₀.Additive] [R₀.Additive]

/-- Original conjugate composition comparisons remain conjugate on actual complexes. -/
theorem mapCochainComplexPlus_conjugate_comp
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₀ : L₀ ⊣ R₀)
    (eL : L₀ ≅ L₁ ⋙ L₂) (eR : R₂ ⋙ R₁ ≅ R₀)
    (h : conjugateEquiv (adj₁.comp adj₂) adj₀ eL.hom = eR.hom) :
    conjugateEquiv (adj₁.mapCochainComplexPlus.comp adj₂.mapCochainComplexPlus)
        adj₀.mapCochainComplexPlus
        ((NatIso.mapCochainComplexPlus eL) ≪≫ mapCochainComplexPlusCompIso L₁ L₂).hom =
      ((mapCochainComplexPlusCompIso R₂ R₁).symm ≪≫
        NatIso.mapCochainComplexPlus eR).hom := by
  apply conjugateEquiv_eq_of_unit
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [comp_unit_app]
  apply ObjectProperty.hom_ext
  ext n
  change (adj₁.unit.app (K.obj.X n) ≫ R₁.map (adj₂.unit.app (L₁.obj (K.obj.X n)))) ≫
      (𝟙 _ ≫ eR.hom.app (L₂.obj (L₁.obj (K.obj.X n)))) =
    adj₀.unit.app (K.obj.X n) ≫ R₀.map (eL.hom.app (K.obj.X n) ≫ 𝟙 _)
  have hu := unit_conjugateEquiv (adj₁.comp adj₂) adj₀ eL.hom (K.obj.X n)
  rw [h] at hu
  simpa only [Category.id_comp, Category.comp_id, comp_unit_app, Functor.comp_obj] using hu

end CategoryTheory.Adjunction
