/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections
/-!
# Original restriction squares and unit maps

The original restriction-composition and equal-morphism comparisons give the natural square
isomorphism. Its unit compatibility retains the actual ring-section maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

lemma restrictUnitIso_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.restrictUnitIso g).hom = (Scheme.Modules.restrictUnitIso f).hom := by
  subst g
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

variable {U V Y X : Scheme.{u}} (a : U ⟶ Y) (j : Y ⟶ X) (c : U ⟶ V) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c] [IsOpenImmersion b]
  (h : a ≫ j = c ≫ b)

/-- The original restriction comparison of a commuting square of open immersions. -/
def restrictionSquareIso :
    Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.restrictFunctor a ≅
      Scheme.Modules.restrictFunctor b ⋙ Scheme.Modules.restrictFunctor c :=
  (Scheme.Modules.restrictFunctorComp a j).symm ≪≫
    Scheme.Modules.restrictFunctorCongr h ≪≫ Scheme.Modules.restrictFunctorComp c b

lemma restrictionSquareIso_unit :
    (restrictionSquareIso a j c b h).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.restrictFunctor c).map (Scheme.Modules.restrictUnitIso b).hom ≫
      (Scheme.Modules.restrictUnitIso c).hom =
    (Scheme.Modules.restrictFunctor a).map (Scheme.Modules.restrictUnitIso j).hom ≫
      (Scheme.Modules.restrictUnitIso a).hom := by
  simp only [restrictionSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [restrictUnitIso_comp, restrictUnitIso_congr]
  rw [← restrictUnitIso_comp a j, Iso.inv_hom_id_app_assoc]

lemma restrictionSquareIso_unit_map {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (restrictionSquareIso a j c b h).hom.app M ≫
      (Scheme.Modules.restrictFunctor c).map
        ((Scheme.Modules.restrictFunctor b).map φ ≫ (Scheme.Modules.restrictUnitIso b).hom) ≫
      (Scheme.Modules.restrictUnitIso c).hom =
    (Scheme.Modules.restrictFunctor a).map
        ((Scheme.Modules.restrictFunctor j).map φ ≫ (Scheme.Modules.restrictUnitIso j).hom) ≫
      (Scheme.Modules.restrictUnitIso a).hom := by
  have hn := (restrictionSquareIso a j c b h).hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← hn, Category.assoc, Category.assoc,
    restrictionSquareIso_unit]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
