/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma

/-!
# Naturality of native exact postcomposition

This leaf extends, rather than replaces, the existing exact-postcomposition
comparison. Naturality in the exact target functor supplies restriction maps
when that target functor is evaluation of a presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]
  (F : C ⥤ D) [F.Additive]
  {G H : D ⥤ E} [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology] (τ : G ⟶ H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact postcomposition is natural in its original target natural transformation. -/
@[reassoc]
theorem rightDerivedPostcompIso_hom_natTrans (n : ℕ) (X : C) :
    ((Functor.whiskerLeft F τ).rightDerived n).app X ≫
        (rightDerivedPostcompIso F H n).hom.app X =
      (rightDerivedPostcompIso F G n).hom.app X ≫ τ.app ((F.rightDerived n).obj X) := by
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h : homologyMap
      ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F τ) (.up ℕ)).app I.cocomplex) n ≫
        (cochainHomologyPostcompIso H n).hom.app K =
      (cochainHomologyPostcompIso G n).hom.app K ≫ τ.app (K.homology n) := by
    change ShortComplex.homologyMap ((K.sc n).mapNatTrans τ) ≫
        ((K.sc n).mapHomologyIso H).hom =
      ((K.sc n).mapHomologyIso G).hom ≫ τ.app (K.sc n).homology
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [InjectiveResolution.rightDerived_app_eq (Functor.whiskerLeft F τ) I n]
  dsimp only [rightDerivedPostcompIso, rightDerivedPostcompObjIso,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  change (I.isoRightDerivedObj (F ⋙ G) n).hom ≫
      homologyMap
        ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F τ) (.up ℕ)).app
          I.cocomplex) n ≫
      (I.isoRightDerivedObj (F ⋙ H) n).inv ≫
      (I.isoRightDerivedObj (F ⋙ H) n).hom ≫
      (cochainHomologyPostcompIso H n).hom.app K ≫
      H.map (I.isoRightDerivedObj F n).inv =
    (I.isoRightDerivedObj (F ⋙ G) n).hom ≫
      (cochainHomologyPostcompIso G n).hom.app K ≫
      G.map (I.isoRightDerivedObj F n).inv ≫ τ.app ((F.rightDerived n).obj X)
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    (homologyMap
      ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F τ) (.up ℕ)).app
        I.cocomplex) n)
    ((cochainHomologyPostcompIso H n).hom.app K), h]
  simp only [Category.assoc]
  rw [τ.naturality]
  rfl

end CategoryTheory.Sheaf.ModuleCoefficients
