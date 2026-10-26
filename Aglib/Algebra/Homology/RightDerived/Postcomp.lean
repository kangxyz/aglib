/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Exact postcomposition for natural-degree right-derived functors

These are the original category-level constructors extracted from
`CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma`.
They retain the chosen injective resolutions and the original homology maps.
No site, coefficient module, or derived-category model is assumed.
-/

@[expose] public noncomputable section

universe u v u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor

section Abstract

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

/-- Exact postcomposition commutes with the actual homology of a cochain complex. -/
def cochainHomologyPostcompIso (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
    (n : ℕ) :
    G.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor E _ n ≅
      HomologicalComplex.homologyFunctor D _ n ⋙ G :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso G) (by
    intro K L f
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor D (.up ℕ) n).map f) G)

/-- The canonical comparison for deriving a natural isomorphism of additive functors. -/
def rightDerivedNatIsoOfAdditive {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

/-- Compute exact postcomposition on the original chosen injective resolution. -/
def rightDerivedPostcompObjIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (n : ℕ) (X : C) :
    ((F ⋙ G).rightDerived n).obj X ≅ G.obj ((F.rightDerived n).obj X) :=
  (injectiveResolution X).isoRightDerivedObj (F ⋙ G) n ≪≫
    (cochainHomologyPostcompIso G n).app
      ((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex) ≪≫
    G.mapIso ((injectiveResolution X).isoRightDerivedObj F n).symm

/-- Exact postcomposition commutes naturally with native right-derived functors. -/
def rightDerivedPostcompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G :=
  NatIso.ofComponents (rightDerivedPostcompObjIso F G n) (by
    intro X Y f
    let φ := InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)
    have hφ := InjectiveResolution.desc_commutes_zero f
      (injectiveResolution Y) (injectiveResolution X)
    have h₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality f
      (injectiveResolution X) (injectiveResolution Y) φ hφ (F ⋙ G) n
    have h₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality f
      (injectiveResolution X) (injectiveResolution Y) φ hφ F n
    have h₃ := (cochainHomologyPostcompIso G n).hom.naturality
      ((F.mapHomologicalComplex _).map φ)
    change ((F ⋙ G).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor E _ n).map φ ≫ _ = _ at h₃
    dsimp only [rightDerivedPostcompObjIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.comp_map]
    rw [← Category.assoc, ← Category.assoc, h₁]
    have h₄ := congrArg (fun k =>
      ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).hom ≫ k ≫
        G.map ((injectiveResolution Y).isoRightDerivedObj F n).inv) h₃
    have h₅ := congrArg (fun k =>
      ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (cochainHomologyPostcompIso G n).hom.app
          ((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex) ≫
        G.map k) h₂
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at h₄ h₅
    simpa only [Functor.comp_map, Iso.app_hom, Category.assoc] using h₄.trans h₅.symm)

end Abstract

end CategoryTheory.Functor
