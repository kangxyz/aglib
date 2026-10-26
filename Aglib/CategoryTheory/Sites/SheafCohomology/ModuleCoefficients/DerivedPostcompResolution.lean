/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma
public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Aglib.Algebra.Homology.Embedding.MapExtend.Homology

/-! # Exact postcomposition on the original resolution complexes

The existing exact-postcomposition comparison is computed on any supplied
injective resolution, including its original extension to integer degrees.
No new comparison map is defined, and no derived-category model is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [G.PreservesHomology]
  {M : C} (I : InjectiveResolution M) (n : ℕ)

/-- The native exact-postcomposition map retains any supplied natural-degree
resolution, not only the resolution chosen in its definition. -/
theorem rightDerivedPostcompIso_hom_resolution :
    (rightDerivedPostcompIso F G n).hom.app M ≫ G.map (I.isoRightDerivedObj F n).hom =
      (I.isoRightDerivedObj (F ⋙ G) n).hom ≫
        (cochainHomologyPostcompIso G n).hom.app
          ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) := by
  let I₀ := injectiveResolution M
  let φ := InjectiveResolution.desc (𝟙 M) I I₀
  have hφ := InjectiveResolution.desc_commutes_zero (𝟙 M) I I₀
  have hF := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 M) I₀ I φ hφ F n
  have hFG := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 M) I₀ I φ hφ (F ⋙ G) n
  simp only [Functor.map_id, Category.id_comp, Functor.comp_map] at hF hFG
  have hG := (cochainHomologyPostcompIso G n).hom.naturality
    ((F.mapHomologicalComplex (.up ℕ)).map φ)
  simp only [Functor.comp_map] at hG
  rw [hF, G.map_comp]
  dsimp only [rightDerivedPostcompIso, rightDerivedPostcompObjIso,
    CategoryTheory.Functor.rightDerivedPostcompIso,
    CategoryTheory.Functor.rightDerivedPostcompObjIso,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp]
  simp only [Iso.app_hom]
  rw [← hG, ← Category.assoc]
  exact congrArg (fun k => k ≫ (cochainHomologyPostcompIso G n).hom.app
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)) hFG.symm

/-- The same original map commutes with the original integer-resolution
comparison and the native homology isomorphism for exact postcomposition. -/
theorem rightDerivedPostcompIso_hom_resolution_cochain :
    (rightDerivedPostcompIso F G n).hom.app M ≫
        G.map (I.isoRightDerivedObjCochain F n).hom =
      (I.isoRightDerivedObjCochain (F ⋙ G) n).hom ≫
        ((((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc (n : ℤ)).mapHomologyIso
          G).hom := by
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let eF := I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat
  let eG := K.mapExtendIso G ComplexShape.embeddingUpNat
  let eFG := I.cocomplex.mapExtendIso (F ⋙ G) ComplexShape.embeddingUpNat
  let hF := K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let hFG := ((G.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let H := homologyFunctor E (.up ℤ) (n : ℤ)
  have he : H.map eFG.hom =
      H.map ((G.mapHomologicalComplex (.up ℤ)).map eF.hom) ≫ H.map eG.hom := by
    simpa only [Functor.map_comp] using congrArg H.map
      (I.cocomplex.mapExtendIso_hom_comp F G ComplexShape.embeddingUpNat)
  have hi : H.map eFG.inv ≫
      H.map ((G.mapHomologicalComplex (.up ℤ)).map eF.hom) = H.map eG.inv := by
    apply (cancel_mono (H.map eG.hom)).mp
    rw [Category.assoc, ← he, ← H.map_comp, Iso.inv_hom_id, H.map_id,
      ← H.map_comp, Iso.inv_hom_id, H.map_id]
    rfl
  have hn : H.map ((G.mapHomologicalComplex (.up ℤ)).map eF.hom) ≫
      (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso G).hom =
    ((((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc (n : ℤ)).mapHomologyIso
      G).hom ≫
      G.map (homologyMap eF.hom (n : ℤ)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor D (.up ℤ) (n : ℤ)).map eF.hom) G
  have hh : H.map eG.hom ≫ hFG.hom ≫ ((K.sc n).mapHomologyIso G).hom =
      (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso G).hom ≫
        G.map hF.hom :=
    K.mapExtendIso_hom_homologyMap G ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl
  apply (cancel_mono
    (G.map (homologyMap eF.hom (n : ℤ)) ≫ G.map hF.hom)).mp
  simp only [InjectiveResolution.isoRightDerivedObjCochain_hom,
    G.map_comp, Category.assoc]
  change (rightDerivedPostcompIso F G n).hom.app M ≫
      G.map (I.isoRightDerivedObj F n).hom ≫ G.map hF.inv ≫
        G.map (homologyMap eF.inv (n : ℤ)) ≫
        G.map (homologyMap eF.hom (n : ℤ)) ≫ G.map hF.hom =
    (I.isoRightDerivedObj (F ⋙ G) n).hom ≫ hFG.inv ≫ H.map eFG.inv ≫
      ((((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc (n : ℤ)).mapHomologyIso
      G).hom ≫
        G.map (homologyMap eF.hom (n : ℤ)) ≫ G.map hF.hom
  have hc : G.map (homologyMap eF.inv (n : ℤ)) ≫
      G.map (homologyMap eF.hom (n : ℤ)) = 𝟙 _ := by
    rw [← G.map_comp, ← homologyMap_comp, Iso.inv_hom_id, homologyMap_id, G.map_id]
  rw [reassoc_of% hc, ← G.map_comp, Iso.inv_hom_id, G.map_id,
    Category.comp_id]
  rw [← reassoc_of% hn, reassoc_of% hi, ← hh]
  rw [← H.map_comp_assoc, Iso.inv_hom_id, H.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc]
  exact rightDerivedPostcompIso_hom_resolution F G I n

end CategoryTheory.Sheaf.ModuleCoefficients
