/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Native homology of exact coproducts

Exact discrete colimits commute with the original homology of arbitrary
homological complexes. The comparison below uses the native homology
comparison for the colimit functor. Its normalization retains the original
coproduct inclusions and the actual induced maps on homology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {κ : Type w} {ι : Type w'} {c : ComplexShape ι}
  (K : κ → HomologicalComplex C c)

/-- The original family of complexes, viewed as a complex of discrete diagrams. -/
def coproductDiagram : HomologicalComplex (Discrete κ ⥤ C) c where
  X i := Discrete.functor K ⋙ eval C c i
  d i j :=
    { app a := (K a.as).d i j
      naturality a b f := ((Discrete.functor K).map f).comm i j }
  shape i j hij := by
    ext a
    exact (K a.as).shape i j hij
  d_comp_d' i j k _ _ := by
    ext a
    exact (K a.as).d_comp_d i j k

variable [HasColimitsOfShape (Discrete κ) C]

/-- Applying the actual discrete colimit functor to the original diagram complex. -/
def coproductColimComplex : HomologicalComplex C c :=
  ((colim : (Discrete κ ⥤ C) ⥤ C).mapHomologicalComplex c).obj (coproductDiagram K)

/-- The original inclusions into the degreewise discrete colimit complex. -/
def coproductColimι (a : κ) : K a ⟶ coproductColimComplex K where
  f i := colimit.ι ((coproductDiagram K).X i) (Discrete.mk a)
  comm' i j _ := ι_colimMap ((coproductDiagram K).d i j) (Discrete.mk a)

/-- The native degreewise colimit complex with its original inclusion maps. -/
def coproductColimCofan : Cofan K := Cofan.mk (coproductColimComplex K) (coproductColimι K)

/-- Degree evaluation proves that the original cofan is colimiting. -/
def coproductColimCofanIsColimit : IsColimit (coproductColimCofan K) :=
  isColimitOfEval _ _ (fun i => colimit.isColimit ((coproductDiagram K).X i))

/-- The canonical comparison with the original categorical coproduct of complexes. -/
def coproductColimIso : coproductColimComplex K ≅ ∐ K :=
  (coproductColimCofanIsColimit K).coconePointUniqueUpToIso (colimit.isColimit _)

/-- The degreewise construction retains every original coproduct inclusion. -/
@[reassoc (attr := simp)]
theorem coproductColimι_iso_hom (a : κ) :
    coproductColimι K a ≫ (coproductColimIso K).hom = Sigma.ι K a :=
  (coproductColimCofanIsColimit K).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (Discrete.mk a)

/-- Evaluation computes the original diagram homology, through the native
exact-functor comparison. -/
def coproductDiagramHomologyIso (i : ι) :
    (coproductDiagram K).homology i ≅ Discrete.functor (fun a => (K a).homology i) :=
  Discrete.natIso (fun a =>
    ((coproductDiagram K).sc i).mapHomologyIso ((evaluation (Discrete κ) C).obj a) |>.symm)

variable [HasExactColimitsOfShape (Discrete κ) C]

/-- Native homology commutes with an exact coproduct, for any complex shape. -/
def coproductHomologyIso (i : ι) :
    (∐ K).homology i ≅ ∐ (fun a => (K a).homology i) :=
  (homologyFunctor C c i).mapIso (coproductColimIso K).symm ≪≫
    ((coproductDiagram K).sc i).mapHomologyIso (colim : (Discrete κ ⥤ C) ⥤ C) ≪≫
    (colim : (Discrete κ ⥤ C) ⥤ C).mapIso (coproductDiagramHomologyIso K i)

/-- The exact-colimit homology comparison retains each original inclusion. -/
@[reassoc]
theorem coproductColimι_homology (a : κ) (i : ι) :
    homologyMap (coproductColimι K a) i ≫
        (((coproductDiagram K).sc i).mapHomologyIso
          (colim : (Discrete κ ⥤ C) ⥤ C)).hom ≫
        (colim : (Discrete κ ⥤ C) ⥤ C).map (coproductDiagramHomologyIso K i).hom =
      Sigma.ι (fun a => (K a).homology i) a := by
  let τ : (evaluation (Discrete κ) C).obj (Discrete.mk a) ⟶
      (colim : (Discrete κ ⥤ C) ⥤ C) :=
    { app X := colimit.ι X (Discrete.mk a)
      naturality X Y f := (ι_colimMap f (Discrete.mk a)).symm }
  have h := ((coproductDiagram K).sc i).homologyMap_mapNatTrans τ
  change homologyMap (coproductColimι K a) i =
    (((coproductDiagram K).sc i).mapHomologyIso
      ((evaluation (Discrete κ) C).obj (Discrete.mk a))).hom ≫
        colimit.ι ((coproductDiagram K).homology i) (Discrete.mk a) ≫
        (((coproductDiagram K).sc i).mapHomologyIso
          (colim : (Discrete κ ⥤ C) ⥤ C)).inv at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [colim_map, ι_colimMap]
  simp [coproductDiagramHomologyIso]

/-- The homology-of-coproduct isomorphism sends the original homology map of
each coproduct inclusion to the original inclusion of its homology. -/
@[reassoc (attr := simp)]
theorem homologyMap_sigma_ι_coproductHomologyIso_hom (a : κ) (i : ι) :
    homologyMap (Sigma.ι K a) i ≫ (coproductHomologyIso K i).hom =
      Sigma.ι (fun a => (K a).homology i) a := by
  have hι : Sigma.ι K a ≫ (coproductColimIso K).inv = coproductColimι K a := by
    rw [← coproductColimι_iso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change homologyMap (Sigma.ι K a) i ≫ homologyMap (coproductColimIso K).inv i ≫
      (((coproductDiagram K).sc i).mapHomologyIso
        (colim : (Discrete κ ⥤ C) ⥤ C)).hom ≫
      (colim : (Discrete κ ⥤ C) ⥤ C).map (coproductDiagramHomologyIso K i).hom = _
  rw [← Category.assoc, ← homologyMap_comp, hι]
  exact coproductColimι_homology K a i

end HomologicalComplex
