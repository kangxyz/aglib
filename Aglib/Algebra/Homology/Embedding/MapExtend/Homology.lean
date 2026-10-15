/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology coherence for native extension by zero

The original comparison between mapping and extending commutes with the
native retained-degree cycle and homology isomorphisms. The functor preserves
homology; the statement uses the original comparison maps throughout.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u₁ u₂ v₁ v₂ w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [F.PreservesHomology]

private theorem homologyπ_mapHomologyIso_hom (S : ShortComplex C) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  dsimp only [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

/-- The original mapped-extension cycle comparison commutes with both
native retained-degree cycle comparisons. -/
@[reassoc]
theorem mapExtendIso_hom_cyclesMap (e : c.Embedding c')
    {j : ι} {j' : ι'} (hj : e.f j = j') :
    cyclesMap (K.mapExtendIso F e).hom j' ≫
        (((F.mapHomologicalComplex c).obj K).extendCyclesIso e hj).hom ≫
        ((K.sc j).mapCyclesIso F).hom =
      (((K.extend e).sc j').mapCyclesIso F).hom ≫
        F.map (K.extendCyclesIso e hj).hom := by
  let L := (F.mapHomologicalComplex c).obj K
  have hf : ((K.sc j).mapCyclesIso F).hom ≫ F.map (K.iCycles j) = L.iCycles j :=
    (K.sc j).mapCyclesIso_hom_iCycles F
  have hm : F.map (K.iCycles j) = ((K.sc j).mapCyclesIso F).inv ≫ L.iCycles j := by
    rw [← cancel_epi ((K.sc j).mapCyclesIso F).hom]
    simp only [Iso.hom_inv_id_assoc]
    exact hf
  let : Mono (F.map (K.iCycles j)) := by
    rw [hm]
    infer_instance
  apply (cancel_mono (F.map (K.iCycles j))).mp
  simp only [Category.assoc]
  calc
    _ = cyclesMap (K.mapExtendIso F e).hom j' ≫
        (L.extend e).iCycles j' ≫ (L.extendXIso e hj).hom := by
      rw [hf]
      erw [L.extendCyclesIso_hom_iCycles e hj]
    _ = (((F.mapHomologicalComplex c').obj (K.extend e)).iCycles j') ≫
        F.map (K.extendXIso e hj).hom := by
      rw [← Category.assoc, cyclesMap_i, Category.assoc]
      rw [K.mapExtendIso_hom_f_extendXIso F e hj]
    _ = _ := by
      rw [← F.map_comp, K.extendCyclesIso_hom_iCycles e hj,
        F.map_comp]
      rw [← Category.assoc]
      exact congrArg (fun φ => φ ≫ F.map (K.extendXIso e hj).hom)
        (((K.extend e).sc j').mapCyclesIso_hom_iCycles F).symm

/-- Native homology of the original mapping-extension comparison agrees
with applying the functor to the original retained-degree homology map. -/
@[reassoc]
theorem mapExtendIso_hom_homologyMap (e : c.Embedding c')
    {j : ι} {j' : ι'} (hj : e.f j = j') :
    homologyMap (K.mapExtendIso F e).hom j' ≫
        (((F.mapHomologicalComplex c).obj K).extendHomologyIso e hj).hom ≫
        ((K.sc j).mapHomologyIso F).hom =
      (((K.extend e).sc j').mapHomologyIso F).hom ≫
        F.map (K.extendHomologyIso e hj).hom := by
  let L := (F.mapHomologicalComplex c).obj K
  have hπ : ((K.extend e).sc j').homologyπ ≫ (K.extendHomologyIso e hj).hom =
      (K.extendCyclesIso e hj).hom ≫ (K.sc j).homologyπ :=
    K.homologyπ_extendHomologyIso_hom e hj
  apply (cancel_epi
    (((F.mapHomologicalComplex c').obj (K.extend e)).homologyπ j')).mp
  rw [homologyπ_naturality_assoc]
  rw [L.homologyπ_extendHomologyIso_hom_assoc e hj]
  erw [homologyπ_mapHomologyIso_hom F (K.sc j)]
  rw [K.mapExtendIso_hom_cyclesMap_assoc F e hj]
  erw [reassoc_of% (homologyπ_mapHomologyIso_hom F ((K.extend e).sc j'))]
  simp only [← F.map_comp, hπ]

end HomologicalComplex
