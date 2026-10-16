/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-!
# Structure maps under the canonical homology comparison

The native comparison for a homology-preserving functor commutes with the
original cycle inclusion, projection from cycles to homology, map from
homology to opcycles and projection to opcycles. These equations normalize
the degree-zero homology embedding in
cochain complexes, including scalar forgetting and scalar restriction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (S : ShortComplex C)

/-- The native homology comparison preserves the actual homology-to-opcycles map. -/
@[reassoc]
theorem mapHomologyIso_hom_homologyι :
    (S.mapHomologyIso F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := by
  rw [← S.mapHomologyIso'_eq_mapHomologyIso F,
    S.homologyData.right.mapHomologyIso'_eq F,
    S.homologyData.right.mapOpcyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← F.map_comp, RightHomologyData.homologyIso_inv_comp_homologyι, F.map_comp,
    ← Category.assoc]
  erw [RightHomologyData.homologyIso_hom_comp_ι]
  exact Category.assoc _ _ _

/-- The native opcycles comparison preserves the original projection from the middle term. -/
@[reassoc]
theorem map_pOpcycles_mapOpcyclesIso_inv :
    F.map S.pOpcycles ≫ (S.mapOpcyclesIso F).inv = (S.map F).pOpcycles := by
  rw [S.homologyData.right.mapOpcyclesIso_eq F]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
  rw [← Category.assoc, ← F.map_comp,
    RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  exact (S.homologyData.right.map F).p_comp_opcyclesIso_inv

/-- The native homology comparison preserves the original projection from cycles. -/
@[reassoc]
theorem homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq F,
    S.homologyData.left.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc]
  erw [(S.homologyData.left.map F).homologyπ_comp_homologyIso_hom]
  change ((S.homologyData.left.map F).cyclesIso.hom ≫
      F.map S.homologyData.left.π) ≫ F.map S.homologyData.left.homologyIso.inv =
    ((S.homologyData.left.map F).cyclesIso.hom ≫
      F.map S.homologyData.left.cyclesIso.inv) ≫ F.map S.homologyπ
  rw [Category.assoc, ← F.map_comp, S.homologyData.left.π_comp_homologyIso_inv,
    F.map_comp, Category.assoc]

/-- The inverse native cycles comparison preserves the original cycle inclusion. -/
@[reassoc]
theorem mapCyclesIso_inv_iCycles :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  apply (cancel_epi (S.mapCyclesIso F).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (S.mapCyclesIso_hom_iCycles F).symm

/-- The inverse native homology comparison preserves the original cycle projection. -/
@[reassoc]
theorem map_homologyπ_mapHomologyIso_inv :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  apply (cancel_epi (S.mapCyclesIso F).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← homologyπ_mapHomologyIso_hom F S, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.ShortComplex
