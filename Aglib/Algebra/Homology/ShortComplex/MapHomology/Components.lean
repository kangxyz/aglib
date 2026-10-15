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
original map from homology to opcycles and the original projection to
opcycles. These equations normalize the degree-zero homology embedding in
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

end CategoryTheory.ShortComplex
