/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Composition of canonical homology comparisons

The native `ShortComplex.mapHomologyIso` is coherent with successive additive
functors preserving the left homology of the displayed short complexes. Exact
additive functors give a convenient specialization. This general result was extracted from
`Aglib.AlgebraicGeometry.Cohomology.BaseChange.CechComparison` so that algebraic
base-change constructions can use the same comparison below scheme cohomology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
section

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] (S : ShortComplex C)
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)]
  [(F ⋙ G).PreservesLeftHomologyOf S]

/-- Identity homology data comparing successive exact functors with their composite. -/
def compositeHomologyDataIdentity :
    ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      ((S.homologyData.left.map F).map G) (S.homologyData.left.map (F ⋙ G)) where
  φK := 𝟙 _
  φH := 𝟙 _
  commi := by simp
  commf' := by simp
  commπ := by simp

/-- The canonical homology comparison is coherent with composition whenever
the individual and composite functors preserve the displayed left homology. -/
theorem mapHomologyIso_comp_hom_of_preservesLeftHomology :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  have hd := (compositeHomologyDataIdentity F G S).homologyMap_comm
  simp only [ShortComplex.homologyMap_id, compositeHomologyDataIdentity, Category.id_comp,
    Category.comp_id] at hd
  rw [(S.homologyData.left.map F).mapHomologyIso_eq G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← G.map_comp]
  change (S.mapHomologyIso (F ⋙ G)).hom =
    ((S.homologyData.left.map F).map G).homologyIso.hom ≫
      G.map ((S.mapHomologyIso F).inv ≫ (S.mapHomologyIso F).hom)
  rw [Iso.inv_hom_id, G.map_id]
  erw [Category.comp_id]
  exact hd


end

section

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]

local instance : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
local instance : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
local instance : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
local instance : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G

/-- The canonical homology comparison is coherent with composition of exact additive functors. -/
theorem mapHomologyIso_comp_hom (S : ShortComplex C) :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom :=
  mapHomologyIso_comp_hom_of_preservesLeftHomology F G S

end

end CategoryTheory.ShortComplex
