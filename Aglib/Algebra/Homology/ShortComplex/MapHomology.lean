/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Canonical homology comparisons and natural transformations

The native `ShortComplex.mapHomologyIso` is coherent with successive additive
functors preserving the left homology of the displayed short complexes. Exact
additive functors also transport natural transformations, following maps and
supplied short-complex squares through these same comparisons. These results
were extracted from `Aglib.AlgebraicGeometry.Cohomology.BaseChange.CechComparison`
so algebraic base-change constructions can retain their original functors and maps.
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


section NaturalTransformation

variable (T : C ⥤ D) (U : C ⥤ E) (G : D ⥤ E)
  [T.Additive] [U.Additive] [G.Additive]
  [T.PreservesHomology] [U.PreservesHomology] [G.PreservesHomology]

local instance : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
local instance : PreservesFiniteColimits T := Functor.preservesFiniteColimits_of_preservesHomology T
local instance : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
local instance : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G

/-- A natural transformation retains its actual homology map when the comparison
for the first functor is cancelled from the composite comparison. -/
@[reassoc]
theorem natTrans_mapHomologyIso_inv (α : U ⟶ T ⋙ G) (S : ShortComplex C) :
    α.app S.homology ≫ G.map (S.mapHomologyIso T).inv =
      (S.mapHomologyIso U).inv ≫ homologyMap (S.mapNatTrans α) ≫
        ((S.map T).mapHomologyIso G).hom := by
  have h := NatTrans.app_homology α S
  erw [mapHomologyIso_comp_hom T G S] at h
  erw [h]
  simp only [Category.assoc]
  erw [← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]

/-- Naturality of the same comparisons for an actual following short-complex map. -/
@[reassoc]
theorem natTrans_mapHomologyIso_inv_map (α : U ⟶ T ⋙ G) (S : ShortComplex C)
    (S' : ShortComplex D) (β : S.map T ⟶ S') :
    α.app S.homology ≫ G.map ((S.mapHomologyIso T).inv ≫ homologyMap β) ≫
        (S'.mapHomologyIso G).inv =
      (S.mapHomologyIso U).inv ≫
        homologyMap (S.mapNatTrans α ≫ G.mapShortComplex.map β) := by
  have hn := mapHomologyIso_inv_naturality β G
  rw [Functor.map_comp]
  simp only [Category.assoc, homologyMap_comp]
  erw [natTrans_mapHomologyIso_inv_assoc]
  erw [hn]
  erw [Iso.hom_inv_id_assoc]

/-- An actual supplied square transports the natural transformation and following
map through homology, using only the original comparison maps. -/
theorem natTrans_mapHomologyIso_inv_map_of_square
    (α : U ⟶ T ⋙ G) (S : ShortComplex C) (S' : ShortComplex D) (β : S.map T ⟶ S')
    {A B : ShortComplex E} (i : S.map U ⟶ A) (j : S'.map G ⟶ B) (g : A ⟶ B)
    (h : S.mapNatTrans α ≫ G.mapShortComplex.map β ≫ j = i ≫ g) :
    α.app S.homology ≫ G.map ((S.mapHomologyIso T).inv ≫ homologyMap β) ≫
        (S'.mapHomologyIso G).inv ≫ homologyMap j =
      (S.mapHomologyIso U).inv ≫ homologyMap i ≫ homologyMap g := by
  have ht := congrArg (fun q => q ≫ homologyMap j)
    (natTrans_mapHomologyIso_inv_map T U G α S S' β)
  have hc := congrArg (fun q => homologyMap q) h
  simp only [homologyMap_comp, Category.assoc] at ht hc
  exact ht.trans (congrArg (fun q => (S.mapHomologyIso U).inv ≫ q) hc)

end NaturalTransformation

end CategoryTheory.ShortComplex
