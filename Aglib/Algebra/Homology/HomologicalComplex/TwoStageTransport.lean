/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive

/-!
# Two-stage exact functors and the original homology comparison

The canonical homology comparisons retain a supplied natural isomorphism
between two composites. For actual complexes the map is the native composite
comparison followed by the native inverse comparison on the other side.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe uA vA uB vB uC vC uD vD uI

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) (F' : A ⥤ C) (G' : C ⥤ D)
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  [F.PreservesHomology] [G.PreservesHomology]
  [F'.PreservesHomology] [G'.PreservesHomology]

local instance : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
local instance : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
local instance : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
local instance : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
local instance : PreservesFiniteLimits F' := Functor.preservesFiniteLimits_of_preservesHomology F'
local instance : PreservesFiniteColimits F' :=
  Functor.preservesFiniteColimits_of_preservesHomology F'
local instance : PreservesFiniteLimits G' := Functor.preservesFiniteLimits_of_preservesHomology G'
local instance : PreservesFiniteColimits G' :=
  Functor.preservesFiniteColimits_of_preservesHomology G'

namespace CategoryTheory.ShortComplex

/-- Native homology of the original natural transformation agrees with its component
after both stages of each exact functor comparison. -/
theorem homologyMap_twoStage_exactIso (e : F ⋙ G ≅ F' ⋙ G') (S : ShortComplex A) :
    G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans e.hom) ≫
      ((S.map F').mapHomologyIso G').hom ≫ G'.map (S.mapHomologyIso F').hom =
        e.hom.app S.homology := by
  have hFG : S.mapHomologyIso (F ⋙ G) =
      ((S.map F).mapHomologyIso G) ≪≫ G.mapIso (S.mapHomologyIso F) := by
    apply Iso.ext
    exact mapHomologyIso_comp_hom F G S
  have hFG' : S.mapHomologyIso (F' ⋙ G') =
      ((S.map F').mapHomologyIso G') ≪≫ G'.mapIso (S.mapHomologyIso F') := by
    apply Iso.ext
    exact mapHomologyIso_comp_hom F' G' S
  have h := NatTrans.app_homology e.hom S
  rw [hFG, hFG'] at h
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] using h.symm

end CategoryTheory.ShortComplex

namespace HomologicalComplex

/-- Homology of the exact native two-stage complex comparison is the original
natural-isomorphism component under the four native homology comparisons. -/
theorem homologyMap_twoStage_exactIso
    (e : F ⋙ G ≅ F' ⋙ G') {I : Type uI} (c : ComplexShape I)
    (K : HomologicalComplex A c) (n : I) :
    let E_K := (Functor.mapHomologicalComplexCompIso e c).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).app K).symm
    G.map ((K.sc n).mapHomologyIso F).inv ≫
      ((((F.mapHomologicalComplex c).obj K).sc n).mapHomologyIso G).inv ≫
      homologyMap E_K.hom n ≫
      ((((F'.mapHomologicalComplex c).obj K).sc n).mapHomologyIso G').hom ≫
      G'.map ((K.sc n).mapHomologyIso F').hom = e.hom.app (K.homology n) := by
  let E_K := (Functor.mapHomologicalComplexCompIso e c).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).app K).symm
  have hE : (shortComplexFunctor D c n).map E_K.hom = (K.sc n).mapNatTrans e.hom := by
    ext <;> simp [E_K, Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
  change G.map ((K.sc n).mapHomologyIso F).inv ≫
      (((K.sc n).map F).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap ((shortComplexFunctor D c n).map E_K.hom) ≫
      (((K.sc n).map F').mapHomologyIso G').hom ≫
      G'.map ((K.sc n).mapHomologyIso F').hom = _
  rw [hE]
  exact CategoryTheory.ShortComplex.homologyMap_twoStage_exactIso F G F' G' e (K.sc n)

end HomologicalComplex
