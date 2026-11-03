/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.TwoStageTransport
public import Aglib.Algebra.Homology.HomologicalComplex.TwoStageCounit

/-!
# Homology of an actual two-stage cochain square

The original cochain square is carried through the native exact-functor homology
comparisons. The original maps, counits and all independent universes are retained.
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

namespace HomologicalComplex

/-- A genuine cochain square retains the original counit-type arrows after
homology and both native exact-functor comparisons. No counit is assumed invertible. -/
theorem homologyMap_twoStage_square
    (e : F ⋙ G ≅ F' ⋙ G') {I : Type uI} (c : ComplexShape I)
    (K : HomologicalComplex A c) (K₁ : HomologicalComplex B c)
    (L : HomologicalComplex C c) (L₁ : HomologicalComplex D c)
    (d : (F.mapHomologicalComplex c).obj K ⟶ K₁)
    (κ : (F'.mapHomologicalComplex c).obj K ⟶ L)
    (κ₁ : (G.mapHomologicalComplex c).obj K₁ ⟶ L₁)
    (Φ : (G'.mapHomologicalComplex c).obj L ⟶ L₁)
    (h : (G.mapHomologicalComplex c).map d ≫ κ₁ =
      ((Functor.mapHomologicalComplexCompIso e c).app K ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).app K).symm).hom ≫
          (G'.mapHomologicalComplex c).map κ ≫ Φ) (n : I) :
    G.map (((K.sc n).mapHomologyIso F).inv ≫ homologyMap d n) ≫
        ((K₁.sc n).mapHomologyIso G).inv ≫ homologyMap κ₁ n =
      e.hom.app (K.homology n) ≫
        G'.map (((K.sc n).mapHomologyIso F').inv ≫ homologyMap κ n) ≫
        ((L.sc n).mapHomologyIso G').inv ≫ homologyMap Φ n := by
  let E := (Functor.mapHomologicalComplexCompIso e c).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).app K).symm
  have hd := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor B c n).map d) G
  change G.map (homologyMap d n) ≫ ((K₁.sc n).mapHomologyIso G).inv =
    ((((F.mapHomologicalComplex c).obj K).sc n).mapHomologyIso G).inv ≫
      homologyMap ((G.mapHomologicalComplex c).map d) n at hd
  have hκ₁ : G.map (homologyMap d n) ≫ homologyCounitMap G c K₁ κ₁ n =
      ((((F.mapHomologicalComplex c).obj K).sc n).mapHomologyIso G).inv ≫
        homologyMap E.hom n ≫ homologyMap ((G'.mapHomologicalComplex c).map κ) n ≫
          homologyMap Φ n := by
    calc
      _ = ((((F.mapHomologicalComplex c).obj K).sc n).mapHomologyIso G).inv ≫
          homologyMap ((G.mapHomologicalComplex c).map d ≫ κ₁) n := by
        simp only [homologyCounitMap, homologyMap_comp]
        rw [← Category.assoc, hd, Category.assoc]
      _ = _ := by
        rw [h]
        simp only [homologyMap_comp, E]
  have hs := twoStageCounitSquare F G F' G' c K K₁ L L₁ κ κ₁ Φ d e E n
    (((K.sc n).mapHomologyIso F).inv ≫ homologyMap d n) rfl
    (homologyMap_twoStage_exactIso F G F' G' e c K n) hκ₁
  simpa only [homologyCounitMap, Category.assoc] using hs

end HomologicalComplex
