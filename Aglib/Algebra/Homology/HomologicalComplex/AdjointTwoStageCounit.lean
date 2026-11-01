/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction.Homology
public import Aglib.Algebra.Homology.HomologicalComplex.TwoStageTransport
public import Aglib.Algebra.Homology.HomologicalComplex.TwoStageCounit

/-! # The original adjoint counit square before taking homology

The actual adjunction, exact two-stage comparison and one complex-level
counit square supply the full homology comparison. No homology-level
comparison laws are new inputs at a geometric specialization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe uA vA uB vB uC vC uD vD uI

namespace HomologicalComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ A) (T : B ⥤ D) (T₀ : A ⥤ C) (U : C ⥤ D)
  [F.Additive] [G.Additive] [T.Additive] [T₀.Additive] [U.Additive]
  [F.PreservesHomology] [G.PreservesHomology] [T.PreservesHomology]
  [T₀.PreservesHomology] [U.PreservesHomology]

local instance : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
local instance : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
local instance : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
local instance : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G

/-- The same ordinary adjoint homology map acts through the original counits.
The sole square input is the original square of complexes, before homology. -/
theorem adjointTwoStageCounitSquare (adj : F ⊣ G)
    {ι : Type uI} (shape : ComplexShape ι)
    (C₀ : HomologicalComplex A shape) (L : HomologicalComplex B shape)
    (K : HomologicalComplex C shape) (K' : HomologicalComplex D shape)
    (κ : (T₀.mapHomologicalComplex shape).obj C₀ ⟶ K)
    (τ : (T.mapHomologicalComplex shape).obj L ⟶ K')
    (Φ : (U.mapHomologicalComplex shape).obj K ⟶ K')
    (f : C₀ ⟶ (G.mapHomologicalComplex shape).obj L)
    (E : F ⋙ T ≅ T₀ ⋙ U)
    (hsquare :
      (T.mapHomologicalComplex shape).map
          (((adj.mapHomologicalComplex shape).homEquiv C₀ L).symm f) ≫ τ =
        (((Functor.mapHomologicalComplexCompIso E shape).app C₀) ≪≫
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (T₀ ⋙ U)) shape).app C₀).symm).hom ≫
            (U.mapHomologicalComplex shape).map κ ≫ Φ)
    (n : ι) :
    T.map ((adj.homEquiv _ _).symm
        (homologyMap f n ≫ ((L.sc n).mapHomologyIso G).hom)) ≫
      homologyCounitMap T shape L τ n =
        E.hom.app (C₀.homology n) ≫ U.map (homologyCounitMap T₀ shape C₀ κ n) ≫
          homologyCounitMap U shape K Φ n := by
  let D₀ := ((adj.mapHomologicalComplex shape).homEquiv C₀ L).symm f
  let B₀ := (Functor.mapHomologicalComplexCompIso E shape).app C₀ ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (T₀ ⋙ U)) shape).app C₀).symm
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor B shape n).map D₀) T
  change T.map (homologyMap D₀ n) ≫ ((L.sc n).mapHomologyIso T).inv =
    ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv ≫
      homologyMap ((T.mapHomologicalComplex shape).map D₀) n at hn
  have hτ : T.map (homologyMap D₀ n) ≫ homologyCounitMap T shape L τ n =
      ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv ≫
        homologyMap B₀.hom n ≫ homologyMap ((U.mapHomologicalComplex shape).map κ) n ≫
          homologyMap Φ n := by
    calc
      _ = ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv ≫
          homologyMap ((T.mapHomologicalComplex shape).map D₀ ≫ τ) n := by
        simp only [homologyCounitMap, homologyMap_comp]
        rw [← Category.assoc, hn, Category.assoc]
      _ = _ := by
        rw [hsquare]
        simp only [homologyMap_comp, B₀]
  exact twoStageCounitSquare F T T₀ U shape C₀ L K K' κ τ Φ D₀ E B₀ n _
    (adj.mapHomologicalComplex_homology_homEquiv_symm shape f n)
    (homologyMap_twoStage_exactIso F T T₀ U E shape C₀ n) hτ

end HomologicalComplex
