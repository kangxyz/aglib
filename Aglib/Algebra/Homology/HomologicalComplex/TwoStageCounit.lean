/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive

/-! # The complete original two-stage homology counit square

All homology comparisons and their cancellation are formed over the original
variable complexes before geometric resolutions or affine counits are supplied.
The inputs are the actual scalar-adjoint, two-stage comparison and counit laws.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe uA vA uB vB uC vC uD vD uI

namespace HomologicalComplex

/-- The original homology comparison followed by homology of an actual complex map.
This constructs a counit map without assuming the supplied complex map is invertible. -/
def homologyCounitMap {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    {ι : Type uI} (shape : ComplexShape ι) (C₀ : HomologicalComplex A shape)
    {K : HomologicalComplex B shape}
    (κ : (F.mapHomologicalComplex shape).obj C₀ ⟶ K) (n : ι) :
    F.obj (C₀.homology n) ⟶ K.homology n :=
  ((C₀.sc n).mapHomologyIso F).inv ≫ homologyMap κ n

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : A ⥤ B) (T : B ⥤ D) (T₀ : A ⥤ C) (U : C ⥤ D)
  [F.Additive] [T.Additive] [T₀.Additive] [U.Additive]
  [F.PreservesHomology] [T.PreservesHomology]
  [T₀.PreservesHomology] [U.PreservesHomology]

/-- Assemble the same homology counit square from its original three whole
comparison laws. The counits are arbitrary maps, not assumed invertible. -/
theorem twoStageCounitSquare {ι : Type uI} (shape : ComplexShape ι)
    (C₀ : HomologicalComplex A shape) (L : HomologicalComplex B shape)
    (K : HomologicalComplex C shape) (K' : HomologicalComplex D shape)
    (κ : (T₀.mapHomologicalComplex shape).obj C₀ ⟶ K)
    (τ : (T.mapHomologicalComplex shape).obj L ⟶ K')
    (Φ : (U.mapHomologicalComplex shape).obj K ⟶ K')
    (D₀ : (F.mapHomologicalComplex shape).obj C₀ ⟶ L)
    (E : F ⋙ T ≅ T₀ ⋙ U)
    (B₀ : (T.mapHomologicalComplex shape).obj
        ((F.mapHomologicalComplex shape).obj C₀) ≅
      (U.mapHomologicalComplex shape).obj ((T₀.mapHomologicalComplex shape).obj C₀))
    (n : ι) (d : F.obj (C₀.homology n) ⟶ L.homology n)
    (hD : ((C₀.sc n).mapHomologyIso F).inv ≫ homologyMap D₀ n = d)
    (hB : T.map ((C₀.sc n).mapHomologyIso F).inv ≫
      ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv ≫
      homologyMap B₀.hom n ≫
      ((((T₀.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso U).hom ≫
      U.map ((C₀.sc n).mapHomologyIso T₀).hom = E.hom.app (C₀.homology n))
    (hτ : T.map (homologyMap D₀ n) ≫ homologyCounitMap T shape L τ n =
      ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv ≫
      homologyMap B₀.hom n ≫ homologyMap ((U.mapHomologicalComplex shape).map κ) n ≫
      homologyMap Φ n) :
    T.map d ≫ homologyCounitMap T shape L τ n =
      E.hom.app (C₀.homology n) ≫
        U.map (homologyCounitMap T₀ shape C₀ κ n) ≫
        homologyCounitMap U shape K Φ n := by
  dsimp only [homologyCounitMap] at hτ ⊢
  let e := ((((T₀.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso U) ≪≫
    U.mapIso ((C₀.sc n).mapHomologyIso T₀)
  let a := T.map ((C₀.sc n).mapHomologyIso F).inv ≫
    ((((F.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso T).inv
  have hB' : (a ≫ homologyMap B₀.hom n) ≫ e.hom = E.hom.app (C₀.homology n) := by
    simpa only [a, e, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hB
  have hb : a ≫ homologyMap B₀.hom n = E.hom.app (C₀.homology n) ≫ e.inv := by
    have hc := congrArg (fun z => z ≫ e.inv) hB'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
  have hκ := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor C shape n).map κ) U
  change U.map (homologyMap κ n) ≫ ((K.sc n).mapHomologyIso U).inv =
    ((((T₀.mapHomologicalComplex shape).obj C₀).sc n).mapHomologyIso U).inv ≫
      homologyMap ((U.mapHomologicalComplex shape).map κ) n at hκ
  have hc : e.inv ≫ homologyMap ((U.mapHomologicalComplex shape).map κ) n =
      U.map (((C₀.sc n).mapHomologyIso T₀).inv ≫ homologyMap κ n) ≫
        ((K.sc n).mapHomologyIso U).inv := by
    simp only [e, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    rw [← hκ, ← Functor.map_comp_assoc]
  calc
    _ = a ≫ homologyMap B₀.hom n ≫
        homologyMap ((U.mapHomologicalComplex shape).map κ) n ≫ homologyMap Φ n := by
      rw [← hD, Functor.map_comp, Category.assoc, hτ]
      simp only [a, Category.assoc]
    _ = E.hom.app (C₀.homology n) ≫ e.inv ≫
        homologyMap ((U.mapHomologicalComplex shape).map κ) n ≫ homologyMap Φ n := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ homologyMap ((U.mapHomologicalComplex shape).map κ) n ≫
          homologyMap Φ n) hb
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => E.hom.app (C₀.homology n) ≫ z ≫ homologyMap Φ n) hc

end HomologicalComplex
