/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquare
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeRestriction

/-! # Original commuting compactification exchange on torsion inputs

The restriction uses the original inverse-image torsion-forgetting comparison.
Its refinement factorization retains the original raw unit transition.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wT wC wD wE

variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ T}
  (C : Hom.Compactification f) (D : Hom.Compactification f')
  (a : X' ⟶ X) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j C.j q) (hp : D.p ≫ b = q ≫ C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The original compactified commuting map, restricted through the native torsion comparison. -/
def moduleRawCommutingSquareMap :
    moduleRawCompactificationFunctor C Λ ⋙ moduleDerivedInverseImage Λ b ⟶
      moduleDerivedInverseImageTorsion a Λ ⋙ moduleRawCompactificationFunctor D Λ :=
  compositeExchange (moduleCompactifiedCommutingExchange C.j C.p D.j D.p a q b hj hp Λ)
    (moduleDerivedInverseImageTorsionForgetIso a Λ).symm

/-- A Cartesian proper face recovers the same original raw square map literally. -/
theorem moduleRawCommutingSquareMap_cartesian (sq : IsPullback q D.p C.p b) :
    moduleRawCommutingSquareMap C D a q b hj sq.w.symm Λ =
      moduleRawSquareMap C D a q b hj sq Λ := rfl

variable (E : Hom.Compactification f') (h : E.Xbar ⟶ D.Xbar)
  (sq : IsPullback E.j (𝟙 X') h D.j) (hbase : h ≫ D.p = E.p)
  (qE : E.Xbar ⟶ C.Xbar) (hambient : h ≫ q = qE)
  (hjE : IsPullback a E.j C.j qE) (hpE : E.p ≫ b = qE ≫ C.p)
  [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)]

include hambient in
/-- Normalizing the actual target model factors through the unchanged original raw transition. -/
theorem moduleRawCommutingSquareMap_refinement :
    moduleRawCommutingSquareMap C E a qE b hjE hpE Λ =
      moduleRawCommutingSquareMap C D a q b hj hp Λ ≫
        Functor.whiskerLeft (moduleDerivedInverseImageTorsion a Λ)
          (moduleRawCompactificationTransition E D h sq hbase Λ) := by
  have he := moduleCompactifiedCommutingExchange_refinement_over
    C.j C.p D.j D.p E.j E.p h a q qE b hj hp sq hbase hambient hjE hpE Λ
  have hr := compositeExchange_restriction_naturality
    (moduleCompactifiedCommutingExchange C.j C.p E.j E.p a qE b hjE hpE Λ)
    (moduleCompactifiedCommutingExchange C.j C.p D.j D.p a q b hj hp Λ)
    (moduleDerivedInverseImageTorsionForgetIso a Λ).symm
    (𝟙 (moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p))
    (imageComparison (moduleDerivedProperRefinementComparison E.j D.j h sq Λ)
      (moduleDerivedDirectImageOverIso Λ E.p D.p h hbase))
    (by simpa only [Functor.whiskerRight_id', Category.id_comp] using he)
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp] at hr
  exact hr

end AlgebraicGeometry.Scheme.EtaleCohomology
