/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBCRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

/-! # Original commuting compactification exchange on full unbounded inputs

The map uses the original native unbounded inverse-image exchange.
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

/-- The original compactified commuting map on every native unbounded input. -/
def moduleUnboundedRawCommutingSquareMap :
    moduleUnboundedRawCompactificationFunctor C Λ ⋙ moduleUnboundedDerivedInverseImage Λ b ⟶
      moduleUnboundedDerivedInverseImage Λ a ⋙ moduleUnboundedRawCompactificationFunctor D Λ :=
  moduleUnboundedCompactifiedCommutingExchange C.j C.p D.j D.p a q b hj hp Λ

/-- A Cartesian proper face recovers the same original raw square map literally. -/
theorem moduleUnboundedRawCommutingSquareMap_cartesian (sq : IsPullback q D.p C.p b) :
    moduleUnboundedRawCommutingSquareMap C D a q b hj sq.w.symm Λ =
      moduleUnboundedRawSquareMap C D a q b hj sq Λ := rfl

variable (E : Hom.Compactification f') (h : E.Xbar ⟶ D.Xbar)
  (sq : IsPullback E.j (𝟙 X') h D.j) (hbase : h ≫ D.p = E.p)
  (qE : E.Xbar ⟶ C.Xbar) (hambient : h ≫ q = qE)
  (hjE : IsPullback a E.j C.j qE) (hpE : E.p ≫ b = qE ≫ C.p)
  [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)]

include hambient in
/-- Normalizing the actual target model factors through the unchanged original raw transition. -/
theorem moduleUnboundedRawCommutingSquareMap_refinement :
    moduleUnboundedRawCommutingSquareMap C E a qE b hjE hpE Λ =
      moduleUnboundedRawCommutingSquareMap C D a q b hj hp Λ ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ a)
          (moduleUnboundedRawCompactificationTransition E D h sq hbase Λ) :=
  moduleUnboundedCompactifiedCommutingExchange_refinement_over
    C.j C.p D.j D.p E.j E.p h a q qE b hj hp sq hbase hambient hjE hpE Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
