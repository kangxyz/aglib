/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.TargetIsoBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeRestriction

/-! # Actual target ambient isomorphisms on native torsion-source raw exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wT wC wD
variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ T}
  (M : Hom.Compactification f) (C D : Hom.Compactification f')
  (a : X' ⟶ X) (qC : C.Xbar ⟶ M.Xbar) (qD : D.Xbar ⟶ M.Xbar) (b : T ⟶ S)
  (k : C.Xbar ⟶ D.Xbar) [IsIso k]
  (sq : IsPullback C.j (𝟙 X') k D.j) (hkp : k ≫ D.p = C.p) (hkq : k ≫ qD = qC)
  (hjC : IsPullback a C.j M.j qC) (hjD : IsPullback a D.j M.j qD)
  (hpC : IsPullback qC C.p M.p b) (hpD : IsPullback qD D.p M.p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

include hkq in
/-- The native raw exchange uses the original transition along the actual ambient isomorphism. -/
theorem moduleRawSquareMap_targetIso :
    TargetIsoBaseChangeEquation
      (moduleRawSquareMap M C a qC b hjC hpC Λ)
      (moduleRawSquareMap M D a qD b hjD hpD Λ)
      (moduleRawCompactificationTransition C D k sq hkp Λ) :=
  targetIsoBaseChange_restrict
    (moduleCompactifiedBaseChangeMap M.j M.p C.j C.p a qC b hjC hpC Λ)
    (moduleCompactifiedBaseChangeMap M.j M.p D.j D.p a qD b hjD hpD Λ)
    (imageComparison (moduleDerivedProperRefinementComparison C.j D.j k sq Λ)
      (moduleDerivedDirectImageOverIso Λ C.p D.p k hkp))
    (moduleDerivedInverseImageTorsionForgetIso a Λ).symm
    (moduleCompactifiedBaseChangeMap_targetIso M.j M.p C.j C.p D.j D.p a qC qD b k sq
      hkp hkq hjC hjD hpC hpD Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
