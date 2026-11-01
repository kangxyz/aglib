/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TargetIsoBaseChange

/-! # Actual target ambient isomorphisms on full-unbounded raw exchange -/

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
theorem moduleUnboundedRawSquareMap_targetIso :
    TargetIsoBaseChangeEquation
      (moduleUnboundedRawSquareMap M C a qC b hjC hpC Λ)
      (moduleUnboundedRawSquareMap M D a qD b hjD hpD Λ)
      (moduleUnboundedRawCompactificationTransition C D k sq hkp Λ) :=
  moduleUnboundedCompactifiedBaseChangeMap_targetIso M.j M.p C.j C.p D.j D.p a qC qD b k sq
    hkp hkq hjC hjD hpC hpD Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
