/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange

/-! # Original Cartesian exchange between raw models in the full unbounded categories -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wX' wT wD
variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ T}
  (C : Hom.Compactification f) (D : Hom.Compactification f')
  (a : X' ⟶ X) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j C.j q) (hp : IsPullback q D.p C.p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The unchanged original native compactified exchange. -/
def moduleUnboundedRawSquareMap :
    moduleUnboundedRawCompactificationFunctor C Λ ⋙ moduleUnboundedDerivedInverseImage Λ b ⟶
      moduleUnboundedDerivedInverseImage Λ a ⋙ moduleUnboundedRawCompactificationFunctor D Λ :=
  moduleUnboundedCompactifiedBaseChangeMap C.j C.p D.j D.p a q b hj hp Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
