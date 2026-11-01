/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquare

/-! # Equality transport of the original raw exchange source arrow -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wX' wT wD
variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ T}
  (C : Hom.Compactification f) (D : Hom.Compactification f')
  (a a' : X' ⟶ X) (ha : a = a') (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j C.j q) (hj' : IsPullback a' D.j C.j q)
  (hp : IsPullback q D.p C.p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- Only the actual source-arrow equality is transported; the original exchange
and its native target model are unchanged. -/
theorem moduleRawSquareMap_congr_source :
    moduleRawSquareMap C D a q b hj hp Λ ≫
        Functor.whiskerRight (eqToIso (congrArg
          (fun z => moduleDerivedInverseImageTorsion z Λ) ha)).hom
          (moduleRawCompactificationFunctor D Λ) =
      moduleRawSquareMap C D a' q b hj' hp Λ := by
  subst a'
  simp only [eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_id', Category.comp_id]

end AlgebraicGeometry.Scheme.EtaleCohomology
