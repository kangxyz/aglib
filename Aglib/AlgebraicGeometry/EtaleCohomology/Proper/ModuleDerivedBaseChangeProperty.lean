/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.ModuleTorsionRingBaseChange
public import Aglib.CategoryTheory.NatTrans.PointwiseIso
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! # Property transport through the actual proper derived exchange -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper
open Coefficients
universe u wX wS wX' wS'
attribute [local instance] hasSheafifyLarge

/-- Every isomorphism-invariant property transports through the original whole exchange. -/
theorem properModuleDerivedBaseChange_property_iff
    (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (P : ObjectProperty (DerivedCategory.Plus (ModuleSheaf S' Λ)))
    [P.IsClosedUnderIsomorphisms] :
    P ((moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K)) ↔
      P ((moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj K)) := by
  let e := NatTrans.isoOfIsIsoComponents
    (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
    (properModuleDerivedBaseChange_isIso_of_nsmul_one_eq_zero
      Λ f f' g g' sq n hn ((nsmul_one n).trans hΛ))
  exact ⟨fun h => P.prop_of_iso (e.app K) h,
    fun h => P.prop_of_iso (e.app K).symm h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
