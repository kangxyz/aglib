/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.ModuleTorsionRingBaseChange
public import Aglib.CategoryTheory.NatTrans.PointwiseIso
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ModuleHigherExchange

/-! # Original module higher images from original proper derived exchange

The installed single/homology comparisons turn the actual proper derived
exchange component into an isomorphism between the original ringed higher
images. All four module-derived universes remain independent. No underlying
additive constructibility or replacement coefficient category is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) [hf : IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)

include sq hf

/-- Every isomorphism-invariant property is transported through the actual
original proper higher-image exchange. The canonical iso is constructed inside
the proof, with its original maps and all original derived models retained. -/
theorem properModuleHigherBaseChange_property_iff
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0) (q : ℕ) (F : ModuleSheaf X Λ)
    (P : ObjectProperty (ModuleSheaf S' Λ)) [P.IsClosedUnderIsomorphisms] :
    P ((moduleInverseImage g Λ).obj (((moduleDirectImage f Λ).rightDerived q).obj F)) ↔
      P (((moduleDirectImage f' Λ).rightDerived q).obj ((moduleInverseImage g' Λ).obj F)) := by
  let e := NatTrans.isoOfIsIsoComponents
    (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
    (properModuleDerivedBaseChange_isIso_of_nsmul_one_eq_zero
      Λ f f' g g' sq n hn ((nsmul_one n).trans hΛ))
  let e' := Functor.higherImageIsoOfDerived (moduleDirectImage f Λ) (moduleInverseImage g Λ)
    (moduleInverseImage g' Λ) (moduleDirectImage f' Λ) q F
    (e.app ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj F))
  exact ⟨fun h => P.prop_of_iso e' h, fun h => P.prop_of_iso e'.symm h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
