/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Limits of the original continuous sheaf pushforward

Continuous sheaf precomposition preserves every limit shape admitted by the
coefficient category. The proof uses native limit creation on underlying
presheaves and applies before choosing a slice or a coefficient realization.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uC vC uD vD uA vA s sH

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (A : Type uA) [Category.{vA} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]

/-- Original continuous sheaf precomposition preserves every admitted limit shape. -/
instance sheafPushforwardContinuous_preservesLimitsOfShape
    {S : Type s} [Category.{sH} S] [HasLimitsOfShape S A] :
    PreservesLimitsOfShape S (F.sheafPushforwardContinuous A J K) := by
  let R := F.sheafPushforwardContinuous A J K
  let I := sheafToPresheaf J A
  have : PreservesLimitsOfShape S (R ⋙ I) := by
    change PreservesLimitsOfShape S
      (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves R I

/-- The same original functor is left exact whenever the coefficients have finite limits. -/
instance sheafPushforwardContinuous_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A J K) :=
  ⟨fun _ => inferInstance⟩

end CategoryTheory.Functor
