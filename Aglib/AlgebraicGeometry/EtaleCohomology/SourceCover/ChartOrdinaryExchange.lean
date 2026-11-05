/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryCartesian

/-! # Bounded ordinary exchange on the original pulled-back source chart

The original pullback scheme and its literal two projections are used here.
This thin geometric instance has no higher-image or source-cover imports.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

/-- Ordinary smooth exchange on the composite original source chart. -/
theorem sourceChartOrdinaryExchange_isIso
    {X S X' S' U : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g) [Smooth g]
    (j : U ⟶ X) (F : AbelianSheaf.{u, u + 1} U)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
      ((IsPullback.of_hasPullback j g').paste_vert H).w.symm).app F) :=
  baseChangeMap_smooth_bounded_isIso_of_isPullback
    (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
    ((IsPullback.of_hasPullback j g').paste_vert H) F n hn hF

end AlgebraicGeometry.Scheme.EtaleCohomology
