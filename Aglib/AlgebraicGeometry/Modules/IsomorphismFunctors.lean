/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # Module-sheaf functors of scheme isomorphisms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
/-- Pushforward along an actual scheme isomorphism is an equivalence with literal inverse image. -/
theorem pushforward_isEquivalence_of_isIso : (Scheme.Modules.pushforward f).IsEquivalence := by
  let : (Scheme.Modules.pushforward f).EssSurj :=
    ⟨fun M => ⟨(Scheme.Modules.pushforward (inv f)).obj M, ⟨
      (Scheme.Modules.pushforwardComp (inv f) f).app M ≪≫
      (Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id f)).app M ≪≫
      (Scheme.Modules.pushforwardId Y).app M⟩⟩⟩
  exact {}
/-- The original geometric pullback along an isomorphism is an equivalence. -/
theorem pullback_isEquivalence_of_isIso : (Scheme.Modules.pullback f).IsEquivalence := by
  have := pushforward_isEquivalence_of_isIso f
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).isEquivalence_left_of_isEquivalence_right
end AlgebraicGeometry.Scheme.Modules
