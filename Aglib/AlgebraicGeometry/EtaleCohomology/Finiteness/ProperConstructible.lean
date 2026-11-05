/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperFromCurves

/-! # Proper constructibility from the complete relative-curve theorem

The existing projective and Chow reductions consume the actual all-degree
curve theorem. No curve certificate is an input to this endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Every higher direct image of an original constructible coefficient under a
proper morphism to a Noetherian scheme is constructible. -/
theorem higherDirectImage_proper_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  apply higherDirectImage_proper_isConstructible_of_curves ?_ f q F hF
  intro Y T _ g _ hdim k G hG
  apply higherDirectImage_isConstructible_of_relativeCurve g ?_ k G hG
  intro Ω _ _ η
  exact hdim Ω η

end AlgebraicGeometry.Scheme.EtaleCohomology
