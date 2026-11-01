/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CohomologyPullback

/-! # Original cohomology tests on finite direct images

The original finite cohomology equivalences and finite exchange transport
surjectivity and injectivity of the original pullback to finite direct-image
coefficients. These implications retain the actual original square, coefficient
and all four independent Ext universes. They impose no torsion condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS eX' eS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsFinite f]
  (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)

include f' h

/-- Surjectivity of the actual source pullback gives surjectivity on the
actual finite direct-image coefficient, through the original exchange square. -/
theorem cohomologyPullback_finiteDirectImage_surjective
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Surjective (cohomologyPullback.{u, eX, eX'} g' F q)) :
    Function.Surjective (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q) :=
  (Finite.cohomologyPullback_directImage_surjective_iff f f' g g' h F q).mpr hF

/-- Injectivity likewise transports to the same finite direct-image coefficient.
Only the source comparison's injectivity is an additional premise. -/
theorem cohomologyPullback_finiteDirectImage_injective
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Injective (cohomologyPullback.{u, eX, eX'} g' F q)) :
    Function.Injective (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q) :=
  (Finite.cohomologyPullback_directImage_injective_iff f f' g g' h F q).mpr hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
