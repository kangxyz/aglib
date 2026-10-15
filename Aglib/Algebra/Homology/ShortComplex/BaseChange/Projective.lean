/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Regular
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Canonical scalar extension with a projective outgoing cokernel

Projectivity of the last term and the original outgoing cokernel makes
the native homology base-change mate invertible after every ring map.
Neither flatness of that map nor projectivity or finiteness of the first
two terms is assumed. The proof uses the actual generalized inverse and
the original extension/restriction adjunction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v w

variable {R : Type u} {B : Type w} [CommRing R] [CommRing B]

/-- A projective final term and projective original outgoing cokernel give arbitrary
canonical homology base change. The original ring and carrier universes are retained. -/
theorem homologyBaseChangeMap_isIso_of_projective_cokernel (σ : R →+* B)
    (S : ShortComplex (ModuleCat.{max v w} R))
    [Module.Projective R S.X₃]
    [Module.Projective R (cokernel S.g : ModuleCat.{max v w} R)] :
    IsIso (homologyBaseChangeMap σ S) :=
  (extendRestrictScalarsAdj.{v, u, w} σ).homologyComparison_isIso_of_projective_cokernel S

end ModuleCat
