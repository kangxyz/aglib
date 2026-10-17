/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The fppf precoverage contains the isomorphisms

Mathlib's `Scheme.fppfPrecoverage` derives `IsStableUnderBaseChange` and
`IsStableUnderComposition` (`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`); this file supplies
`HasIsos`. With these three instances, Mathlib's `Pseudofunctor.IsStack.of_precoverage` and
`Pseudofunctor.IsPrestack.of_precoverage` apply to
`Scheme.fppfTopology = fppfPrecoverage.toGrothendieck`: a pseudofunctor on `Scheme` is a stack
(prestack) for the fppf topology as soon as it is a stack (prestack) for every fppf covering
family.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Singleton presieves of isomorphisms are fppf coverings. -/
instance instHasIsosFppfPrecoverage : fppfPrecoverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ := f.singleton_mem_fppfPrecoverage

end AlgebraicGeometry.Scheme
