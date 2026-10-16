/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Compatibility import for native local perfectness

The sole predicates and categories are in `Modules.PerfectComplexes.Local`.
The former local standard-derived name transparently delegates to its lower
canonical owner; it does not register another global instance.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Legacy name for the same canonical native derived-category choice. -/
abbrev standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  Scheme.Modules.standardHasDerivedCategory X

end AlgebraicGeometry.Scheme.Modules.Complex
