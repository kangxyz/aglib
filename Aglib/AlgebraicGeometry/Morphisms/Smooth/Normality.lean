/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.RingTheory.RegularLocalRing.Normal

/-! General smooth-field normality from actual regular stalks. -/

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- The original smooth-field normality interface, including domain stalks,
for every field and every smooth scheme. -/
theorem smoothFieldNormality : SmoothFieldNormality.{u} := by
  intro K _ X f hSmooth x
  let := smoothFieldRegularity K X f hSmooth x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

end AlgebraicGeometry.Scheme
