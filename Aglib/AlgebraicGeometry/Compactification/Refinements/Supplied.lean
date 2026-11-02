/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Cofiltered

/-! # The original supplied compactification choice, before coefficient categories -/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]

/-- Choose one actual compactification from the supplied nonempty category. -/
def moduleExceptionalSuppliedCompactification : Hom.DenseCompactification f :=
  Classical.choice inferInstance


end AlgebraicGeometry.Scheme.EtaleCohomology
