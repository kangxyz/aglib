/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.AdjoinMap

/-! # Compatibility names for the lower generated-subalgebra algebra

The algebraic arguments are owned by `Algebra`; the original geometric
namespace keeps its existing caller interface.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

export Algebra (adjoin_clear_power adjoinMap adjoin_isLocalization
  adjoin_finiteType_of_span_fg adjoin_iUnion_range_finiteType)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
