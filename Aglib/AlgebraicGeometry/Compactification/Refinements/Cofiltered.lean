/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Common
public import Aglib.AlgebraicGeometry.Compactification.QCQS

/-! # The cofiltered category of dense compactifications over a qcqs base -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The supplied Nagata theorem gives a schematically dense object without
changing the original source or structural morphism. -/
instance : Nonempty (DenseCompactification f) := by
  obtain ⟨C, hC⟩ := exists_schematicallyDense_compactification_of_qcqs f
  exact ⟨{ toCompactification := C, isSchemeTheoreticallyDominant_j := hC }⟩

/-- Dense compactifications form a cofiltered category for a separated
finite-type morphism over a qcqs base. -/
instance : IsCofiltered (DenseCompactification f) where

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
