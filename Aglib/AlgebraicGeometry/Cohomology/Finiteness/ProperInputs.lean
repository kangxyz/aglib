/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
/-!
# General proper structure-cohomology and constants theorem families

The explicit structure-cohomology finiteness predicate for arbitrary proper
field schemes, using actual cohomology with structural scalars.

Extracted from `R5Lab.AlgebraicGeometry.Curves.Genus:39–47,54–61` at
R5Lab revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
Only `ProperStructureCohomologyFinite` is included. This predicate is not
proved here; consumers retain it as an explicit hypothesis.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme

universe u

/-- General proper structure-sheaf cohomology finiteness in every degree.
This is the structure-sheaf specialization of Stacks 02O6 (30.19.2), with
properness over a field ensuring Noetherianity and coherence of O_X.
The exact statement and 2023 typographical correction were inspected
2026-10-09. This is an explicit retained theorem family on constructed objects. -/
def ProperStructureCohomologyFinite : Prop :=
  ∀ (K : Type u) [Field K] (X : FScheme K) (n : ℕ),
    IsProper X.hom → Module.Finite K (structureCohomology K X n)

end AlgebraicGeometry.Scheme
