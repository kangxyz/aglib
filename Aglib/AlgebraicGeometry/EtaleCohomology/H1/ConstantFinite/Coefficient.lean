/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic

/-!
# Constant abelian coefficients on the small étale site

The original lifted value and native constant abelian sheaf are shared by
finite representation and cohomology consumers.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w w'

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- The finite additive value in the native sheaf-value universe. -/
abbrev value : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)

/-- The actual native constant abelian sheaf with the displayed finite value. -/
abbrev coefficient (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj (value A)

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
