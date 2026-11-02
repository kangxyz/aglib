/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Commutative

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Group

universe u

example {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsCommMonObj G] :
    IsCommMonObj (identityComponentOver G) := inferInstance
