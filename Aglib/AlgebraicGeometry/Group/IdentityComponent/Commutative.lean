/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic
public import Aglib.CategoryTheory.Monoidal.CommMonObjOfMono

/-! # Commutativity of the original identity-component group law -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Group

/-- The native identity-component group law of a commutative group scheme is
commutative, by its actual monic group inclusion. -/
instance isCommMonObj_identityComponentOver
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsCommMonObj G] :
    IsCommMonObj (identityComponentOver G) :=
  IsCommMonObj.of_mono (identityComponentι G)

end AlgebraicGeometry.Scheme.Group
