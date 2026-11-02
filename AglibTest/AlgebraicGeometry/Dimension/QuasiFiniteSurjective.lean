/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective`

Strict monotonicity of locally quasi-finite morphisms for specialization, surjectivity from the
local dimension, and the finite-endomorphism case; axiom guards.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.DimensionQuasiFiniteSurjective

/-- A locally quasi-finite morphism maps a strict generalization to a strict generalization. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] {x y : X} (h : x < y) :
    f x < f y :=
  f.strictMono_of_locallyQuasiFinite h

/-- Surjectivity from the local dimension, for a universally closed locally quasi-finite map. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [UniversallyClosed f]
    [IrreducibleSpace Y] (x : X)
    (hle : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : ringKrullDim (X.presheaf.stalk x) < ⊤) : Surjective f :=
  f.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top
    f.isClosedMap.isClosed_range x hle hfin

/-- A finite endomorphism of an irreducible locally Noetherian scheme fixing a point is
surjective. -/
example {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IrreducibleSpace X] [IsLocallyNoetherian X]
    {x : X} (hx : f x = x) : Surjective f :=
  f.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq f.isClosedMap.isClosed_range hx

/--
info: 'AlgebraicGeometry.Scheme.Hom.strictMono_of_locallyQuasiFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.strictMono_of_locallyQuasiFinite

/--
info: 'AlgebraicGeometry.Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top

/--
info: 'AlgebraicGeometry.Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq

end AglibTest.DimensionQuasiFiniteSurjective
