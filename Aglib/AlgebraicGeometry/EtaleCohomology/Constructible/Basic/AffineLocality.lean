/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackQcqs

/-! # Affine locality for the original abelian constructibility predicate

Constructibility of every original affine-open inverse image supplies an
actual partition on that same affine open by the qcqs partition producer.
The entire family is assembled for a variable original coefficient before
specializing to any direct image. No new local coefficient models are used.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- Affine-local constructibility of the original restrictions gives the
original constructibility predicate by actual partitions on those opens. -/
theorem isConstructible_of_affineOpenPullbacks
    {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}
    (hF : ∀ U : X.affineOpens, IsConstructible ((inverseImage U.1.ι).obj F)) :
    IsConstructible F := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact nonempty_constructiblePartition_of_qcqs (hF U)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
