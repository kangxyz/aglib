/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup.RootsInclusion

/-! The original Kummer inclusion is represented by the original roots inclusion. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group.MultiplicativeGroup

universe u

namespace GroupCohomology.Kummer.Coefficients

attribute [local instance] Over.cartesianMonoidalCategory

/-- The two descriptions give the same original coefficient morphism. -/
theorem representedSheafMap_rootsInclusionHom (X : Scheme.{u}) (n : ℕ) :
    representedSheafMap (rootsInclusionHom X n) = inclusion X n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ULift.ext
  apply Additive.toMul.injective
  change a.down.toMul ≫ (rootsInclusionHom X n).hom.hom =
    ((inclusion X n).hom.app U a).down.toMul
  rw [rootsInclusionHom_hom_hom]
  have h := @inclusion_apply_scheme X n U
  unfold mu at h
  exact (h a).symm

end GroupCohomology.Kummer.Coefficients
