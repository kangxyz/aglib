/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup

/-! Naturality of an original roots-valued pairing on test sections. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Group.MultiplicativeGroup

attribute [local instance] Over.cartesianMonoidalCategory

/-- Restricting both test points pulls back the actual unit of the original pairing. -/
theorem rootsValue_pair_naturality {X : Scheme.{u}} (n : ℕ) {A B T U : Over X}
    (p : A ⊗ B ⟶ rootsScheme X n) (f : U ⟶ T) (x : T ⟶ A) (y : T ⟶ B) :
    (rootsHomEquiv X n U (lift (f ≫ x) (f ≫ y) ≫ p)).val =
      Units.map f.left.appTop.hom.toMonoidHom (rootsHomEquiv X n T (lift x y ≫ p)).val := by
  have h : f ≫ (lift x y ≫ p) = lift (f ≫ x) (f ≫ y) ≫ p :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ p) (comp_lift f x y))
  have hv := congrArg Subtype.val ((rootsRepresentable X n).homEquiv_comp f (lift x y ≫ p))
  exact (congrArg (fun g => (rootsHomEquiv X n U g).val) h).symm.trans hv

end AlgebraicGeometry.Scheme.Group.MultiplicativeGroup
