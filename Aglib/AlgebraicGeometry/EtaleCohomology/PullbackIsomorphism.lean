/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-! # The original inverse image along a scheme isomorphism

Native identity and composition comparisons supply the quasi-inverse. The
original inverse-image functor is retained, so existing original Ext pullback
comparison applies without replacing the cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- The actual inverse-image functor of a scheme isomorphism is an equivalence. -/
def inverseImageEquivalenceOfIso {S X : Scheme.{u}} (e : S ≅ X) :
    AbelianSheaf.{u, u + 1} X ≌ AbelianSheaf.{u, u + 1} S :=
  CategoryTheory.Equivalence.mk (inverseImage e.hom) (inverseImage e.inv)
    ((inverseImageId X).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) e.inv_hom_id).symm ≪≫
      inverseImageComp e.hom e.inv)
    ((inverseImageComp e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : S ⟶ S => inverseImage f) e.hom_inv_id) ≪≫
      inverseImageId S)

instance inverseImage_isEquivalence_of_isIso {S X : Scheme.{u}} (f : S ⟶ X) [IsIso f] :
    (inverseImage f).IsEquivalence :=
  (inverseImageEquivalenceOfIso (asIso f)).isEquivalence_functor

end AlgebraicGeometry.Scheme.EtaleCohomology
