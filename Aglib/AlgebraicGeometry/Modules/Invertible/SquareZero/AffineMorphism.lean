/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.Affine
public import Aglib.AlgebraicGeometry.Modules.Pullback.Isomorphism
public import Aglib.CategoryTheory.Functor.IsoLifting
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Line-bundle lifting for an actual affine square-zero morphism

Transport through the canonical affine-spectrum isomorphisms preserves the
original scheme morphism in the pullback comparison. The square-zero and
surjectivity conditions concern its original map on global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X]

/-- Every line bundle on the source of an actual affine square-zero closed
immersion lifts, retaining the original geometric pullback functor. -/
theorem exists_lineBundle_lift_affine_of_square_zero (i : X₀ ⟶ X)
    (hsurj : Function.Surjective i.appTop.hom) (hi : RingHom.ker i.appTop.hom ^ 2 = ⊥)
    (L : LineBundle X₀) :
    ∃ L' : LineBundle X, Nonempty ((pullback i).obj L'.val ≅ L.val) := by
  let M := pullbackLineBundle X₀.isoSpec.inv L
  obtain ⟨N, ⟨e⟩⟩ := exists_lineBundle_lift_of_square_zero i.appTop hsurj hi M
  refine ⟨pullbackLineBundle X.isoSpec.hom N, ⟨?_⟩⟩
  exact (pullbackComp i X.isoSpec.hom).app N.val ≪≫
    (pullbackCongr (Scheme.isoSpec_hom_naturality i).symm).app N.val ≪≫
    ((pullbackComp X₀.isoSpec.hom (Spec.map i.appTop)).app N.val).symm ≪≫
    (pullback X₀.isoSpec.hom).mapIso e ≪≫
    (pullbackComp X₀.isoSpec.hom X₀.isoSpec.inv).app L.val ≪≫
    (pullbackCongr X₀.isoSpec.hom_inv_id).app L.val ≪≫
    (pullbackId X₀).app L.val

/-- A prescribed pullback isomorphism between line bundles lifts along
an actual affine square-zero morphism, with its forward map unchanged. -/
theorem exists_lineBundle_iso_lift_affine_of_square_zero (i : X₀ ⟶ X)
    (hsurj : Function.Surjective i.appTop.hom) (hi : RingHom.ker i.appTop.hom ^ 2 = ⊥)
    (L M : LineBundle X)
    (e : (pullback i).obj L.val ≅ (pullback i).obj M.val) :
    ∃ e' : L.val ≅ M.val, (pullback i).map e'.hom = e.hom := by
  let G := pullback X.isoSpec.inv
  let H := pullback X₀.isoSpec.inv
  let t : pullback i ⋙ H ≅ G ⋙ pullback (Spec.map i.appTop) :=
    pullbackComp X₀.isoSpec.inv i ≪≫
      pullbackCongr (Scheme.isoSpec_inv_naturality i).symm ≪≫
        (pullbackComp (Spec.map i.appTop) X.isoSpec.inv).symm
  apply Functor.exists_iso_lift_of_square (pullback i) (pullback (Spec.map i.appTop))
    G H (Functor.FullyFaithful.ofFullyFaithful G) t L.val M.val e
  intro e'
  exact exists_lineBundle_iso_lift_of_square_zero i.appTop hsurj hi
    (pullbackLineBundle X.isoSpec.inv L) (pullbackLineBundle X.isoSpec.inv M) e'

end AlgebraicGeometry.Scheme.Modules.Invertible
