/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FlatBaseChange.LiteralQuotient

/-! # Literal affine-open refinement of the original quotient chart

The refined ideal is the original mapped ideal and its source map is the
original quotient map followed by the original source chart. The principal
base-changed lift equality is proved from its two native projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

namespace ClosedImmersionAffineQuotientChart

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {R : CommRingCat.{u}}
  {a : Spec R ⟶ Y} (C : ClosedImmersionAffineQuotientChart i R a)

/-- Refine the SAME quotient chart along an actual affine-open ring map.
The source and ideal are literal, and its square is the original pasted pullback. -/
def affineOpenRefinement (S : CommRingCat.{u}) [Algebra R S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    ClosedImmersionAffineQuotientChart i S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ a) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S))))) :=
    MorphismProperty.of_isPullback (quotientChart_isPullback R S C.ideal).flip inferInstance
  exact
    { ideal := C.ideal.map (algebraMap R S)
      sourceMap := Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))) ≫ C.sourceMap
      isOpenImmersion := inferInstance
      square := (quotientChart_isPullback R S C.ideal).paste_horiz C.square }

@[simp]
theorem affineOpenRefinement_ideal (S : CommRingCat.{u}) [Algebra R S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (C.affineOpenRefinement S).ideal = C.ideal.map (algebraMap R S) := rfl

@[simp]
theorem affineOpenRefinement_sourceMap (S : CommRingCat.{u}) [Algebra R S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (C.affineOpenRefinement S).sourceMap = Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))) ≫ C.sourceMap := rfl

end ClosedImmersionAffineQuotientChart

end AlgebraicGeometry.Scheme.Modules
