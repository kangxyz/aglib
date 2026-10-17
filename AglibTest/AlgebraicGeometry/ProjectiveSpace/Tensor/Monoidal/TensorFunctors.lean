/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.TensorFunctors
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.TwistMultiplication
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.CoordinateGeneration

/-! Focused consumer of the twist tensor functor comparisons. The outer and inner comparisons
attempted in the Hilbert-polynomial regularity work, stated verbatim with `twistingTensorMultiply`
and with the transport of twist tensor functors written out, are the library lemmas
`twistingTensorMultiply_app_tensor_comp` and `twistingTensorMultiply_map_tensor_comp`. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The components of `twistingTensorMultiply` are whiskerings of the unit multiplication. -/
example (a d : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤)) (F : (ProjectiveSpace R ι).Modules) :
    (twistingTensorMultiply R ι a d s).app F =
      (unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι d) ≫
        twistingTensorMap R ι a d) ▷ F :=
  congrArg (· ▷ F) (twistingMultiplyGlobal_eq_unitMultiply R ι a d s)

/-- The components of `twistingTensorMultiplyTo` are whiskerings of the unit multiplication
followed by the transport to the free target degree. -/
example (a d d' : ℤ) (h : a + d = d') (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) :
    (twistingTensorMultiplyTo R a d d' h s).app F =
      (unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι d) ≫
        twistingTensorMap R ι a d ≫ eqToHom (congrArg (twistingSheaf R ι) h)) ▷ F :=
  congrArg (· ▷ F) ((twistingMultiplyGlobal_eq_unitMultiply R ι a d s).symm ▸ rfl)

/-- Multiplying the outer twist factor is multiplication on the merged twist. -/
example (a d b : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) (h : a + (d + b) = a + d + b) :
    (twistingTensorMultiply R ι a d s).app
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F) ≫
      (twistingTensorCompIso R ι (a + d) b).hom.app F =
    (twistingTensorCompIso R ι d b).hom.app F ≫ (twistingTensorMultiply R ι a (d + b) s).app F ≫
      (eqToIso (congrArg (fun k => moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F :=
  twistingTensorMultiply_app_tensor_comp R ι a d b s F h

/-- Multiplying the inner twist factor is multiplication on the merged twist. -/
example (a e b : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) (h : a + (e + b) = e + (a + b)) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).map
        ((twistingTensorMultiply R ι a b s).app F) ≫
      (twistingTensorCompIso R ι e (a + b)).hom.app F =
    (twistingTensorCompIso R ι e b).hom.app F ≫ (twistingTensorMultiply R ι a (e + b) s).app F ≫
      (eqToIso (congrArg (fun k => moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F :=
  twistingTensorMultiply_map_tensor_comp R ι a e b s F h

/-- The outer comparison at the concrete degrees `1 + (0 + 1)` and `1 + 0 + 1` of the cokernel
step, obtained by instantiating the comparison at variable degrees. -/
example (s : (twistingSheaf R ι 1).val.obj (op ⊤)) (F : (ProjectiveSpace R ι).Modules) :=
  twistingMultiplyGlobal_coefficientMap_app_tensor_comp R ι 1 0 1 s F (add_assoc 1 0 1).symm

/-- The same instance in the spelling of `twistingTensorMultiply`. -/
example (s : (twistingSheaf R ι 1).val.obj (op ⊤)) (F : (ProjectiveSpace R ι).Modules) :=
  twistingTensorMultiply_app_tensor_comp R ι 1 0 1 s F (add_assoc 1 0 1).symm

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorCompIso_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorCompIso_hom_app

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorFunctorCongr_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorFunctorCongr_hom_app

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_coefficientMap_app_tensor_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_coefficientMap_app_tensor_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_coefficientMap_map_tensor_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_coefficientMap_map_tensor_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_tensor_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_tensor_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_map_tensor_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_map_tensor_comp
