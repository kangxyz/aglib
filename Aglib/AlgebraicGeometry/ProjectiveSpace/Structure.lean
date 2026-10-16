/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The structure morphism of polynomial projective space

The degree-zero component of the polynomial grading is canonically the coefficient ring.
This identifies Mathlib's native `Proj.toSpecZero` with the projective-space structure morphism
to `Spec R`. For finitely many homogeneous coordinates that actual morphism is proper.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Coefficients embedded into the actual degree-zero component. -/
def toHomogeneousSubmoduleZero : R →+* homogeneousSubmodule ι R 0 where
  toFun r := ⟨C r, isHomogeneous_C ι r⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' r s := Subtype.ext (map_mul C r s)
  map_zero' := Subtype.ext (map_zero C)
  map_add' r s := Subtype.ext (map_add C r s)

/-- The coefficient ring is the degree-zero ring of the total-degree grading. -/
def homogeneousSubmoduleZeroEquiv : homogeneousSubmodule ι R 0 ≃+* R where
  toFun p := constantCoeff p.1
  invFun := toHomogeneousSubmoduleZero R ι
  left_inv p := by
    apply Subtype.ext
    exact (homogeneousComponent_zero p.1).symm.trans
      (homogeneousComponent_eq_self p.2)
  right_inv r := constantCoeff_C ι r
  map_mul' p q := map_mul constantCoeff p.1 q.1
  map_add' p q := map_add constantCoeff p.1 q.1

@[simp]
theorem homogeneousSubmoduleZeroEquiv_symm_apply (r : R) :
    (homogeneousSubmoduleZeroEquiv R ι).symm r = toHomogeneousSubmoduleZero R ι r := rfl

/-- Finitely many variables generate the polynomial algebra over its degree-zero component. -/
instance finiteType_homogeneousSubmoduleZero [Finite ι] :
    Algebra.FiniteType (homogeneousSubmodule ι R 0) (MvPolynomial ι R) := by
  let : IsScalarTower R (homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule ι R 0)
      (A := MvPolynomial ι R) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R _ _

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The structure map of polynomial projective space, induced by the inclusion of constants. -/
def toSpec : ProjectiveSpace R ι ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι R) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.toHomogeneousSubmoduleZero R ι))

/-- Polynomial projective space is separated for every coordinate type. -/
instance isSeparated : (ProjectiveSpace R ι).IsSeparated :=
  inferInstanceAs (Proj (MvPolynomial.homogeneousSubmodule ι R)).IsSeparated

/-- With finitely many coordinates, the actual projective-space structure map is proper. -/
instance isProper_toSpec [Finite ι] : IsProper (toSpec R ι) := by
  have : IsIso (CommRingCat.ofHom (MvPolynomial.toHomogeneousSubmoduleZero R ι)) := by
    change IsIso (MvPolynomial.homogeneousSubmoduleZeroEquiv R ι).toCommRingCatIso.inv
    infer_instance
  dsimp only [toSpec]
  infer_instance

/-- Projective space with finitely many coordinates is locally Noetherian over a Noetherian ring. -/
instance isLocallyNoetherian [Finite ι] [IsNoetherianRing R] :
    IsLocallyNoetherian (ProjectiveSpace R ι) :=
  LocallyOfFiniteType.isLocallyNoetherian (toSpec R ι)

/-- The coordinate chart maps to the base by the actual inclusion of constants into its
homogeneous localization. -/
@[reassoc]
theorem coordinateChart_toSpec (i : ι) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ≫ toSpec R ι =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι R)
          (Submonoid.powers (MvPolynomial.X i))).comp
            (MvPolynomial.toHomogeneousSubmoduleZero R ι))) := by
  rw [toSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end AlgebraicGeometry.ProjectiveSpace
