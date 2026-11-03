/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.DegreeOne
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Native polynomial extension of a degree-one linear equivalence

The original homogeneous degree-one basis and native evaluation extend a
linear map, and an inverse linear map gives the inverse polynomial map.
The coefficient semiring and both variable universes are arbitrary.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommSemiring R] {ι : Type v} {κ : Type w}

/-- Extend the actual degree-one linear map by native polynomial evaluation. -/
def degreeOneLinearMapAlgHom
    (f : homogeneousSubmodule ι R 1 →ₗ[R] homogeneousSubmodule κ R 1) :
    MvPolynomial ι R →ₐ[R] MvPolynomial κ R :=
  aeval fun i => (f (homogeneousDegreeOneBasis R ι i)).val

/-- Every original variable has its supplied original degree-one image. -/
theorem degreeOneLinearMapAlgHom_X
    (f : homogeneousSubmodule ι R 1 →ₗ[R] homogeneousSubmodule κ R 1) (i : ι) :
    degreeOneLinearMapAlgHom f (X i) = (f (homogeneousDegreeOneBasis R ι i)).val :=
  aeval_X _ _

/-- On the original degree-one submodule this is exactly the given linear map. -/
theorem degreeOneLinearMapAlgHom_apply
    (f : homogeneousSubmodule ι R 1 →ₗ[R] homogeneousSubmodule κ R 1)
    (p : homogeneousSubmodule ι R 1) : degreeOneLinearMapAlgHom f p.val = (f p).val := by
  have h : (degreeOneLinearMapAlgHom f).toLinearMap.comp
      (homogeneousSubmodule ι R 1).subtype =
        (homogeneousSubmodule κ R 1).subtype.comp f := by
    apply (homogeneousDegreeOneBasis R ι).ext
    intro i
    change degreeOneLinearMapAlgHom f (homogeneousDegreeOneBasis R ι i).val =
      (f (homogeneousDegreeOneBasis R ι i)).val
    rw [homogeneousDegreeOneBasis_val]
    exact degreeOneLinearMapAlgHom_X f i
  exact LinearMap.congr_fun h p

/-- The original extension and the extension of the actual inverse are inverse maps. -/
theorem degreeOneLinearMapAlgHom_comp_symm
    (e : homogeneousSubmodule ι R 1 ≃ₗ[R] homogeneousSubmodule κ R 1) :
    (degreeOneLinearMapAlgHom e.toLinearMap).comp
      (degreeOneLinearMapAlgHom e.symm.toLinearMap) = AlgHom.id R _ := by
  apply algHom_ext
  intro i
  change degreeOneLinearMapAlgHom e.toLinearMap
    (degreeOneLinearMapAlgHom e.symm.toLinearMap (X i)) = X i
  rw [degreeOneLinearMapAlgHom_X, degreeOneLinearMapAlgHom_apply]
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    homogeneousDegreeOneBasis_val]

/-- Extend the supplied degree-one linear equivalence on the same native polynomials. -/
def degreeOneLinearEquivAlgEquiv
    (e : homogeneousSubmodule ι R 1 ≃ₗ[R] homogeneousSubmodule κ R 1) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial κ R :=
  AlgEquiv.ofAlgHom (degreeOneLinearMapAlgHom e.toLinearMap)
    (degreeOneLinearMapAlgHom e.symm.toLinearMap)
    (degreeOneLinearMapAlgHom_comp_symm e) (degreeOneLinearMapAlgHom_comp_symm e.symm)

/-- The polynomial equivalence retains its literal original degree-one restriction. -/
theorem degreeOneLinearEquivAlgEquiv_apply
    (e : homogeneousSubmodule ι R 1 ≃ₗ[R] homogeneousSubmodule κ R 1)
    (p : homogeneousSubmodule ι R 1) : degreeOneLinearEquivAlgEquiv e p.val = (e p).val :=
  degreeOneLinearMapAlgHom_apply e.toLinearMap p

/-- The same native extension preserves every original homogeneous degree. -/
theorem degreeOneLinearEquivAlgEquiv_isHomogeneous
    (e : homogeneousSubmodule ι R 1 ≃ₗ[R] homogeneousSubmodule κ R 1)
    {n : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous n) :
    (degreeOneLinearEquivAlgEquiv e p).IsHomogeneous n := by
  change (aeval (fun i => (e (homogeneousDegreeOneBasis R ι i)).val) p).IsHomogeneous n
  simpa only [one_mul] using hp.aeval
    (fun i => (e (homogeneousDegreeOneBasis R ι i)).val)
    (fun i => (e (homogeneousDegreeOneBasis R ι i)).property)

end MvPolynomial
