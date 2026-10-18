/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalInversion
public import Aglib.FieldTheory.RationalCoefficientRoot

/-!
# The actual rational-function norm for a specified constant presentation

Transport the polynomial-presentation norm along the proved literal root-field
identification. This supplies the rational norm in the finite norm diamond;
it does not declare general presentation independence or a norm tower law.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open scoped RatFunc

attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k]

/-- The irreducible literal constant presentation over the rational-function field. -/
def rationalCoefficientPolynomial (p : MonicIrreducible k) : MonicIrreducible (RatFunc k) :=
  ⟨p.val.map RatFunc.C, p.property.1.map _,
    p.property.1.irreducible_map_ratFunc_C p.property.2⟩

local instance (p : MonicIrreducible k) :
    Fact (Irreducible (p.val.map (algebraMap k (RatFunc k)))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

local instance (p : MonicIrreducible k) :
    Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

/-- The norm on the actual rational-function field for the specified presentation. -/
def rationalFunctionNorm (n : ℕ) (p : MonicIrreducible k) :
    K (RatFunc (AdjoinRoot p.val)) n →ₗ[ℤ] K (RatFunc k) n :=
  (polynomialNorm n (rationalCoefficientPolynomial p)).comp
    (map n (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom)

/-- The inverse root-field identification sends constants to the literal quotient map. -/
theorem rationalCoefficientAlgEquiv_symm_comp_C (p : MonicIrreducible k) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom.comp
      (RatFunc.C : AdjoinRoot p.val →+* RatFunc (AdjoinRoot p.val)) =
        adjoinRootMap (RatFunc.C : k →+* RatFunc k) p.val
          (rationalCoefficientPolynomial p).val dvd_rfl := by
  apply RingHom.ext
  intro x
  apply (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).injective
  change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm (RatFunc.C x)) = _
  rw [AlgEquiv.apply_symm_apply]
  change RatFunc.C x = (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    (adjoinRootMap (algebraMap k (RatFunc k)) p.val
      (p.val.map (algebraMap k (RatFunc k))) dvd_rfl x)
  rw [adjoinRootMap_eq_coefficientMap]
  exact (AdjoinRoot.rationalCoefficientAlgEquiv_coefficientMap p.val p.property.1 x).symm

/-- On actual constant classes the rational norm is the literal restriction of
its original polynomial norm, in every degree. -/
theorem rationalFunctionNorm_map_C [CharZero k]
    (n : ℕ) (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) n) :
    rationalFunctionNorm n p (map n RatFunc.C x) = map n RatFunc.C (polynomialNorm n p x) := by
  rw [polynomialNorm_restrict_irreducible RatFunc.C n p
    (rationalCoefficientPolynomial p) rfl]
  apply congrArg (polynomialNorm n (rationalCoefficientPolynomial p))
  have hm := LinearMap.congr_fun (map_comp n
    (RatFunc.C : AdjoinRoot p.val →+* RatFunc (AdjoinRoot p.val))
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom) x
  rw [rationalCoefficientAlgEquiv_symm_comp_C] at hm
  exact hm.symm

/-- The inverse rational root identification intertwines the literal inversions. -/
theorem rationalCoefficientAlgEquiv_symm_comp_inversion (p : MonicIrreducible k) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom.comp
      (RatFunc.inversion (AdjoinRoot p.val)).toRingHom =
        (adjoinRootMap (RatFunc.inversion k).toRingHom
          (rationalCoefficientPolynomial p).val (rationalCoefficientPolynomial p).val
          (by rw [show (rationalCoefficientPolynomial p).val = p.val.map RatFunc.C from rfl,
            polynomial_map_inversion_map_C])).comp
          (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom := by
  apply RingHom.ext
  intro x
  apply (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).injective
  change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm
      (RatFunc.inversion (AdjoinRoot p.val) x)) = _
  rw [AlgEquiv.apply_symm_apply]
  have h := RingHom.congr_fun
    (AdjoinRoot.rationalCoefficientAlgEquiv_comp_inversion p.val p.property.1)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)
  change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    (adjoinRootMap (RatFunc.inversion k).toRingHom (p.val.map RatFunc.C)
      (p.val.map RatFunc.C) _
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) =
        RatFunc.inversion (AdjoinRoot p.val)
          ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
            ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- Rational inversion commutes with the norm on the original rational-function
fields, not merely on their auxiliary polynomial quotient presentations. -/
theorem rationalFunctionNorm_inversion [CharZero k]
    (n : ℕ) (p : MonicIrreducible k) (x : K (RatFunc (AdjoinRoot p.val)) n) :
    map n (RatFunc.inversion k).toRingHom (rationalFunctionNorm n p x) =
      rationalFunctionNorm n p (map n (RatFunc.inversion (AdjoinRoot p.val)).toRingHom x) := by
  unfold rationalFunctionNorm
  simp only [LinearMap.comp_apply]
  rw [polynomialNorm_inversion _ (polynomial_map_inversion_map_C p.val)]
  apply congrArg (polynomialNorm n (rationalCoefficientPolynomial p))
  have h := congrArg (map n) (rationalCoefficientAlgEquiv_symm_comp_inversion p)
  unfold rationalCoefficientPolynomial at h ⊢
  rw [map_comp, map_comp] at h
  exact (LinearMap.congr_fun h x).symm

end MilnorK.PolynomialNorm
