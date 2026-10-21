/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesLocalSections
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Multiplication

/-! # Original homogeneous Rees multiplication on affine sections -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Rees

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]

/-- Geometric Rees scalar multiplication is exactly the original ideal-power
coefficient map on every homogeneous affine section. -/
theorem homogeneousSectionMap_mul (r n : ℕ) (a : ↥(I ^ r))
    (U : X.Opens) (hU : IsAffineOpen U) (m : powerSections I f F n U) :
    homogeneousSectionMap I f F (r + n) U hU
      ((idealPowerMul X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        F I r n a).app U m) =
    (⟨Polynomial.monomial r a.val, reesAlgebra.monomial_mem.mpr a.property⟩ : reesAlgebra I) •
      homogeneousSectionMap I f F n U hU m := by
  apply (coefficientSectionsEquiv I f F U hU).injective
  apply Subtype.ext
  rw [coefficientSectionsEquiv_monomial_smul I f F U hU r a.val a.property,
    homogeneousSectionMap_polynomial, homogeneousSectionMap_polynomial,
    PolynomialModule.monomial_smul_single]
  congr 1
  have h := congrArg (fun k => k.app U m)
    (idealMultipleMul_ι X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      F (J := I ^ n) (K := I ^ (r + n)) a.val
      (fun b hb => by simpa only [pow_add] using Ideal.mul_mem_mul a.property hb))
  exact h.trans (globalScalarEndomorphism_app X F
    ((f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) a.val) U _)

end AlgebraicGeometry.Scheme.Modules.Rees
