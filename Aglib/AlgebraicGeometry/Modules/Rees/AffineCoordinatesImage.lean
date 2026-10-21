/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.AffineCoordinates
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections

/-! # Actual affine sections of the geometric Rees coefficient -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.Rees

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]

/-- Actual affine chart sections of the image coefficient, with structural Rees scalars. -/
abbrev coefficientSections (U : X.Opens) :=
  (moduleSectionsPresheaf (space I f)
    ((structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
    (coefficient I f F)).obj (op (projection I f ⁻¹ᵁ U))

/-- The original image inclusion followed by canonical polynomial coordinates. -/
def coefficientSectionsToPolynomial (U : X.Opens) (hU : IsAffineOpen U) :
    coefficientSections I f F U →ₗ[reesAlgebra I]
      PolynomialModule A (originalSections f F U) :=
  (polynomialSectionsEquiv I f F U hU).restrictScalars (reesAlgebra I) |>.toLinearMap.comp
    (((moduleSectionsMapAlong (polynomialProjection I f)
      ((structureMap I f).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
      ((polynomialStructure I f).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv.hom)
      (reesAlgebra I).val.toRingHom
      (moduleSectionsBaseChangeScalars _ _ _ _ Limits.pullback.condition)
      (affineUnitImageι (polynomialProjection I f) (pulledCoefficient I f F))).app
        (op (projection I f ⁻¹ᵁ U))).hom)

/-- Normalization by the original quotient from the pulled-back coefficient. -/
theorem coefficientSectionsToPolynomial_toCoefficient (U : X.Opens) (hU : IsAffineOpen U)
    (x : reesAlgebra I ⊗[A] originalSections f F U) :
    coefficientSectionsToPolynomial I f F U hU
      ((toCoefficient I f F).app (projection I f ⁻¹ᵁ U)
        (pulledSectionsEquiv I f F U hU x)) =
      reesAlgebra.moduleImageMap I (originalSections f F U) x := by
  change polynomialSectionsEquiv I f F U hU
    ((affineUnitImageι (polynomialProjection I f) (pulledCoefficient I f F)).app
      (projection I f ⁻¹ᵁ U)
      ((toAffineUnitImage (polynomialProjection I f) (pulledCoefficient I f F)).app
        (projection I f ⁻¹ᵁ U) (pulledSectionsEquiv I f F U hU x))) = _
  have h := congrArg (fun k => k.app (projection I f ⁻¹ᵁ U)
      (pulledSectionsEquiv I f F U hU x))
    (toAffineUnitImage_ι (polynomialProjection I f) (pulledCoefficient I f F))
  exact (congrArg (polynomialSectionsEquiv I f F U hU) h).trans
    (polynomialSectionsEquiv_unit I f F U hU x)

/-- The affine coefficient quotient is surjective on sections. -/
theorem toCoefficient_sections_surjective (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((toCoefficient I f F).app (projection I f ⁻¹ᵁ U)) := by
  let := isQuasicoherent_pushforward_of_isAffineHom (polynomialProjection I f)
    ((pullback (polynomialProjection I f)).obj (pulledCoefficient I f F))
  let η : pulledCoefficient I f F ⟶
      (pushforward (polynomialProjection I f)).obj
        ((pullback (polynomialProjection I f)).obj (pulledCoefficient I f F)) :=
    (pullbackPushforwardAdjunction (polynomialProjection I f)).unit.app
      (pulledCoefficient I f F)
  exact affineOpenSections_factorThruImage_surjective
    ⟨projection I f ⁻¹ᵁ U, hU.preimage (projection I f)⟩ η

/-- The canonical inclusion is injective, because it is the actual image inclusion. -/
theorem coefficientSectionsToPolynomial_injective (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Injective (coefficientSectionsToPolynomial I f F U hU) := by
  let : Mono (affineUnitImageι (polynomialProjection I f) (pulledCoefficient I f F)) :=
    inferInstanceAs (Mono (Abelian.image.ι
      ((pullbackPushforwardAdjunction (polynomialProjection I f)).unit.app
        (pulledCoefficient I f F))))
  apply (polynomialSectionsEquiv I f F U hU).injective.comp
  exact moduleHom_app_injective
    (affineUnitImageι (polynomialProjection I f) (pulledCoefficient I f F))
    (projection I f ⁻¹ᵁ U)

/-- Its range is the native adic Rees submodule, not the scalar-extension source. -/
theorem range_coefficientSectionsToPolynomial (U : X.Opens) (hU : IsAffineOpen U) :
    LinearMap.range (coefficientSectionsToPolynomial I f F U hU) =
      (I.stableFiltration (⊤ : Submodule A (originalSections f F U))).submodule := by
  rw [← reesAlgebra.range_moduleImageMap]
  ext z
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨n, rfl⟩ := toCoefficient_sections_surjective I f F U hU m
    obtain ⟨x, rfl⟩ := (pulledSectionsEquiv I f F U hU).surjective n
    exact ⟨x, (coefficientSectionsToPolynomial_toCoefficient I f F U hU x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(toCoefficient I f F).app (projection I f ⁻¹ᵁ U)
      (pulledSectionsEquiv I f F U hU x),
      coefficientSectionsToPolynomial_toCoefficient I f F U hU x⟩

/-- Canonical affine coordinates identify the actual image coefficient with the
native adic Rees submodule, retaining the original inclusion. -/
def coefficientSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    coefficientSections I f F U ≃ₗ[reesAlgebra I]
      (I.stableFiltration (⊤ : Submodule A (originalSections f F U))).submodule :=
  LinearEquiv.ofInjective (coefficientSectionsToPolynomial I f F U hU)
    (coefficientSectionsToPolynomial_injective I f F U hU) ≪≫ₗ
      LinearEquiv.ofEq _ _ (range_coefficientSectionsToPolynomial I f F U hU)

/-- The forward map is exactly the geometric inclusion in polynomial coordinates. -/
@[simp]
theorem coefficientSectionsEquiv_val (U : X.Opens) (hU : IsAffineOpen U)
    (m : coefficientSections I f F U) :
    (coefficientSectionsEquiv I f F U hU m).val =
      coefficientSectionsToPolynomial I f F U hU m := rfl

/-- Homogeneous monomials act through the original structural Rees action. -/
theorem coefficientSectionsEquiv_monomial_smul (U : X.Opens) (hU : IsAffineOpen U)
    (r : ℕ) (a : A) (ha : a ∈ I ^ r) (m : coefficientSections I f F U) :
    (coefficientSectionsEquiv I f F U hU
      ((⟨Polynomial.monomial r a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) • m)).val =
      Polynomial.monomial r a • (coefficientSectionsEquiv I f F U hU m).val := by
  exact congrArg Subtype.val ((coefficientSectionsEquiv I f F U hU).map_smul
    (⟨Polynomial.monomial r a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) m)

end AlgebraicGeometry.Scheme.Modules.Rees
