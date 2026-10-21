/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.RingTheory.ReesAlgebra.ModuleImage
public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-!
# Canonical affine coordinates for the geometric Rees unit

Two arbitrary affine base changes and the native tensor cancellation identify
sections of the iterated polynomial pullback with polynomial coefficients.
These coordinates retain the original unit, even for nonflat coefficients.
-/

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

/-- The actual sections of the original coefficient with its structural action. -/
abbrev originalSections (U : X.Opens) :=
  (moduleSectionsPresheaf X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F).obj (op U)

/-- The actual sections on the Rees base change. -/
abbrev pulledSections (U : X.Opens) :=
  (moduleSectionsPresheaf (space I f)
    ((structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
    (pulledCoefficient I f F)).obj (op (projection I f ⁻¹ᵁ U))

/-- Canonical Rees scalar-extension coordinates, without a flatness hypothesis. -/
def pulledSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    reesAlgebra I ⊗[A] originalSections f F U ≃ₗ[reesAlgebra I]
      pulledSections I f F U := by
  let := moduleSectionsBaseChangeMap_isIso_app f (algebraMap A (reesAlgebra I)) F U hU
  exact (ModuleCat.extendScalarsAlgebraIso A (reesAlgebra I)
    (originalSections f F U)).symm.toLinearEquiv ≪≫ₗ
    (asIso ((moduleSectionsBaseChangeMap f
    (algebraMap A (reesAlgebra I)) F).app (op U))).toLinearEquiv

/-- Pure tensors use the original geometric section comparison. -/
theorem pulledSectionsEquiv_tmul (U : X.Opens) (hU : IsAffineOpen U)
    (b : reesAlgebra I) (m : originalSections f F U) :
    pulledSectionsEquiv I f F U hU (b ⊗ₜ[A] m) =
      (moduleSectionsBaseChangeMap f (algebraMap A (reesAlgebra I)) F).app (op U)
        (b ⊗ₜ[A,algebraMap A (reesAlgebra I)] m) := by
  change (moduleSectionsBaseChangeMap f (algebraMap A (reesAlgebra I)) F).app (op U)
    ((ModuleCat.extendScalarsAlgebraIso A (reesAlgebra I) (originalSections f F U)).inv
      (b ⊗ₜ[A] m)) = _
  rw [ModuleCat.extendScalarsAlgebraIso_inv_tmul]

/-- The structural map from the iterated polynomial base change. -/
abbrev polynomialStructure : polynomialSpace I f ⟶ Spec (CommRingCat.of (Polynomial A)) :=
  Limits.pullback.snd _ _

/-- Actual sections of the polynomial pullback, with the polynomial-ring action. -/
abbrev polynomialSections (U : X.Opens) :=
  (moduleSectionsPresheaf (polynomialSpace I f)
    ((polynomialStructure I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv.hom)
    ((pullback (polynomialProjection I f)).obj (pulledCoefficient I f F))).obj
      (op (polynomialProjection I f ⁻¹ᵁ (projection I f ⁻¹ᵁ U)))

/-- Canonical scalar-extension coordinates for the second affine base change. -/
def polynomialSectionsTensorEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    Polynomial A ⊗[reesAlgebra I] pulledSections I f F U ≃ₗ[Polynomial A]
      polynomialSections I f F U := by
  let := moduleSectionsBaseChangeMap_isIso_app (structureMap I f)
    (reesAlgebra I).val.toRingHom (pulledCoefficient I f F)
    (projection I f ⁻¹ᵁ U) (hU.preimage (projection I f))
  exact (asIso ((moduleSectionsBaseChangeMap (structureMap I f)
    (reesAlgebra I).val.toRingHom (pulledCoefficient I f F)).app
      (op (projection I f ⁻¹ᵁ U)))).toLinearEquiv

/-- Polynomial coordinates on the actual iterated pullback sections. -/
def polynomialSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    polynomialSections I f F U ≃ₗ[Polynomial A]
      PolynomialModule A (originalSections f F U) :=
  (polynomialSectionsTensorEquiv I f F U hU).symm ≪≫ₗ
    (pulledSectionsEquiv I f F U hU).symm.baseChange (reesAlgebra I) (Polynomial A) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (reesAlgebra I) (Polynomial A)
      (Polynomial A) (originalSections f F U) ≪≫ₗ
    PolynomialModule.polynomialTensorProductLEquivPolynomialModule A (originalSections f F U)

/-- The second geometric pullback unit is the unit pure tensor in these coordinates. -/
theorem polynomialSectionsTensorEquiv_one_tmul (U : X.Opens) (hU : IsAffineOpen U)
    (m : pulledSections I f F U) :
    polynomialSectionsTensorEquiv I f F U hU ((1 : Polynomial A) ⊗ₜ[reesAlgebra I] m) =
      (((pullbackPushforwardAdjunction (polynomialProjection I f)).unit.app
        (pulledCoefficient I f F)).app (projection I f ⁻¹ᵁ U)) m :=
  moduleSectionsBaseChangeMap_one_tmul (structureMap I f) (reesAlgebra I).val.toRingHom
    (pulledCoefficient I f F) (projection I f ⁻¹ᵁ U) m

/-- The original geometric unit is precisely the canonical Rees tensor image map. -/
theorem polynomialSectionsEquiv_unit (U : X.Opens) (hU : IsAffineOpen U)
    (x : reesAlgebra I ⊗[A] originalSections f F U) :
    polynomialSectionsEquiv I f F U hU
      ((((pullbackPushforwardAdjunction (polynomialProjection I f)).unit.app
        (pulledCoefficient I f F)).app (projection I f ⁻¹ᵁ U))
          (pulledSectionsEquiv I f F U hU x)) =
      reesAlgebra.moduleImageMap I (originalSections f F U) x := by
  rw [← polynomialSectionsTensorEquiv_one_tmul I f F U hU]
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    simp [polynomialSectionsEquiv, reesAlgebra.moduleImageMap,
      PolynomialModule.polynomialTensorProductLEquivPolynomialModule]
  | add x y hx hy =>
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy

end AlgebraicGeometry.Scheme.Modules.Rees
