/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImageSections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf

/-!
# The actual finite-etale coefficient algebras on affine stage opens

For a finite-etale cover of an actual closed subscheme, the original ambient
pushforward sections are etale over the quotient of the original affine ring.
Any quotient scalar map satisfying the original factor equation is this same
map, by surjectivity of the original quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u
attribute [local instance] Modules.Algebra.inverseImageSectionsAlgebra
variable {X : Scheme.{u}} (K : X.IdealSheafData) (C : FiniteEtale K.subscheme)
  (U : X.affineOpens) (J : Ideal Γ(X, U)) (hJ : J = K.ideal U)

/-- The original closed-subscheme section comparison, with a named but
equal affine ideal for the consumer's literal quotient ring. -/
def stageBaseSectionsEquiv :
    (Γ(X, U) ⧸ J) ≃+* Γ(K.subscheme, K.subschemeι ⁻¹ᵁ U.val) :=
  (Ideal.quotEquivOfEq hJ).trans (K.subschemeObjIso U).commRingCatIsoToRingEquiv.symm

@[simp]
theorem stageBaseSectionsEquiv_mk (r : Γ(X, U)) :
    stageBaseSectionsEquiv K U J hJ (Ideal.Quotient.mk J r) = (K.subschemeι.app U.val) r := by
  rw [K.subschemeι_app U]
  rfl

/-- The original coefficient module, not a replacement tensor ring. -/
abbrev stageCoefficient : X.Modules :=
  Modules.pushforwardStructureSheaf (C.obj.hom ≫ K.subschemeι)

/-- The canonical quotient scalar into the original coefficient sections. -/
def stageCoefficientScalar : (Γ(X, U) ⧸ J) →+* Γ(stageCoefficient K C, U.val) :=
  (Modules.Algebra.pushforwardStructureSectionsAlgEquiv
    (C.obj.hom ≫ K.subschemeι) U.val).symm.toRingHom.comp
      ((C.obj.hom.app (K.subschemeι ⁻¹ᵁ U.val)).hom.comp
        (stageBaseSectionsEquiv K U J hJ).toRingHom)

/-- Its composition with the original quotient map is the original scalar map. -/
theorem stageCoefficientScalar_factor :
    (stageCoefficientScalar K C U J hJ).comp (Ideal.Quotient.mk J) =
      algebraMap Γ(X, U) Γ(stageCoefficient K C, U.val) := by
  ext r
  apply (Modules.Algebra.pushforwardStructureSectionsAlgEquiv
    (C.obj.hom ≫ K.subschemeι) U.val).injective
  change (Modules.Algebra.pushforwardStructureSectionsAlgEquiv
      (C.obj.hom ≫ K.subschemeι) U.val)
      ((Modules.Algebra.pushforwardStructureSectionsAlgEquiv
        (C.obj.hom ≫ K.subschemeι) U.val).symm
        ((C.obj.hom.app (K.subschemeι ⁻¹ᵁ U.val))
          (stageBaseSectionsEquiv K U J hJ (Ideal.Quotient.mk J r)))) = _
  rw [AlgEquiv.apply_symm_apply, stageBaseSectionsEquiv_mk,
    Modules.Algebra.pushforwardStructureSectionsAlgEquiv_algebraMap]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app C.obj.hom K.subschemeι U.val) r).symm

/-- Finite-etaleness of the original cover gives etaleness of its literal
ambient coefficient algebra over the original affine quotient. -/
theorem stageCoefficientScalar_etale : (stageCoefficientScalar K C U J hJ).Etale := by
  have hV : IsAffineOpen (K.subschemeι ⁻¹ᵁ U.val) := U.property.preimage K.subschemeι
  have hW : IsAffineOpen (C.obj.hom ⁻¹ᵁ (K.subschemeι ⁻¹ᵁ U.val)) :=
    hV.preimage C.obj.hom
  have hp : (C.obj.hom.app (K.subschemeι ⁻¹ᵁ U.val)).hom.Etale := by
    simpa only [Scheme.Hom.appLE_eq_app] using C.obj.hom.etale_appLE hV hW le_rfl
  have hq : (stageBaseSectionsEquiv K U J hJ).toRingHom.Etale :=
    RingHom.Etale.of_bijective (stageBaseSectionsEquiv K U J hJ).bijective
  have he : (Modules.Algebra.pushforwardStructureSectionsAlgEquiv
      (C.obj.hom ≫ K.subschemeι) U.val).symm.toRingHom.Etale :=
    RingHom.Etale.of_bijective
      (Modules.Algebra.pushforwardStructureSectionsAlgEquiv
        (C.obj.hom ≫ K.subschemeι) U.val).symm.bijective
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ hq hp) he

include hJ in
/-- The original factor equation uniquely identifies every quotient scalar.
This matches the scalar returned by the algebraization comparison without
changing that scalar or its underlying module ring. -/
theorem etale_of_original_quotientScalar
    (ρ : (Γ(X, U) ⧸ J) →+* Γ(stageCoefficient K C, U.val))
    (hρ : ρ.comp (Ideal.Quotient.mk J) =
      algebraMap Γ(X, U) Γ(stageCoefficient K C, U.val)) : ρ.Etale := by
  have heq : ρ = stageCoefficientScalar K C U J hJ := by
    apply RingHom.ext
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr := congrArg (fun g : Γ(X, U) →+* Γ(stageCoefficient K C, U.val) => g r)
      (hρ.trans (stageCoefficientScalar_factor K C U J hJ).symm)
    exact hr
  rw [heq]
  exact stageCoefficientScalar_etale K C U J hJ

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
