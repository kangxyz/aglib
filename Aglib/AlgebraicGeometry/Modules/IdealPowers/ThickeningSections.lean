/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections
public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Original sections on an ideal thickening

The actual base change by `Spec (A/J)` has pullback sections given by the
ordinary quotient of the original affine sections. This is an affine-sections
comparison, not a nonflat cohomology base-change assertion. Its forward map
retains the original geometric pullback unit.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (J : Ideal A)

/-- The actual ideal-thickening space. -/
abbrev idealThickeningSpace :=
  Limits.pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))

/-- The actual closed immersion of the ideal thickening. -/
abbrev idealThickeningι : idealThickeningSpace f J ⟶ X :=
  Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))

/-- The actual structure map of the thickening over the quotient ring. -/
abbrev idealThickeningStructure : idealThickeningSpace f J ⟶ Spec (CommRingCat.of (A ⧸ J)) :=
  Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))

/-- The original coefficient pulled back to the actual thickening. -/
abbrev idealThickeningCoefficient := (pullback (idealThickeningι f J)).obj F

/-- Original sections with the original structural base-ring action. -/
abbrev idealThickeningOriginalSections (U : X.Opens) :=
  (moduleSectionsPresheaf X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F).obj (op U)

/-- Actual sections of the pulled-back coefficient over the quotient ring. -/
abbrev idealThickeningSections (U : X.Opens) :=
  (moduleSectionsPresheaf (idealThickeningSpace f J)
    ((idealThickeningStructure f J).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom)
    (idealThickeningCoefficient f F J)).obj (op (idealThickeningι f J ⁻¹ᵁ U))

/-- The actual section base-change map in ordinary algebra tensor coordinates. -/
def idealThickeningSectionsMap (U : X.Opens) :
    (A ⧸ J) ⊗[A] idealThickeningOriginalSections f F U →ₗ[A ⧸ J]
      idealThickeningSections f F J U :=
  ((moduleSectionsBaseChangeMap f (Ideal.Quotient.mk J) F).app (op U)).hom.comp
    (ModuleCat.extendScalarsAlgebraIso A (A ⧸ J)
      (idealThickeningOriginalSections f F U)).symm.toLinearEquiv.toLinearMap

/-- Unit pure tensors are the original geometric pullback unit. -/
theorem idealThickeningSectionsMap_one_tmul (U : X.Opens)
    (s : idealThickeningOriginalSections f F U) :
    idealThickeningSectionsMap f F J U ((1 : A ⧸ J) ⊗ₜ[A] s) =
      (((pullbackPushforwardAdjunction (idealThickeningι f J)).unit.app F).app U) s := by
  change (moduleSectionsBaseChangeMap f (Ideal.Quotient.mk J) F).app (op U)
    ((ModuleCat.extendScalarsAlgebraIso A (A ⧸ J)
      (idealThickeningOriginalSections f F U)).inv ((1 : A ⧸ J) ⊗ₜ[A] s)) = _
  rw [ModuleCat.extendScalarsAlgebraIso_inv_tmul]
  exact moduleSectionsBaseChangeMap_one_tmul f (Ideal.Quotient.mk J) F U s

variable [F.IsQuasicoherent]

/-- The canonical section tensor comparison is invertible on every affine open. -/
def idealThickeningSectionsTensorEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    (A ⧸ J) ⊗[A] idealThickeningOriginalSections f F U ≃ₗ[A ⧸ J]
      idealThickeningSections f F J U := by
  letI := moduleSectionsBaseChangeMap_isIso_app f (Ideal.Quotient.mk J) F U hU
  exact (ModuleCat.extendScalarsAlgebraIso A (A ⧸ J)
    (idealThickeningOriginalSections f F U)).symm.toLinearEquiv.trans
      (asIso ((moduleSectionsBaseChangeMap f (Ideal.Quotient.mk J) F).app (op U))).toLinearEquiv

/-- Actual affine thickening sections are the ordinary ideal quotient of
original sections, with restriction of the quotient-ring scalar action. -/
def idealThickeningSectionsQuotientEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    (idealThickeningOriginalSections f F U ⧸
      (J • (⊤ : Submodule A (idealThickeningOriginalSections f F U)))) ≃ₗ[A]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj
        (idealThickeningSections f F J U) := by
  letI : Module A (idealThickeningSections f F J U) :=
    Module.compHom _ (Ideal.Quotient.mk J)
  letI : IsScalarTower A (A ⧸ J) (idealThickeningSections f F J U) :=
    IsScalarTower.of_compHom A (A ⧸ J) _
  exact (TensorProduct.quotTensorEquivQuotSMul (idealThickeningOriginalSections f F U) J).symm.trans
    ((idealThickeningSectionsTensorEquiv f F J U hU).restrictScalars A)

/-- The quotient-section equivalence sends the original class of a section
to its original geometric pullback, including nonflat coefficients. -/
theorem idealThickeningSectionsQuotientEquiv_mk (U : X.Opens) (hU : IsAffineOpen U)
    (s : idealThickeningOriginalSections f F U) :
    idealThickeningSectionsQuotientEquiv f F J U hU (Submodule.Quotient.mk s) =
      (((pullbackPushforwardAdjunction (idealThickeningι f J)).unit.app F).app U) s := by
  have hs : Submodule.Quotient.mk s =
      TensorProduct.quotTensorEquivQuotSMul (idealThickeningOriginalSections f F U) J
        ((1 : A ⧸ J) ⊗ₜ[A] s) := by simp
  rw [hs]
  simp only [idealThickeningSectionsQuotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  change idealThickeningSectionsMap f F J U ((1 : A ⧸ J) ⊗ₜ[A] s) = _
  exact idealThickeningSectionsMap_one_tmul f F J U s

end AlgebraicGeometry.Scheme.Modules
