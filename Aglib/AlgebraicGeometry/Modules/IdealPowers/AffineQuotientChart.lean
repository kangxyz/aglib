/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientSections

/-! # Quotient-section comparison linear over the actual affine coordinate ring -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]
  (J : Ideal A) (U : X.affineOpens)

local notation "α" => idealThickeningBaseScalar f
/-- The chart-ring submodule defining the original structural quotient. -/
abbrev idealQuotientAffineChartSubmodule : Submodule Γ(X, U) Γ(F, U) :=
  J.map (idealSectionRingHom X α U.val) • ⊤

local notation "P" => idealQuotientAffineChartSubmodule f F J U

/-- The chart-linear quotient-section map is induced by the original reduction. -/
def idealQuotientAffineChartMap :
    (Γ(F, U) ⧸ P) →ₗ[Γ(X, U)] Γ(idealQuotient X α F J, U) := by
  refine (P).liftQ ((idealQuotientπ X α F J).val.app (op U.val)).hom ?_
  intro x hx
  have hx' : x ∈ idealSectionSpan X α F J U.val :=
    (idealSectionSpan_eq_smul X α F J U.val).symm ▸ hx
  have hx'' : x ∈ LinearMap.range ((idealMultipleι X α F J).val.app (op U.val)).hom :=
    (idealMultiple_affine_range X α F J U).symm ▸ hx'
  obtain ⟨y, rfl⟩ := hx''
  exact congrArg (fun k => k.app U.val y) (idealMultipleι_quotientπ X α F J)

@[simp]
theorem idealQuotientAffineChartMap_mk (x : Γ(F, U)) :
    idealQuotientAffineChartMap f F J U (Submodule.Quotient.mk x) =
      (idealQuotientπ X α F J).app U.val x := rfl

/-- The chart-linear map is bijective for the same original quotient sheaf. -/
theorem idealQuotientAffineChartMap_bijective :
    Function.Bijective (idealQuotientAffineChartMap f F J U) := by
  let := idealSectionModule X α F U.val
  let : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom A Γ(X, U) _
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    have hx : (Submodule.Quotient.mk x : Γ(F, U) ⧸
        (J • ⊤ : Submodule A Γ(F, U))) = 0 := by
      apply (idealQuotientAffineSectionsEquiv f F J U).injective
      simpa only [idealQuotientAffineSectionsEquiv_mk,
        idealQuotientAffineChartMap_mk, map_zero] using hq
    have hx' := (Submodule.Quotient.mk_eq_zero
      (J • ⊤ : Submodule A Γ(F, U))).mp hx
    change x ∈ (P).restrictScalars A
    erw [Submodule.restrictScalars_map_smul_eq]
    exact hx'
  · intro s
    obtain ⟨x, rfl⟩ := idealQuotientπ_affine_surjective f F J U s
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Canonical affine quotient sections, linear over the full chart ring. -/
def idealQuotientAffineChartEquiv :
    (Γ(F, U) ⧸ P) ≃ₗ[Γ(X, U)] Γ(idealQuotient X α F J, U) :=
  LinearEquiv.ofBijective (idealQuotientAffineChartMap f F J U)
    (idealQuotientAffineChartMap_bijective f F J U)

@[simp]
theorem idealQuotientAffineChartEquiv_mk (x : Γ(F, U)) :
    idealQuotientAffineChartEquiv f F J U (Submodule.Quotient.mk x) =
      (idealQuotientπ X α F J).app U.val x := rfl

end AlgebraicGeometry.Scheme.Modules
