/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Thickening

/-!
# Affine sections of the original ideal quotient

The actual quotient coefficient has, on each affine open, the quotient of
original sections. The forward map is the original coefficient reduction.
No flatness, Noetherianity or completeness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]
  (J : Ideal A) (U : X.affineOpens)

local notation "α" => idealThickeningBaseScalar f

/-- The quotient of affine sections maps to sections of the actual quotient. -/
def idealQuotientAffineSectionsMap :
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α (idealQuotient X α F J) U.val
    (Γ(F, U.val) ⧸ (J • ⊤ : Submodule A (Γ(F, U.val)))) →ₗ[A]
      Γ(idealQuotient X α F J, U.val) := by
  letI := idealSectionModule X α F U.val
  letI := idealSectionModule X α (idealQuotient X α F J) U.val
  refine (J • ⊤ : Submodule A (Γ(F, U.val))).liftQ
    (idealSectionMap X α (idealQuotientπ X α F J) U.val) ?_
  intro x hx
  rw [← idealMultiple_affine_range_structural X α F J U] at hx
  obtain ⟨y, rfl⟩ := hx
  exact congrArg (fun k => k.app U.val y) (idealMultipleι_quotientπ X α F J)

@[simp]
theorem idealQuotientAffineSectionsMap_mk (s : Γ(F, U.val)) :
    letI := idealSectionModule X α F U.val
    idealQuotientAffineSectionsMap f F J U (Submodule.Quotient.mk s) =
      (idealQuotientπ X α F J).app U.val s := rfl

/-- The canonical affine quotient-section map is bijective. -/
theorem idealQuotientAffineSectionsMap_bijective :
    Function.Bijective (idealQuotientAffineSectionsMap f F J U) := by
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α (idealQuotient X α F J) U.val
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    apply (Submodule.Quotient.mk_eq_zero (J • ⊤ : Submodule A (Γ(F, U.val)))).mpr
    apply (idealThickeningUnit_eq_zero_iff f F J U.val U.property s).mp
    have h := congrArg (fun k => k.app U.val s)
      (idealQuotientπ_toThickening f F J)
    change (idealQuotientToThickening f F J).app U.val
      ((idealQuotientπ X α F J).app U.val s) =
        (idealThickeningUnit f F J).app U.val s at h
    rw [← h, ← idealQuotientAffineSectionsMap_mk f F J U, hq]
    exact map_zero _
  · intro s
    obtain ⟨s, rfl⟩ := idealQuotientπ_affine_surjective f F J U s
    exact ⟨Submodule.Quotient.mk s, rfl⟩

/-- Affine quotient sections, with the original structural action and reduction. -/
def idealQuotientAffineSectionsEquiv :
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α (idealQuotient X α F J) U.val
    (Γ(F, U.val) ⧸ (J • ⊤ : Submodule A (Γ(F, U.val)))) ≃ₗ[A]
      Γ(idealQuotient X α F J, U.val) :=
  LinearEquiv.ofBijective (idealQuotientAffineSectionsMap f F J U)
    (idealQuotientAffineSectionsMap_bijective f F J U)

@[simp]
theorem idealQuotientAffineSectionsEquiv_mk (s : Γ(F, U.val)) :
    letI := idealSectionModule X α F U.val
    idealQuotientAffineSectionsEquiv f F J U (Submodule.Quotient.mk s) =
      (idealQuotientπ X α F J).app U.val s := rfl

end AlgebraicGeometry.Scheme.Modules
