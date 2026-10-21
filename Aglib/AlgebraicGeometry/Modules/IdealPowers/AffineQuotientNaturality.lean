/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientSections
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Restriction and transition laws for affine quotient sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]

local notation "α" => idealThickeningBaseScalar f

/-- Affine quotient-section comparisons retain actual restriction maps. -/
theorem idealQuotientAffineSectionsEquiv_restrict (J : Ideal A)
    (U V : X.affineOpens) (i : V.val ⟶ U.val) :
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α F V.val
    ∀ s : Γ(F, U.val) ⧸ (J • ⊤ : Submodule A (Γ(F, U.val))),
      idealQuotientAffineSectionsEquiv f F J V
        (((Cohomology.moduleSectionsPresheaf X α F).map i.op).hom.reduceModIdeal J s) =
      (idealQuotient X α F J).val.map i.op
        (idealQuotientAffineSectionsEquiv f F J U s) := by
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α F V.val
  intro s
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  simp only [LinearMap.reduceModIdeal_apply, idealQuotientAffineSectionsEquiv_mk]
  exact PresheafOfModules.naturality_apply (idealQuotientπ X α F J).val i.op s

/-- Changing the ideal commutes with the original coefficient quotient map. -/
theorem idealQuotientAffineSectionsEquiv_factor {J K : Ideal A} (h : J ≤ K)
    (U : X.affineOpens) :
    letI := idealSectionModule X α F U.val
    ∀ s : Γ(F, U.val) ⧸ (J • ⊤ : Submodule A (Γ(F, U.val))),
      idealQuotientAffineSectionsEquiv f F K U
        (Submodule.factor (Submodule.smul_mono_left h) s) =
      (idealQuotientMap X α F h).app U.val
        (idealQuotientAffineSectionsEquiv f F J U s) := by
  let := idealSectionModule X α F U.val
  intro s
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  simp only [idealQuotientAffineSectionsEquiv_mk]
  exact (congrArg (fun k => k.app U.val s) (idealQuotientπ_map X α F h)).symm

end AlgebraicGeometry.Scheme.Modules
