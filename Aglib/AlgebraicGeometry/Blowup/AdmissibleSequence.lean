/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Admissible
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Actual admissible blowup sequences

This proposition records a finite sequence of native blowups with specified
centres, allowing source isomorphisms. It does not identify a composite with
one blowup, nor characterize arbitrary proper modifications.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Finite native blowup provenance, unchanged over the specified open. -/
inductive AdmissibleSequence {X : Scheme.{u}} (U : X.Opens) :
    {Y : Scheme.{u}} → (Y ⟶ X) → Prop
  | id : AdmissibleSequence U (𝟙 X)
  | step {Y : Scheme.{u}} {β : Y ⟶ X}
      (hβ : AdmissibleSequence U β) (J : Y.IdealSheafData) (B : BlowupDatum J)
      (hJ : J.comap (β ⁻¹ᵁ U).ι = ⊤) : AdmissibleSequence U (B.map ≫ β)
  | iso {Y Z : Scheme.{u}} {β : Y ⟶ X}
      (hβ : AdmissibleSequence U β) (e : Z ≅ Y) : AdmissibleSequence U (e.hom ≫ β)

namespace AdmissibleSequence

/-- A single native blowup with a unit centre on the protected open. -/
theorem single {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
    (U : X.Opens) (hI : I.comap U.ι = ⊤) : AdmissibleSequence U B.map := by
  simpa only [Category.comp_id] using
    (AdmissibleSequence.step (.id (U := U)) I B hI)

/-- Concatenation retains the actual composite and the pulled-back protected open. -/
theorem comp {X Y Z : Scheme.{u}} {U : X.Opens} {β : Y ⟶ X} {γ : Z ⟶ Y}
    (hβ : AdmissibleSequence U β) (hγ : AdmissibleSequence (β ⁻¹ᵁ U) γ) :
    AdmissibleSequence U (γ ≫ β) := by
  induction hγ with
  | id => simpa using hβ
  | @step T δ hδ J B hJ ih =>
      simpa only [Category.assoc] using AdmissibleSequence.step ih J B hJ
  | @iso T T' δ hδ e ih =>
      simpa only [Category.assoc] using AdmissibleSequence.iso ih e

/-- Properness follows for locally Noetherian bases, not by definition. -/
theorem isProper {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens} {β : Y ⟶ X} (hβ : AdmissibleSequence U β) : IsProper β := by
  induction hβ with
  | id => infer_instance
  | @step T δ hδ J B hJ ih =>
      let : IsProper δ := ih
      let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian δ
      let : IsProper B.map := B.isProper_of_isLocallyNoetherian
      infer_instance
  | iso hδ e ih =>
      let := ih
      infer_instance

/-- The literal restriction of the composite to its protected open is an isomorphism. -/
theorem restrict_isIso {X Y : Scheme.{u}} {U : X.Opens} {β : Y ⟶ X}
    (hβ : AdmissibleSequence U β) : IsIso (β ∣_ U) := by
  induction hβ with
  | id =>
      rw [morphismRestrict_id]
      exact (Iso.refl ((𝟙 X) ⁻¹ᵁ U).toScheme).isIso_hom
  | step hδ J B hJ ih =>
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' (B.restrict_isIso_of_comap_eq_top _ hJ) ih
  | @iso T T' δ hδ e ih =>
      have he : IsIso (e.hom ∣_ (δ ⁻¹ᵁ U)) := inferInstance
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' he ih

end AdmissibleSequence
end AlgebraicGeometry.Scheme.Blowup
