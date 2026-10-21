/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-! # The actual residue range over a surjective parameter residue field

A surjective parameter residue map supplies scalar closure of the source image.
No action of that residue field on the original source ring is imposed.
-/

@[expose] public noncomputable section

namespace ResidueRange

variable {C A F L : Type*} [CommRing C] [CommRing A] [Field F] [Field L]
variable [Algebra F L]
variable (ψ : C →+* F) (hψ : Function.Surjective ψ) (η : C →+* A) (θ : A →+* L)
variable (h : θ.comp η = (algebraMap F L).comp ψ)

/-- The literal source image is a subalgebra because every ground-field scalar
has an actual preimage in the parameter ring. -/
def algebra : Subalgebra F L where
  toSubsemiring := θ.range.toSubsemiring
  algebraMap_mem' c := by
    obtain ⟨b, rfl⟩ := hψ c
    exact ⟨η b, DFunLike.congr_fun h b⟩

/-- The original source maps to its actual residue image. -/
def sourceMap : A →+* algebra ψ hψ η θ h :=
  θ.codRestrict (algebra ψ hψ η θ h).toSubring fun a => ⟨a, rfl⟩

/-- Inclusion of the range recovers the original point exactly. -/
@[simp] theorem coe_sourceMap (a : A) :
    (sourceMap ψ hψ η θ h a : L) = θ a := rfl

/-- The actual source-to-image map is surjective. -/
theorem sourceMap_surjective : Function.Surjective (sourceMap ψ hψ η θ h) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

/-- The source-to-image map preserves the actual parameter residue triangle. -/
theorem sourceMap_parameter (c : C) :
    sourceMap ψ hψ η θ h (η c) =
      algebraMap F (algebra ψ hψ η θ h) (ψ c) := by
  apply Subtype.ext
  exact DFunLike.congr_fun h c

/-- If actual source coordinates field-generate the target, that target is the
fraction field of the actual residue image. -/
theorem isFractionRing {σ : Type*} (x : σ → A)
    (hx : IntermediateField.adjoin F (Set.range (fun i => θ (x i))) = ⊤) :
    IsFractionRing (algebra ψ hψ η θ h) L := by
  let D := algebra ψ hψ η θ h
  have hle : Algebra.adjoin F (Set.range (fun i => θ (x i))) ≤ D := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ IntermediateField.adjoin F (Set.range (fun i => θ (x i))) := by
    rw [hx]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  exact ⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, hab⟩

end ResidueRange
