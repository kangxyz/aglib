/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
Native extraction from `R5Lab.Aglib.AlgebraicGeometry.Stalk.Regular`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`e6a8de660e77bebcaba3a3cb8409422e4c3b1e828d64a4e5dea6223db10c2476`.
Only the three actual restriction-isomorphism lemmas are extracted.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

lemma isIso_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hUV : U ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have h : IsIso ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) := inferInstance
  have heq : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hUV]
  have hh := (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))
  rw [heq] at hh
  exact hh.mp h

lemma isIso_restrict_sup {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens)
    [IsIso (f ∣_ U)] [IsIso (f ∣_ V)] : IsIso (f ∣_ (U ⊔ V)) := by
  let W := U ⊔ V
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun b : Bool => W.ι ⁻¹ᵁ (if b then U else V))
  · ext x
    simpa [W, Scheme.Opens.ι_apply] using Or.symm x.property
  · intro b
    have hle : (if b then U else V) ≤ W := by cases b <;> simp [W]
    have heq : W.ι ''ᵁ (W.ι ⁻¹ᵁ (if b then U else V)) = (if b then U else V) := by
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]
    apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ (if b then U else V)))).mpr
    rw [heq]
    cases b <;> dsimp <;> infer_instance

lemma isIso_restrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) [IsIso (f ∣_ (g ⁻¹ᵁ U))] [IsIso (g ∣_ U)] :
    IsIso ((f ≫ g) ∣_ U) := by
  rw [morphismRestrict_comp]
  infer_instance


end AlgebraicGeometry.Scheme.Hom
