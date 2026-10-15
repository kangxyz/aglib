/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
/-!
# Section comparisons for open-immersion pushforwards

The sections of an open-immersion pushforward on an open depend only on its
intersection with the image. Restricting the pushforward back to its domain
also preserves quasicoherence.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections

/-- A pushforward restriction is an isomorphism of modules over the affine
coordinate ring whenever the two inverse-image opens coincide. -/
lemma isIso_pushforward_modulesSpecToSheaf_map_of_preimage_eq
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R)
    (F : X.Modules) {W₁ W₂ : (Spec R).Opens} (i : W₁ ⟶ W₂)
    (heq : j ⁻¹ᵁ W₁ = j ⁻¹ᵁ W₂) :
    IsIso ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)).obj.map
      i.op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  apply (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pushforward j).obj F).presheaf.map i.op)).mp
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have hi : IsIso ((Opens.map j.base).map i) :=
    homOfLE_isIso_of_eq _ heq
  infer_instance

/-- An open-immersion pushforward has the same sections on an open and on
its intersection with the image. -/
lemma isIso_pushforward_presheaf_map_inf_opensRange
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : X.Modules) (W : Y.Opens) :
    IsIso (((Scheme.Modules.pushforward j).obj F).presheaf.map
      (homOfLE (inf_le_left : W ⊓ j.opensRange ≤ W)).op) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have heq : j ⁻¹ᵁ (W ⊓ j.opensRange) = j ⁻¹ᵁ W := by
    simp [Scheme.Hom.preimage_inf]
  have hi : IsIso ((Opens.map j.base).map
      (homOfLE (inf_le_left : W ⊓ j.opensRange ≤ W))) :=
    homOfLE_isIso_of_eq _ heq
  infer_instance

/-- The section comparison for an open-immersion pushforward over an affine
scheme is an isomorphism of modules over its coordinate ring. -/
lemma isIso_pushforward_modulesSpecToSheaf_map_inf_opensRange
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R) [IsOpenImmersion j]
    (F : X.Modules) (W : (Spec R).Opens) :
    IsIso ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)).obj.map
      (homOfLE (inf_le_left : W ⊓ j.opensRange ≤ W)).op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pushforward j).obj F).presheaf.map
      (homOfLE (inf_le_left : W ⊓ j.opensRange ≤ W)).op)).mp
    (isIso_pushforward_presheaf_map_inf_opensRange j F W)

/-- Specialization of the section comparison to the inclusion of an open
subscheme of an affine scheme. -/
lemma isIso_pushforward_modulesSpecToSheaf_map_inf
    {R : CommRingCat.{u}} (V : (Spec R).Opens) (F : V.toScheme.Modules)
    (W : (Spec R).Opens) :
    IsIso ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward V.ι).obj F)).obj.map
      (homOfLE (inf_le_left : W ⊓ V ≤ W)).op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  apply (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pushforward V.ι).obj F).presheaf.map
      (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)).mp
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have heq : V.ι ⁻¹ᵁ (W ⊓ V) = V.ι ⁻¹ᵁ W := by
    have hV : V.ι ⁻¹ᵁ V = ⊤ := by
      simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange V.ι
    rw [Scheme.Hom.preimage_inf, hV, inf_top_eq]
  have hi : IsIso ((Opens.map V.ι.base).map
      (homOfLE (inf_le_left : W ⊓ V ≤ W))) :=
    homOfLE_isIso_of_eq _ heq
  infer_instance

/-- Restricting an open-immersion pushforward back to its domain recovers a
quasicoherent module when the original module is quasicoherent. -/
lemma isQuasicoherent_restrict_pushforward
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : X.Modules) [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward j).obj F).restrict j).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso j).app F).symm
    (by change F.IsQuasicoherent; infer_instance)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
