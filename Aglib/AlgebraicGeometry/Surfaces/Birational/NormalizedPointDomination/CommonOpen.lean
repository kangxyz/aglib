/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# An actual common open for two proper birational models

The common open is constructed from the original restriction isomorphisms
near the generic point of the normal target. Its actual comparison map is
the first restriction followed by the inverse second restriction and the
second source-open inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

private theorem isIso_restrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V W : Y.Opens) [IsIso (f ∣_ V)] (hWV : W ≤ V) :
    IsIso (f ∣_ W) := by
  let W' := V.ι ⁻¹ᵁ W
  have himage : V.ι ''ᵁ W' = W := by
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr hWV]
  have hdouble : IsIso (f ∣_ V ∣_ W') := inferInstance
  have hsingle : IsIso (f ∣_ V.ι ''ᵁ W') :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f V W')).mp hdouble
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictEq f himage)).mp hsingle

/-- Two actual proper birational models of a normal Noetherian integral target
have a nonempty quasi-compact common open and its original comparison map.
No source regularity or source normality is assumed. -/
theorem exists_commonOpen
    {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S] [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (g : Y ⟶ S) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g))) (hS : NormalStalks S) :
    ∃ (U : X.Opens) (h : U.toScheme ⟶ Y),
      Nonempty U ∧ QuasiCompact U.ι ∧ IsOpenImmersion h ∧ U.ι ≫ f = h ≫ g := by
  have hzero : Order.coheight (genericPoint S) = 0 :=
    Order.coheight_eq_zero.mpr (fun z _ ↦ genericPoint_specializes z)
  have hcodim : Order.coheight (genericPoint S) ≤ 1 := by
    rw [hzero]
    exact zero_le_one
  obtain ⟨V, hηV, hV⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hf hS (genericPoint S) hcodim
  obtain ⟨W, hηW, hW⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_coheight_le_one g hg hS (genericPoint S) hcodim
  let : IsIso (f ∣_ V) := hV
  let : IsIso (g ∣_ W) := hW
  let Z := V ⊓ W
  let : IsIso (f ∣_ Z) := isIso_restrict_of_le f V Z inf_le_left
  let : IsIso (g ∣_ Z) := isIso_restrict_of_le g W Z inf_le_right
  let U := f ⁻¹ᵁ Z
  let h : U.toScheme ⟶ Y := (f ∣_ Z) ≫ inv (g ∣_ Z) ≫ (g ⁻¹ᵁ Z).ι
  have hηU : genericPoint X ∈ U := by
    change f (genericPoint X) ∈ Z
    rw [map_genericPoint_of_isDominant X f]
    exact ⟨hηV, hηW⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  refine ⟨U, h, ⟨⟨genericPoint X, hηU⟩⟩, inferInstance, inferInstance, ?_⟩
  simp only [h, Category.assoc]
  rw [← morphismRestrict_ι g Z, IsIso.inv_hom_id_assoc]
  exact (morphismRestrict_ι f Z).symm

end AlgebraicGeometry.Scheme.NormalizedPointDomination
