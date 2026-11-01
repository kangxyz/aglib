/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponent
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.OpenGaloisReflection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange
public import Aglib.CategoryTheory.Galois.Iso

/-! # The original Galois cover on an etale open of its normalization

Only open restrictions of the original cover and normalization occur. The
restricted original recovery square supplies their comparison; no new
normalization or deck action is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j] (Y : FiniteEtale U) [IsIntegral Y.obj.left]
  (Z : X.Opens) [Nonempty Z]

/-- The actual original normalization map. -/
abbrev restrictedNormalizationMap : (genericMap j Y.obj.hom).normalization ⟶ X :=
  (genericMap j Y.obj.hom).fromNormalization

/-- The original base open, restricted to the original covering target. -/
abbrev restrictedNormalizationBaseOpen : U.Opens := j ⁻¹ᵁ Z

/-- The literal source open in the original finite-etale covering scheme. -/
abbrev restrictedNormalizationSourceOpen : Y.obj.left.Opens :=
  Y.obj.hom ⁻¹ᵁ (j ⁻¹ᵁ Z)

/-- The literal source open in the original normalization. -/
abbrev restrictedNormalizationTargetOpen : (genericMap j Y.obj.hom).normalization.Opens :=
  (genericMap j Y.obj.hom).fromNormalization ⁻¹ᵁ Z

local notation "f" => restrictedNormalizationMap j Y
local notation "i" => inclusion j Y.obj.hom
local notation "W" => restrictedNormalizationBaseOpen j Z
local notation "EZ" => restrictedNormalizationSourceOpen j Y Z
local notation "NZ" => restrictedNormalizationTargetOpen j Y Z

omit [IsLocallyNoetherian X] [IsIntegral Y.obj.left] [Nonempty Z] in
/-- The original inclusion has exactly the original restricted covering source. -/
theorem restrictedNormalization_preimage : i ⁻¹ᵁ NZ = EZ := by
  rw [← Scheme.Hom.comp_preimage, inclusion_over, Scheme.Hom.comp_preimage]

omit [IsLocallyNoetherian X] [IsIntegral Y.obj.left] [Nonempty Z] in
/-- Restrict the original open-recovery square, with its literal four maps. -/
theorem restrictedNormalization_isPullback :
    IsPullback ((i).resLE NZ EZ (le_of_eq (restrictedNormalization_preimage j Y Z).symm))
      (Y.obj.hom ∣_ W) (f ∣_ Z) (j ∣_ Z) := by
  have h := Scheme.Hom.isPullback_resLE (isPullback j Y.obj.hom)
    (UT := W) (US := Z) (UX := NZ) le_rfl le_rfl
    (UY := EZ) (by rw [restrictedNormalization_preimage, inf_idem])
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h

local instance restrictedNormalization_finite : IsFinite f :=
  fromNormalization_isFinite j Y.obj.hom

variable [Etale (restrictedNormalizationMap j Y ∣_ Z)]

/-- The literal finite-etale restriction of the original normalization. -/
abbrev restrictedNormalizationCover : FiniteEtale Z := FiniteEtale.mk (f ∣_ Z)

/-- The original cover restriction maps to the literal normalization restriction. -/
def restrictedNormalization_restrictionIso :
    FiniteEtale.mk (Y.obj.hom ∣_ W) ≅
      (baseChange (j ∣_ Z)).obj (restrictedNormalizationCover j Y Z) :=
  ObjectProperty.isoMk _ (Over.isoMk
    (restrictedNormalization_isPullback j Y Z).isoPullback
    (restrictedNormalization_isPullback j Y Z).isoPullback_hom_snd)

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
private theorem restrictedNormalization_open_nonempty : Nonempty W := by
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  refine ⟨⟨genericPoint U, ?_⟩⟩
  change j (genericPoint U) ∈ Z
  rw [map_genericPoint_of_isDominant]
  exact ((genericPoint_spec X).mem_open_set_iff Z.isOpen).mpr (by simpa using ‹Nonempty Z›)

local instance : Nonempty W := restrictedNormalization_open_nonempty j Z
local instance : IsIntegral W := isIntegral_of_isOpenImmersion (W).ι
local instance : IsIntegral Z := isIntegral_of_isOpenImmersion Z.ι

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [Etale (restrictedNormalizationMap j Y ∣_ Z)] in
private theorem restrictedNormalization_cover_nonempty : Nonempty EZ := by
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  refine ⟨⟨genericPoint Y.obj.left, ?_⟩⟩
  change Y.obj.hom (genericPoint Y.obj.left) ∈ W
  rw [map_genericPoint_of_isDominant]
  exact ((genericPoint_spec U).mem_open_set_iff (W).isOpen).mpr
    (by simpa using (inferInstance : Nonempty W))

local instance : Nonempty EZ := restrictedNormalization_cover_nonempty j Y Z
local instance : IsIntegral EZ := isIntegral_of_isOpenImmersion (EZ).ι

local instance restrictedNormalization_integral :
    IsIntegral (genericMap j Y.obj.hom).normalization := by
  let : IsIntegral (genericCover j Y.obj.hom).obj.left :=
    IsIntegral.of_isIso (originalFieldSpectrumIso j Y).hom
  infer_instance

local instance : Nonempty NZ := by
  obtain ⟨y⟩ := (inferInstance : Nonempty EZ)
  exact ⟨((i).resLE NZ EZ (le_of_eq (restrictedNormalization_preimage j Y Z).symm)) y⟩

local instance : IsIntegral NZ := isIntegral_of_isOpenImmersion (NZ).ι

local instance : ∀ z : (Z : Scheme.{u}), IsIntegrallyClosed ((Z : Scheme.{u}).presheaf.stalk z) :=
  fun z => IsIntegrallyClosed.of_equiv (asIso (Z.ι.stalkMap z)).commRingCatIsoToRingEquiv

private def originalCoverRestrictionIso :
    FiniteEtale.mk (Y.obj.hom ∣_ W) ≅ (baseChange (W).ι).obj Y :=
  ObjectProperty.isoMk _ (Over.isoMk
    (isPullback_morphismRestrict Y.obj.hom W).flip.isoPullback
    (isPullback_morphismRestrict Y.obj.hom W).flip.isoPullback_hom_snd)

/-- The unchanged normalization on any nonempty etale open is Galois and has
exactly the original deck-group order. -/
theorem restrictedNormalization_isGalois_card [IsGalois Y] :
    IsGalois (restrictedNormalizationCover j Y Z) ∧
      Nat.card (Aut (restrictedNormalizationCover j Y Z)) = Nat.card (Aut Y) := by
  let E := FiniteEtale.mk (Y.obj.hom ∣_ W)
  let G := restrictedNormalizationCover j Y Z
  let : IsIntegral E.obj.left := inferInstanceAs (IsIntegral EZ)
  let : IsIntegral G.obj.left := inferInstanceAs (IsIntegral NZ)
  let eY : E ≅ (baseChange (W).ι).obj Y := originalCoverRestrictionIso j Y Z
  let eG : E ≅ (baseChange (j ∣_ Z)).obj G := restrictedNormalization_restrictionIso j Y Z
  let : IsIntegral ((forgetToScheme W).obj E) := by
    rw [forgetToScheme_obj]
    infer_instance
  let : IsIntegral ((baseChange (W).ι).obj Y).obj.left :=
    IsIntegral.of_isIso ((forgetToScheme W).map eY.hom)
  let : IsGalois ((baseChange (W).ι).obj Y) := baseChange_isGalois_of_connected (W).ι Y
  let x := algebraicClosureResiduePoint W (Classical.choice (inferInstance : Nonempty W))
  let : IsGalois ((baseChange (j ∣_ Z)).obj G) :=
    isGalois_of_iso (fiberToFinite x) (eY.symm ≪≫ eG)
  let : IsGalois G := isGalois_of_open_baseChange (j ∣_ Z) G
  refine ⟨inferInstance, ?_⟩
  calc
    Nat.card (Aut G) = Nat.card (Aut ((baseChange (j ∣_ Z)).obj G)) :=
      (card_aut_open_baseChange (j ∣_ Z) G).symm
    _ = Nat.card (Aut ((baseChange (W).ι).obj Y)) :=
      Nat.card_congr (Aut.autMulEquivOfIso (eG.symm ≪≫ eY)).toEquiv
    _ = Nat.card (Aut Y) := baseChange_card_aut_of_connected (W).ι Y

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
