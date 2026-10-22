/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.BoundaryPatch
public import Aglib.AlgebraicGeometry.Gluing.SchematicDensity.Pushout
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant.OpenFactor
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite-type boundary patches containing the original source -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- The actual boundary pushout is a separated finite-type scheme over the
base and contains the original source as a schematically dense open. The
schematic-density hypothesis concerns the protected chart in the ambient
model, not the intersection of a family of charts. -/
theorem exists_finiteType_boundary_patch
    {T X Y S : Scheme.{u}} [IsNoetherian S]
    (β : T ⟶ X) [IsProper β] (i : T ⟶ Y) [IsOpenImmersion i]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) [IsProper pY]
    (h : i ≫ pY = β ≫ pX) (U : X.Opens) (O : Y.Opens)
    [IsIso (β ∣_ U)] (hpre : i ⁻¹ᵁ O = β ⁻¹ᵁ U)
    [IsSchemeTheoreticallyDominant (inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ i)] :
    ∃ (M : Scheme.{u}) (pM : M ⟶ S) (x : X ⟶ M) (o : O.toScheme ⟶ M)
      (r : U.toScheme ⟶ O.toScheme),
      IsNoetherian M ∧ IsSeparated pM ∧ QuasiCompact pM ∧ LocallyOfFiniteType pM ∧
      IsOpenImmersion x ∧ IsSchemeTheoreticallyDominant x ∧ IsOpenImmersion o ∧
      IsOpenImmersion r ∧ IsSchemeTheoreticallyDominant r ∧
      x ≫ pM = pX ∧ o ≫ pM = O.ι ≫ pY ∧ U.ι ≫ x = r ≫ o ∧
      r ≫ O.ι = inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ i := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  let : IsNoetherian Y := ⟨⟩
  let : NoetherianSpace O.toScheme := by
    change NoetherianSpace (O : Set Y)
    infer_instance
  obtain ⟨r, hr, ho, hri, _, hsep⟩ :=
    SeparatedGluing.exists_boundary_patch β i pX pY h U O hpre
  let : IsOpenImmersion r := ho
  let : IsSchemeTheoreticallyDominant (r ≫ O.ι) := by rw [hri]; infer_instance
  let : IsSchemeTheoreticallyDominant r :=
    IsSchemeTheoreticallyDominant.of_comp_left_of_isOpenImmersion r O.ι
  let M := pushout U.ι r
  let pM : M ⟶ S := pushout.desc pX (O.ι ≫ pY) hr
  let : IsSeparated pM := hsep
  let : LocallyOfFiniteType pM := by
    let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
      (OpenNormalizationGluing.twoChartCover U.ι r)).mpr
    intro b
    cases b
    · change LocallyOfFiniteType (pushout.inl U.ι r ≫ pM)
      dsimp only [pM]
      rw [pushout.inl_desc]
      infer_instance
    · change LocallyOfFiniteType (pushout.inr U.ι r ≫ pM)
      dsimp only [pM]
      rw [pushout.inr_desc]
      infer_instance
  let : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian pM
  let : CompactSpace M := openPushout_compactSpace U.ι r
  let : IsNoetherian M := ⟨⟩
  let : IsSchemeTheoreticallyDominant (pushout.inl U.ι r) :=
    pushout_inl_isSchemeTheoreticallyDominant U.ι r
  exact ⟨M, pM, pushout.inl U.ι r, pushout.inr U.ι r, r,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ho, inferInstance,
    pushout.inl_desc _ _ _, pushout.inr_desc _ _ _, pushout.condition, hri⟩

end AlgebraicGeometry.Scheme.Compactification
