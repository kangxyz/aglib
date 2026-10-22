/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.Refinement
public import Aglib.AlgebraicGeometry.Blowup.TopologicalDensity

/-!
# Finite simultaneous admissible refinements

A finite induction successively blows up the inverse image of each selected
centre on the current scheme. The previous comparisons are retained by
composition, and the new comparison is supplied by the native blowup universal
property. The composite is not asserted to be a single blowup. Schematic
density is retained using the actual blowup density theorem at every step.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Blowup

private theorem quasiCompact_preimage_inclusion {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [QuasiCompact U.ι] : QuasiCompact (f ⁻¹ᵁ U).ι := by
  rw [← (isPullback_morphismRestrict f U).isoPullback_hom_snd]
  infer_instance

private theorem dense_preimage_of_flat {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Flat f] (U : X.Opens) [QuasiCompact U.ι]
    [IsSchemeTheoreticallyDominant U.ι] :
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ U).ι :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict f U)

/-- A finite family of admissible native blowups has a proper common refinement
unchanged on the protected open. The construction also preserves schematic
density of that open, when it is present, including for nonreduced schemes.
The comparisons have their literal triangles over the original base. -/
private theorem exists_finite_admissible_refinement_aux {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type v} (U : X.Opens) (I : ι → X.IdealSheafData)
    (B : ∀ i, BlowupDatum (I i)) (s : Finset ι)
    (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X),
      AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      (Dense (U : Set X) → Dense ((β ⁻¹ᵁ U) : Set Y)) ∧
      (IsSchemeTheoreticallyDominant U.ι →
        IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι) ∧
      (∀ i ∈ s, ∃ g : Y ⟶ (B i).Y, g ≫ (B i).map = β) ∧
      ∀ {Z : Scheme.{u}} (q : Z ⟶ X) [Flat q]
        [QuasiCompact (q ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U).ι],
        IsSchemeTheoreticallyDominant
          ((pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι := by
  classical
  revert hI
  induction s using Finset.induction_on with
  | empty =>
      intro hI
      refine ⟨X, 𝟙 X, .id, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
      · rw [morphismRestrict_id]
        exact (Iso.refl ((𝟙 X) ⁻¹ᵁ U).toScheme).isIso_hom
      · exact fun h => h
      · exact fun h => h
      · simp
      · intro Z q hq hqc hd
        exact dense_preimage_of_flat (pullback.snd (𝟙 X) q) (q ⁻¹ᵁ U)
  | @insert a s ha ih =>
      intro hI
      obtain ⟨Y, β, hSeq, hβ, hU, hTop, hD, hg, hRel⟩ :=
        ih (fun i hi => hI i (Finset.mem_insert_of_mem hi))
      let : IsProper β := hβ
      let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian β
      let C := blowupDatum ((I a).comap β)
      let : IsProper C.map := C.isProper_of_isLocallyNoetherian
      have hc : cartierPullback (I a) (C.map ≫ β) := by
        have he : (I a).comap (C.map ≫ β) = ((I a).comap β).comap C.map :=
          IdealSheafData.comap_comp (I a) C.map β
        exact (congrArg (fun K : C.Y.IdealSheafData =>
          Modules.Invertible.IsLocallyRankOne C.Y (Scheme.Hom.idealModule K.subschemeι))
          he).mpr C.cartier
      have ht : ((I a).comap β).comap (β ⁻¹ᵁ U).ι = ⊤ := by
        rw [← IdealSheafData.comap_comp, ← morphismRestrict_ι,
          IdealSheafData.comap_comp, hI a (Finset.mem_insert_self a s),
          IdealSheafData.comap_top]
      refine ⟨C.Y, C.map ≫ β, .step hSeq _ C ht, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
      · rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' (C.restrict_isIso_of_comap_eq_top _ ht) hU
      · intro hd
        exact C.preimage_open_dense (β ⁻¹ᵁ U) (hTop hd)
      · intro hd
        let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι := hD hd
        exact C.preimage_open_isSchemeTheoreticallyDominant (β ⁻¹ᵁ U)
      · intro i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          exact ⟨(B a).lift (C.map ≫ β) hc, (B a).lift_map _ hc⟩
        · obtain ⟨g, hgi⟩ := hg i hi
          exact ⟨C.map ≫ g, by rw [Category.assoc, hgi]⟩
      · intro Z q hq hqc hd
        let q' := pullback.fst β q
        let D := flatPullbackDatum C q'
        have he : q' ⁻¹ᵁ (β ⁻¹ᵁ U) = (pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U) := by
          rw [← Hom.comp_preimage, ← Hom.comp_preimage]
          exact congrArg (fun k => k ⁻¹ᵁ U) (pullback.condition (f := β) (g := q))
        let : QuasiCompact (q' ⁻¹ᵁ (β ⁻¹ᵁ U)).ι := by
          rw [he]
          exact quasiCompact_preimage_inclusion (pullback.snd β q) (q ⁻¹ᵁ U)
        let : IsSchemeTheoreticallyDominant (q' ⁻¹ᵁ (β ⁻¹ᵁ U)).ι := by
          rw [he]
          exact hRel q
        let hqcD : QuasiCompact (D.map ⁻¹ᵁ (q' ⁻¹ᵁ (β ⁻¹ᵁ U))).ι :=
          quasiCompact_preimage_inclusion D.map _
        let hsdD : IsSchemeTheoreticallyDominant
            (D.map ⁻¹ᵁ (q' ⁻¹ᵁ (β ⁻¹ᵁ U))).ι :=
          D.preimage_open_isSchemeTheoreticallyDominant _
        let e := pullbackRightPullbackFstIso β q C.map
        have heFlat : Flat e.inv := inferInstance
        have h := @dense_preimage_of_flat D.Y (pullback (C.map ≫ β) q)
          e.inv heFlat (D.map ⁻¹ᵁ (q' ⁻¹ᵁ (β ⁻¹ᵁ U))) hqcD hsdD
        have he' : e.inv ⁻¹ᵁ (D.map ⁻¹ᵁ (q' ⁻¹ᵁ (β ⁻¹ᵁ U))) =
            (pullback.snd (C.map ≫ β) q) ⁻¹ᵁ (q ⁻¹ᵁ U) := by
          rw [he]
          change e.inv ⁻¹ᵁ ((pullback.snd C.map q') ⁻¹ᵁ
            ((pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U))) = _
          rw [← Hom.comp_preimage, ← Hom.comp_preimage, Category.assoc]
          exact congrArg (fun k => k ⁻¹ᵁ (q ⁻¹ᵁ U))
            (pullbackRightPullbackFstIso_inv_snd_snd β q C.map)
        exact he' ▸ h

/-- A finite family of admissible native blowups has a proper common refinement
with literal comparison triangles, unchanged on the protected open. -/
theorem exists_finite_admissible_refinement {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type v} (U : X.Opens) (I : ι → X.IdealSheafData)
    (B : ∀ i, BlowupDatum (I i)) (s : Finset ι)
    (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      (IsSchemeTheoreticallyDominant U.ι →
        IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι) ∧
      ∀ i ∈ s, ∃ g : Y ⟶ (B i).Y, g ≫ (B i).map = β := by
  obtain ⟨Y, β, _, hβ, hU, _, hD, hg, _⟩ :=
    exists_finite_admissible_refinement_aux U I B s hI
  exact ⟨Y, β, hβ, hU, hD, hg⟩

/-- Schematic density on a flat local base is retained through the actual
finite sequence of blowups. No density of the protected open in `X` is assumed. -/
theorem exists_finite_admissible_refinement_of_flat_schematicallyDense
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type v}
    (U : X.Opens) (q : Z ⟶ X) [Flat q]
    [QuasiCompact (q ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U).ι]
    (I : ι → X.IdealSheafData) (B : ∀ i, BlowupDatum (I i))
    (s : Finset ι) (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (g : ∀ i : {i // i ∈ s}, Y ⟶ (B i.val).Y),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant
        ((pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ∧
      ∀ i, g i ≫ (B i.val).map = β := by
  obtain ⟨Y, β, _, hβ, hU, _, _, hg, hRel⟩ :=
    exists_finite_admissible_refinement_aux U I B s hI
  refine ⟨Y, β, fun i => Classical.choose (hg i.val i.property),
    hβ, hU, hRel q, ?_⟩
  intro i
  exact Classical.choose_spec (hg i.val i.property)

/-- The same actual refinement retains both a global topological density
implication and schematic density on the specified flat local base. -/
theorem exists_finite_admissible_refinement_of_flat_schematicallyDense_with_dense
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type v}
    (U : X.Opens) (q : Z ⟶ X) [Flat q]
    [QuasiCompact (q ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U).ι]
    (I : ι → X.IdealSheafData) (B : ∀ i, BlowupDatum (I i))
    (s : Finset ι) (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (g : ∀ i : {i // i ∈ s}, Y ⟶ (B i.val).Y),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      (Dense (U : Set X) → Dense ((β ⁻¹ᵁ U) : Set Y)) ∧
      IsSchemeTheoreticallyDominant
        ((pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ∧
      ∀ i, g i ≫ (B i.val).map = β := by
  obtain ⟨Y, β, _, hβ, hU, hTop, _, hg, hRel⟩ :=
    exists_finite_admissible_refinement_aux U I B s hI
  refine ⟨Y, β, fun i => Classical.choose (hg i.val i.property),
    hβ, hU, hTop, hRel q, ?_⟩
  intro i
  exact Classical.choose_spec (hg i.val i.property)

/-- The same actual refinement additionally retains its native admissible
blowup sequence, for subsequent closed-ambient extension. -/
theorem exists_finite_admissible_refinement_of_flat_schematicallyDense_with_sequence
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type v}
    (U : X.Opens) (q : Z ⟶ X) [Flat q]
    [QuasiCompact (q ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U).ι]
    (I : ι → X.IdealSheafData) (B : ∀ i, BlowupDatum (I i))
    (s : Finset ι) (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (g : ∀ i : {i // i ∈ s}, Y ⟶ (B i.val).Y),
      AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      (Dense (U : Set X) → Dense ((β ⁻¹ᵁ U) : Set Y)) ∧
      IsSchemeTheoreticallyDominant
        ((pullback.snd β q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ∧
      ∀ i, g i ≫ (B i.val).map = β := by
  obtain ⟨Y, β, hSeq, hβ, hU, hTop, _, hg, hRel⟩ :=
    exists_finite_admissible_refinement_aux U I B s hI
  refine ⟨Y, β, fun i => Classical.choose (hg i.val i.property),
    hSeq, hβ, hU, hTop, hRel q, ?_⟩
  intro i
  exact Classical.choose_spec (hg i.val i.property)

/-- The finite simultaneous refinement with an explicit family of comparison
maps and schematic density of the protected open in the resulting source. -/
theorem exists_finite_admissible_refinement_of_schematicallyDense
    {X : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type v}
    (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (I : ι → X.IdealSheafData) (B : ∀ i, BlowupDatum (I i))
    (s : Finset ι) (hI : ∀ i ∈ s, (I i).comap U.ι = ⊤) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (g : ∀ i : {i // i ∈ s}, Y ⟶ (B i.val).Y),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι ∧
      ∀ i, g i ≫ (B i.val).map = β := by
  obtain ⟨Y, β, hβ, hU, hD, hg⟩ := exists_finite_admissible_refinement U I B s hI
  refine ⟨Y, β, fun i => Classical.choose (hg i.val i.property),
    hβ, hU, hD inferInstance, ?_⟩
  intro i
  exact Classical.choose_spec (hg i.val i.property)

end AlgebraicGeometry.Scheme.Blowup
