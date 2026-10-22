/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.BaseChange.ClosedComparison

/-!
# Common refinements of actual admissible sequences

Domination along an arbitrary map uses successive native blowups of pulled-back
centres. The comparison is not asserted to be a nonflat pullback isomorphism.
Finite induction then dominates a finite family of actual sequences.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

set_option backward.isDefEq.respectTransparency false in
private theorem exists_domination_aux {X T Y : Scheme.{u}} {U : X.Opens} {β : T ⟶ X}
    (hβ : AdmissibleSequence U β) (f : Y ⟶ X) :
    ∃ (Y' : Scheme.{u}) (γ : Y' ⟶ Y) (a : Y' ⟶ T) (he : a ≫ β = γ ≫ f),
      AdmissibleSequence (f ⁻¹ᵁ U) γ ∧
      (LocallyOfFiniteType f → IsClosedImmersion (pullback.lift γ a he.symm)) := by
  induction hβ with
  | id =>
      refine ⟨Y, 𝟙 Y, f, by simp, .id, ?_⟩
      intro hf
      let z : Y ⟶ pullback f (𝟙 X) := pullback.lift (𝟙 Y) f (by simp)
      let : IsIso (z ≫ pullback.fst f (𝟙 X)) := by
        rw [pullback.lift_fst]
        infer_instance
      let : IsIso z := IsIso.of_isIso_comp_right z (pullback.fst f (𝟙 X))
      exact inferInstanceAs (IsClosedImmersion z)
  | @step T δ hδ J B hJ ih =>
      obtain ⟨Y', γ, a, he, hγ, hz⟩ := ih
      let D := blowupDatum (J.comap a)
      have hp : γ ⁻¹ᵁ (f ⁻¹ᵁ U) = a ⁻¹ᵁ (δ ⁻¹ᵁ U) := by
        rw [← Hom.comp_preimage, ← he, Hom.comp_preimage]
      have ht : (J.comap a).comap (γ ⁻¹ᵁ (f ⁻¹ᵁ U)).ι = ⊤ := by
        rw [hp, ← IdealSheafData.comap_comp, ← morphismRestrict_ι,
          IdealSheafData.comap_comp, hJ, IdealSheafData.comap_top]
      let k := BaseChange.map a rfl B D
      have hk : k ≫ (B.map ≫ δ) = (D.map ≫ γ) ≫ f := by
        rw [← Category.assoc, BaseChange.map_triangle, Category.assoc, he, Category.assoc]
      refine ⟨D.Y, D.map ≫ γ, k, hk, .step hγ _ D ht, ?_⟩
      intro hf
      let : LocallyOfFiniteType f := hf
      let z := pullback.lift γ a he.symm
      let : IsClosedImmersion z := hz hf
      have hza : z ≫ pullback.snd f δ = a := pullback.lift_snd _ _ _
      let : LocallyOfFiniteType a := by rw [← hza]; infer_instance
      let b := pullback.lift D.map k (BaseChange.map_triangle a rfl B D).symm
      let : IsClosedImmersion b := BaseChange.toPullback_isClosedImmersion a rfl B D
      let m := pullback.map a B.map (pullback.snd f δ) B.map z (𝟙 B.Y) (𝟙 T)
        (by simpa using hza.symm) (by simp)
      let : IsClosedImmersion m := MorphismProperty.pullbackMap
        (P := @IsClosedImmersion.{u}) (inferInstance : IsClosedImmersion z)
        (inferInstance : IsClosedImmersion (𝟙 B.Y)) hza.symm (by simp)
      let e := pullbackLeftPullbackSndIso f δ B.map
      have hz' : pullback.lift (D.map ≫ γ) k hk.symm = b ≫ m ≫ e.hom := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, e,
            pullbackLeftPullbackSndIso_hom_fst]
          dsimp only [m, b, z]
          simp only [pullback.map, Category.assoc, pullback.lift_fst,
            pullback.lift_fst_assoc]
        · simp only [Category.assoc, pullback.lift_snd, e,
            pullbackLeftPullbackSndIso_hom_snd]
          dsimp only [m, b]
          simp only [pullback.map, pullback.lift_snd,
            Category.comp_id]
      rw [hz']
      infer_instance
  | @iso T T' δ hδ e ih =>
      obtain ⟨Y', γ, a, he, hγ, hz⟩ := ih
      have he' : (a ≫ e.inv) ≫ (e.hom ≫ δ) = γ ≫ f := by
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he
      refine ⟨Y', γ, a ≫ e.inv, he', hγ, ?_⟩
      intro hf
      let z := pullback.lift γ a he.symm
      let : IsClosedImmersion z := hz hf
      let m := pullback.map f δ f (e.hom ≫ δ) (𝟙 Y) e.inv (𝟙 X)
        (by simp) (by simp)
      let : IsClosedImmersion m := MorphismProperty.pullbackMap
        (P := @IsClosedImmersion.{u}) (inferInstance : IsClosedImmersion (𝟙 Y))
        (inferInstance : IsClosedImmersion e.inv) (by simp) (by simp)
      have hm : pullback.lift γ (a ≫ e.inv) he'.symm = z ≫ m := by
        apply pullback.hom_ext <;>
          simp only [m, z, pullback.map, Category.assoc, pullback.lift_fst,
            pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [hm]
      infer_instance

/-- An actual sequence can be dominated after any base map by another actual
sequence, with an exact comparison triangle. -/
theorem exists_domination {X T Y : Scheme.{u}} {U : X.Opens} {β : T ⟶ X}
    (hβ : AdmissibleSequence U β) (f : Y ⟶ X) :
    ∃ (Y' : Scheme.{u}) (γ : Y' ⟶ Y) (a : Y' ⟶ T),
      AdmissibleSequence (f ⁻¹ᵁ U) γ ∧ a ≫ β = γ ≫ f := by
  obtain ⟨Y', γ, a, he, hγ, _⟩ := exists_domination_aux hβ f
  exact ⟨Y', γ, a, hγ, he⟩

/-- Replay along a locally finite-type map retains a closed comparison into
the actual fibre product. This is not a nonflat base-change isomorphism. -/
theorem exists_closed_domination {X T Y : Scheme.{u}} {U : X.Opens} {β : T ⟶ X}
    (hβ : AdmissibleSequence U β) (f : Y ⟶ X) [LocallyOfFiniteType f] :
    ∃ (Y' : Scheme.{u}) (γ : Y' ⟶ Y) (a : Y' ⟶ T) (he : a ≫ β = γ ≫ f),
      AdmissibleSequence (f ⁻¹ᵁ U) γ ∧
      IsClosedImmersion (pullback.lift a γ he) := by
  obtain ⟨Y', γ, a, he, hγ, hz⟩ := exists_domination_aux hβ f
  let : IsClosedImmersion (pullback.lift γ a he.symm) := hz inferInstance
  refine ⟨Y', γ, a, he, hγ, ?_⟩
  have h : pullback.lift a γ he =
      pullback.lift γ a he.symm ≫ (pullbackSymmetry f β).hom := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]
  rw [h]
  infer_instance

/-- A finite family of actual admissible sequences has a common actual
admissible sequence, retaining all literal comparison triangles. -/
theorem exists_finite_refinement {X : Scheme.{u}} {ι : Type v}
    (U : X.Opens) (T : ι → Scheme.{u}) (β : ∀ i, T i ⟶ X)
    (hβ : ∀ i, AdmissibleSequence U (β i)) (s : Finset ι) :
    ∃ (Y : Scheme.{u}) (γ : Y ⟶ X)
      (a : ∀ i : {i // i ∈ s}, Y ⟶ T i.val),
      AdmissibleSequence U γ ∧ ∀ i, a i ≫ β i.val = γ := by
  classical
  suffices h : ∃ (Y : Scheme.{u}) (γ : Y ⟶ X), AdmissibleSequence U γ ∧
      ∀ i ∈ s, ∃ a : Y ⟶ T i, a ≫ β i = γ by
    obtain ⟨Y, γ, hγ, ha⟩ := h
    exact ⟨Y, γ, fun i => Classical.choose (ha i.val i.property), hγ,
      fun i => Classical.choose_spec (ha i.val i.property)⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨X, 𝟙 X, .id, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨Y, γ, hγ, ha⟩ := ih
      obtain ⟨Y', δ, a, hδ, he⟩ := (hβ i).exists_domination γ
      refine ⟨Y', δ ≫ γ, hγ.comp hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        exact ⟨a, he⟩
      · obtain ⟨b, hb⟩ := ha j hj
        exact ⟨δ ≫ b, by rw [Category.assoc, hb]⟩

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
