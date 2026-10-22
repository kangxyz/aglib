/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.IdealChoice
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Boundary closure control

The Noetherian closure-control step of Conrad's Lemma 3.1, with the original
map and actual fibre product. The centre is supported on the specified closed
boundary outside the protected open. No strict-transform identification is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Boundary closure control for every subset of the original protected open.
The same canonical blowup works for all such subsets. -/
theorem exists_boundary_closure_control {X₁ X₂ : Scheme.{u}}
    [IsNoetherian X₁] [IsNoetherian X₂]
    (q : X₂ ⟶ X₁) (V : X₁.Opens) (Z₁ : Closeds X₁) (Z₂ : Closeds X₂)
    (hq : q ⁻¹' ((Z₁ : Set X₁) ∩ (V : Set X₁)) ⊆ Z₂) :
    ∃ I : X₁.IdealSheafData,
      ((I.support : Set X₁) ⊆ (Z₁ : Set X₁) \ (V : Set X₁)) ∧
      I.comap V.ι = ⊤ ∧
      let B := blowupDatum I
      IsProper B.map ∧ IsIso (B.map ∣_ V) ∧
      ∀ D : Set X₂, D ⊆ q ⁻¹' (V : Set X₁) →
        (pullback.snd q B.map ⁻¹'
          closure (B.map ⁻¹' ((Z₁ : Set X₁) ∩ (V : Set X₁)))) ∩
          closure (pullback.fst q B.map ⁻¹' D) ⊆
            pullback.fst q B.map ⁻¹' (Z₂ : Set X₂) := by
  let A : X₁.Opens := ⟨(Z₁ : Set X₁)ᶜ, Z₁.isClosed.isOpen_compl⟩
  let W := A ⊔ V
  let Z : X₂.Opens := ⟨(Z₂ : Set X₂)ᶜ, Z₂.isClosed.isOpen_compl⟩
  let : CompactSpace Z.toScheme := by
    change CompactSpace (Z : Set X₂)
    infer_instance
  let : IsNoetherian Z.toScheme := ⟨⟩
  let p : Z.toScheme ⟶ X₁ := Z.ι ≫ q
  let f := (p ⁻¹ᵁ A).ι
  have hA : ∀ z : Z.toScheme, p z ∈ W → p z ∈ A := by
    intro z hz
    rcases hz with hz | hz
    · exact hz
    · change q (Z.ι z) ∉ Z₁
      intro hz₁
      exact z.property (hq ⟨hz₁, hz⟩)
  have hfA : Set.range (f ≫ p) ⊆ A := by
    rintro _ ⟨z, rfl⟩
    exact z.property
  have hclosed : IsClosed ((p ⁻¹ᵁ W).ι ⁻¹' Set.range f) := by
    have he : (p ⁻¹ᵁ W).ι ⁻¹' Set.range f = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      exact ⟨⟨z.val, hA z.val z.property⟩, rfl⟩
    rw [he]
    exact isClosed_univ
  obtain ⟨I₁, I₂, _, hI₁, hI₂, _, hproper, _, hsep⟩ :=
    exists_canonical_boundary_separation p f A W le_sup_left hfA hclosed
  let I := I₁ ⊔ I₂
  let B := blowupDatum I
  have hsupp : (I.support : Set X₁) ⊆ (Z₁ : Set X₁) \ (V : Set X₁) := by
    intro x hx
    rw [IdealSheafData.support_sup] at hx
    refine ⟨?_, fun hxV => (hI₂ hx.2).2 (Or.inr hxV)⟩
    have hxA := hI₁ hx.1
    change ¬¬x ∈ Z₁ at hxA
    exact not_not.mp hxA
  have hunit : I.comap V.ι = ⊤ := by
    apply BlowupDatum.comap_eq_top_of_disjoint
    exact Set.disjoint_left.mpr (fun x hxV hxI => (hsupp hxI).2 hxV)
  refine ⟨I, hsupp, hunit, hproper, B.restrict_isIso_of_comap_eq_top V hunit, ?_⟩
  intro D hD y hy
  by_contra hyZ
  let e : pullback p B.map ⟶ pullback q B.map :=
    pullback.map _ _ _ _ Z.ι (𝟙 B.Y) (𝟙 X₁) (by simp [p]) (by simp)
  let : IsOpenImmersion e := by dsimp [e]; infer_instance
  have he₁ : e ≫ pullback.fst q B.map = pullback.fst p B.map ≫ Z.ι :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd q B.map = pullback.snd p B.map := by
    dsimp only [e, pullback.map]
    rw [pullback.lift_snd, Category.comp_id]
  have hyrange : y ∈ Set.range e := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨⟨pullback.fst q B.map y, hyZ⟩, rfl⟩,
      ⟨pullback.snd q B.map y, rfl⟩⟩
  obtain ⟨y₀, rfl⟩ := hyrange
  have hboundary : (W : Set X₁) \ (A : Set X₁) =
      (Z₁ : Set X₁) ∩ (V : Set X₁) := by
    ext x
    change ((x ∉ Z₁ ∨ x ∈ V) ∧ ¬x ∉ Z₁) ↔ (x ∈ Z₁ ∧ x ∈ V)
    tauto
  have hyboundary : y₀ ∈ pullback.snd p B.map ⁻¹'
      closure (B.map ⁻¹' ((W : Set X₁) \ (A : Set X₁))) := by
    rw [hboundary]
    have heval := congrArg (fun g : pullback p B.map ⟶ B.Y => g y₀) he₂
    change pullback.snd q B.map (e y₀) = pullback.snd p B.map y₀ at heval
    have hh : pullback.snd q B.map (e y₀) ∈
        closure (B.map ⁻¹' ((Z₁ : Set X₁) ∩ (V : Set X₁))) := hy.1
    rwa [heval] at hh
  have hsub : e ⁻¹' (pullback.fst q B.map ⁻¹' D) ⊆
      Set.range (pullback.snd f (pullback.fst p B.map)) := by
    intro z hz
    rw [Scheme.Pullback.range_snd]
    have heval := congrArg (fun g : pullback p B.map ⟶ X₂ => g z) he₁
    change pullback.fst q B.map (e z) = Z.ι (pullback.fst p B.map z) at heval
    have hzV : p (pullback.fst p B.map z) ∈ V := by
      change q (Z.ι (pullback.fst p B.map z)) ∈ (V : Set X₁)
      have hh : q (pullback.fst q B.map (e z)) ∈ (V : Set X₁) := hD hz
      rwa [heval] at hh
    exact ⟨⟨pullback.fst p B.map z, hA _ (Or.inr hzV)⟩, rfl⟩
  have hyclosure : y₀ ∈ closure
      (Set.range (pullback.snd f (pullback.fst p B.map))) := by
    apply closure_mono hsub
    have hh : y₀ ∈ e ⁻¹' closure (pullback.fst q B.map ⁻¹' D) := hy.2
    rwa [e.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage e.continuous] at hh
  exact Set.disjoint_left.mp hsep hyclosure hyboundary

end AlgebraicGeometry.Scheme.Blowup
