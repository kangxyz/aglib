/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Clopen descent along affine inverse limits

FE-05 scratch authoring on project HEAD 1e2b2a1a and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. This supplies the clopen-set
part of limit descent. It does not assert descent of finite étale objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Every clopen subset of a qcqs affine-transition limit descends to a clopen
subset of one stage. No surjectivity of the transition maps is assumed. -/
theorem exists_clopen_preimage_eq (U : c.pt.Opens)
    (hU : IsClosed (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens),
      IsClosed (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U := by
  let : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let Uc : c.pt.Opens := ⟨(U : Set c.pt)ᶜ, hU.isOpen_compl⟩
  have hUc : IsClosed (Uc : Set c.pt) := U.isOpen.isClosed_compl
  obtain ⟨i₁, V₁, hV₁, e₁⟩ := AlgebraicGeometry.exists_preimage_eq D c hc U hU.isCompact
  obtain ⟨i₂, V₂, hV₂, e₂⟩ := AlgebraicGeometry.exists_preimage_eq D c hc Uc hUc.isCompact
  let i := IsCofiltered.min i₁ i₂
  let f₁ : i ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let f₂ : i ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let V : (D.obj i).Opens := D.map f₁ ⁻¹ᵁ V₁
  let W : (D.obj i).Opens := D.map f₂ ⁻¹ᵁ V₂
  have hV : IsCompact (V : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage _ V₁.isOpen hV₁
  have hW : IsCompact (W : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage _ V₂.isOpen hV₂
  have eV : c.π.app i ⁻¹ᵁ V = U := by
    simpa only [V, ← Scheme.Hom.comp_preimage, c.w] using e₁
  have eW : c.π.app i ⁻¹ᵁ W = Uc := by
    simpa only [W, ← Scheme.Hom.comp_preimage, c.w] using e₂
  have he : c.π.app i ⁻¹ᵁ (V ⊔ W) = ⊤ := by
    rw [Scheme.Hom.preimage_sup, eV, eW]
    ext x
    simp [Uc]
  have hd : c.π.app i ⁻¹ᵁ (V ⊓ W) ≤ c.π.app i ⁻¹ᵁ ⊥ := by
    rw [Scheme.Hom.preimage_inf, eV, eW]
    intro x hx
    exact False.elim (hx.2 hx.1)
  obtain ⟨j₁, g₁, ej₁⟩ := AlgebraicGeometry.exists_map_eq_top D c hc (V ⊔ W) he
  obtain ⟨j₂, g₂, ej₂⟩ := AlgebraicGeometry.exists_map_preimage_le_map_preimage D c hc
    (hV.inter_of_isOpen hW V.isOpen W.isOpen) hd
  obtain ⟨k, a, b, hab⟩ := IsCofiltered.cospan g₁ g₂
  let g : k ⟶ i := a ≫ g₁
  have ek : D.map g ⁻¹ᵁ (V ⊔ W) = ⊤ := by
    simp only [g, Functor.map_comp, Scheme.Hom.comp_preimage, ej₁,
      Scheme.Hom.preimage_top]
  have dk : D.map g ⁻¹ᵁ (V ⊓ W) ≤ ⊥ := by
    have H := Scheme.Hom.preimage_mono (D.map b) ej₂
    simpa only [g, hab, Functor.map_comp, Scheme.Hom.comp_preimage,
      Scheme.Hom.preimage_bot] using H
  have hcompl : ((D.map g ⁻¹ᵁ V : (D.obj k).Opens) : Set (D.obj k))ᶜ =
      (D.map g ⁻¹ᵁ W : Set (D.obj k)) := by
    ext x
    constructor
    · intro hx
      have : x ∈ D.map g ⁻¹ᵁ (V ⊔ W) := ek.ge (Set.mem_univ x)
      exact this.resolve_left hx
    · intro hxW hxV
      exact dk ⟨hxV, hxW⟩
  refine ⟨k, D.map g ⁻¹ᵁ V, ?_, ?_⟩
  · rw [← isOpen_compl_iff, hcompl]
    exact (D.map g ⁻¹ᵁ W).isOpen
  · simpa only [← Scheme.Hom.comp_preimage, c.w] using eV

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 755d4dd49c9b43fc0ca7330d7a9dc99cda88256f85801a0abcf4b06dfb7dd334.
Definitions, hypotheses and universes are retained modulo native names. -/
