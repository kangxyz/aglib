/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Clopen subsets in affine-transition limits

Clopen subsets of a qcqs inverse limit with affine transition maps descend
to a stage. A specified quasi-compact stage open whose limit pullback is
closed is already closed after a later transition.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Every clopen subset of a qcqs affine-transition limit descends to a clopen
subset of one stage. No surjectivity of the transition maps is assumed. -/
theorem exists_clopen_preimage_eq_of_isLimit (U : c.pt.Opens)
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

include hc in
/-- A specified quasi-compact open whose pullback to the limit is closed
becomes closed after one transition. -/
theorem exists_isClosed_preimage_of_isLimit {i : I} (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i)))
    (hclosed : IsClosed ((c.π.app i ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)) :
    ∃ (j : I) (f : j ⟶ i), IsClosed ((D.map f ⁻¹ᵁ U : (D.obj j).Opens) : Set (D.obj j)) := by
  obtain ⟨k, V, hV, eV⟩ := exists_clopen_preimage_eq_of_isLimit D c hc
    (c.π.app i ⁻¹ᵁ U) hclosed
  let l := IsCofiltered.min i k
  let a : l ⟶ i := IsCofiltered.minToLeft i k
  let b : l ⟶ k := IsCofiltered.minToRight i k
  have hUa : IsCompact ((D.map a ⁻¹ᵁ U : (D.obj l).Opens) : Set (D.obj l)) :=
    QuasiCompact.isCompact_preimage _ U.isOpen hU
  have hVb : IsCompact ((D.map b ⁻¹ᵁ V : (D.obj l).Opens) : Set (D.obj l)) :=
    QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
  have e : c.π.app l ⁻¹ᵁ D.map a ⁻¹ᵁ U = c.π.app l ⁻¹ᵁ D.map b ⁻¹ᵁ V := by
    simpa only [← Scheme.Hom.comp_preimage, c.w] using eV.symm
  obtain ⟨j, q, hq⟩ := AlgebraicGeometry.exists_map_preimage_eq_map_preimage
    D c hc hUa hVb e
  refine ⟨j, q ≫ a, ?_⟩
  have H : IsClosed ((D.map q ⁻¹ᵁ D.map b ⁻¹ᵁ V : (D.obj j).Opens) : Set (D.obj j)) :=
    (hV.preimage (D.map b).continuous).preimage (D.map q).continuous
  simpa only [Functor.map_comp, Scheme.Hom.comp_preimage, hq] using H

end AlgebraicGeometry.Scheme
