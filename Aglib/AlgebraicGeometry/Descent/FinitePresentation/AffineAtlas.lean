/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Sections

/-!
# Descending an original affine atlas together with prescribed sections

The original finite atlas index is retained. The source opens are the literal
inverse images of affine stage opens, and the section comparisons are actual
`appLE` equations in the original source section rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Descend a specified finite affine atlas and finite section families without
changing the atlas index or replacing its section rings by unidentified carriers. -/
lemma exists_affine_atlas_with_sections_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {J : Type v} [Finite J] (U : J → c.pt.Opens)
    (hcover : IsOpenCover U) (hU : ∀ a, IsAffineOpen (U a))
    {K : J → Type w} [∀ a, Finite (K a)] (s : ∀ a, K a → Γ(c.pt, U a)) :
    ∃ (i : I) (V : J → (D.obj i).Opens),
      IsOpenCover V ∧ (∀ a, IsAffineOpen (V a)) ∧
      ∃ (e : ∀ a, U a = c.π.app i ⁻¹ᵁ V a)
        (t : ∀ a, K a → Γ(D.obj i, V a)),
        ∀ a k, s a k = (c.π.app i).appLE (V a) (U a) (e a).le (t a k) := by
  obtain ⟨i, W, hcoverW, hW⟩ :=
    exists_isOpenCover_and_isAffine_of_finite D c hc U hcover hU
  have e : U = fun a => c.π.app i ⁻¹ᵁ W a := funext fun a => (hW a).2
  subst U
  obtain ⟨j, t, ht⟩ := exists_common_appLE_eq_families_of_isLimit D c hc i W
    (fun a => (hW a).1) s
  refine ⟨j.left, fun a => D.map j.hom ⁻¹ᵁ W a, ?_,
    fun a => (hW a).1.preimage (D.map j.hom), ?_⟩
  · change (⨆ a, D.map j.hom ⁻¹ᵁ W a) = ⊤
    rw [← Hom.preimage_iSup, hcoverW.iSup_eq_top]
    simp
  · refine ⟨fun a => ?_, t, ht⟩
    rw [← Hom.comp_preimage, c.w]

end AlgebraicGeometry.Scheme
