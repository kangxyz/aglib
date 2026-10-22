/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FinitePrincipalRangeDescent

/-!
# Common stages for sections on specified affine opens

Finite families of sections in finitely many actual scheme-limit diagrams lift
to one common index. For specified affine stage opens, the comparison is stated
in the original ambient section carrier through the actual `appLE` map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Finite families in finitely many qcqs affine-transition diagrams lift at one
common index. The single-diagram family theorem is reused for each diagram. -/
lemma exists_common_appTop_π_eq_families_of_isLimit
    {J : Type v} [Finite J] (E : J → I ⥤ Scheme.{u})
    (c : ∀ a, Cone (E a)) (hc : ∀ a, IsLimit (c a))
    [∀ a, ∀ {i j} (f : i ⟶ j), IsAffineHom ((E a).map f)]
    [∀ a i, CompactSpace ((E a).obj i)] [∀ a i, QuasiSeparatedSpace ((E a).obj i)]
    {K : J → Type w} [∀ a, Finite (K a)] (s : ∀ a, K a → Γ((c a).pt, ⊤)) :
    ∃ (i : I) (t : ∀ a, K a → Γ((E a).obj i, ⊤)),
      ∀ a k, s a k = ((c a).π.app i).appTop (t a k) := by
  classical
  let _ := Fintype.ofFinite J
  choose i t ht using fun a => exists_appTop_π_eq_family_of_isLimit (E a) (c a) (hc a) (s a)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (a : J) : j ⟶ i a :=
    (hj (Finset.mem_image_of_mem i (Finset.mem_univ a))).some
  refine ⟨j, fun a k => ((E a).map (q a)).appTop (t a k), fun a k => ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, (c a).w]
  exact ht a k

/-- Sections on a finite family of specified affine stage opens lift together.
The output equation lives in the original section ring, not in an implicitly
identified section ring of a restriction scheme. -/
lemma exists_common_appLE_eq_families_of_isLimit
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) {J : Type v} [Finite J] (W : J → (D.obj i).Opens)
    (hW : ∀ a, IsAffineOpen (W a)) {K : J → Type w} [∀ a, Finite (K a)]
    (s : ∀ a, K a → Γ(c.pt, c.π.app i ⁻¹ᵁ W a)) :
    ∃ (j : Over i) (t : ∀ a, K a → Γ(D.obj j.left, D.map j.hom ⁻¹ᵁ W a)),
      ∀ a k, s a k = (c.π.app j.left).appLE (D.map j.hom ⁻¹ᵁ W a)
        (c.π.app i ⁻¹ᵁ W a) (by rw [← Scheme.Hom.comp_preimage, c.w]) (t a k) := by
  classical
  have (a : J) (j : Over i) : IsAffine ((opensDiagram D i (W a)).obj j) :=
    (hW a).preimage (D.map j.hom)
  obtain ⟨j, t₀, ht₀⟩ := exists_common_appTop_π_eq_families_of_isLimit
    (fun a => opensDiagram D i (W a)) (fun a => opensCone D c i (W a))
    (fun a => isLimitOpensCone D c hc i (W a))
    (fun a k => (c.π.app i ⁻¹ᵁ W a).topIso.inv (s a k))
  have hlift (a : J) (k : K a) : ∃ t : Γ(D.obj j.left, D.map j.hom ⁻¹ᵁ W a),
      (D.map j.hom ⁻¹ᵁ W a).topIso.inv t = t₀ a k :=
    (D.map j.hom ⁻¹ᵁ W a).topIso.symm.commRingCatIsoToRingEquiv.surjective (t₀ a k)
  choose t ht using hlift
  refine ⟨j, t, fun a k => ?_⟩
  have h := ht₀ a k
  rw [← ht a k] at h
  convert!
    show s a k = ((D.map j.hom ⁻¹ᵁ W a).topIso.inv ≫
        ((opensCone D c i (W a)).π.app j).appTop ≫
        (c.π.app i ⁻¹ᵁ W a).topIso.hom) (t a k) from
      (c.π.app i ⁻¹ᵁ W a).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp h using 3
  simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]

end AlgebraicGeometry
