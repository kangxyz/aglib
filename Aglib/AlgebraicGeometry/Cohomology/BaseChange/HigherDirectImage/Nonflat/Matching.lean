/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartRefinementMap
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartRefinement
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Refinement

/-! # Matching of the actual nonflat affine chart arrows

Common affine refinements identify the original Hom-sheaf sections. The
ordinary Hom sheaf's separation gives matching on each overlap, which is
the exact compatibility required by native module-Hom gluing.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- On every overlap, the original affine chart maps give matching sections of the native
module-Hom sheaf. The common-refinement compatibility is proved internally. -/
theorem chartMap_homSections_matching (C D : AffineBaseChangeChart g) :
    let E := (pullback g).obj (((pushforward f).rightDerived n).obj M)
    let F := ((pushforward b).rightDerived n).obj ((pullback a).obj M)
    let H := InternalHom.sheaf V E F
    H.val.presheaf.map
        (homOfLE (inf_le_left : C.target.opensRange ⊓ D.target.opensRange ≤
          C.target.opensRange)).op
        (InternalHom.restrictionHomEquiv C.target E F
          (chartMap a b f g h C.source C.target C.scalar C.comm n M)) =
      H.val.presheaf.map
        (homOfLE (inf_le_right : C.target.opensRange ⊓ D.target.opensRange ≤
          D.target.opensRange)).op
        (InternalHom.restrictionHomEquiv D.target E F
          (chartMap a b f g h D.source D.target D.scalar D.comm n M)) := by
  let E := (pullback g).obj (((pushforward f).rightDerived n).obj M)
  let F := ((pushforward b).rightDerived n).obj ((pullback a).obj M)
  let H := InternalHom.sheaf V E F
  let sC := InternalHom.restrictionHomEquiv C.target E F
    (chartMap a b f g h C.source C.target C.scalar C.comm n M)
  let sD := InternalHom.restrictionHomEquiv D.target E F
    (chartMap a b f g h D.source D.target D.scalar D.comm n M)
  apply TopCat.Presheaf.IsSheaf.section_ext H.isSheaf
  intro x hx
  have hrange : Set.range (Limits.pullback.fst C.target D.target ≫ C.target) =
      (C.target.opensRange ⊓ D.target.opensRange : V.Opens) :=
    IsOpenImmersion.range_pullback_to_base_of_left C.target D.target
  have hxrange : x ∈ Set.range (Limits.pullback.fst C.target D.target ≫ C.target) := by
    rw [hrange]
    exact hx
  obtain ⟨xT, hxT⟩ := hxrange
  obtain ⟨A, B, s, z, ρ₁, ρ₂, r, hs, hz, hρ₁, hρ₂, hxz, h₁, h₂, hr₁, hr₂⟩ :=
    Scheme.exists_commonAffineBaseChangeRefinement g C.source D.source C.target D.target
      (Spec.map C.scalar) (Spec.map D.scalar) C.comm D.comm xT
  let := hs
  let := hz
  let := hρ₁
  let := hρ₂
  let τ₁ := z ≫ Limits.pullback.fst C.target D.target
  let τ₂ := z ≫ Limits.pullback.snd C.target D.target
  let t := τ₁ ≫ C.target
  have ht₂ : τ₂ ≫ D.target = t := by
    dsimp only [τ₁, τ₂, t]
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have ht : IsOpenImmersion t := inferInstance
  let := ht
  have hcomm : Spec.map (Spec.preimage r) ≫ s = t ≫ g := by
    rw [Spec.map_preimage, ← h₁, ← Category.assoc, hr₁]
    simp only [τ₁, t, Category.assoc, C.comm]
  let K : AffineBaseChangeChart g :=
    { sourceRing := A
      targetRing := B
      source := s
      target := t
      scalar := Spec.preimage r
      source_open := hs
      target_open := ht
      comm := hcomm }
  have hτ₁ : Spec.map (Spec.preimage τ₁) ≫ C.target = K.target := by
    rw [Spec.map_preimage]
  have hτ₂ : Spec.map (Spec.preimage τ₂) ≫ D.target = K.target := by
    rw [Spec.map_preimage]; exact ht₂
  have hsource₁ : Spec.map (Spec.preimage ρ₁) ≫ C.source = K.source := by
    rw [Spec.map_preimage]; exact h₁
  have hsource₂ : Spec.map (Spec.preimage ρ₂) ≫ D.source = K.source := by
    rw [Spec.map_preimage]; exact h₂
  have hb₁ : Spec.map (Spec.preimage τ₁) ≫ Spec.map C.scalar =
      Spec.map K.scalar ≫ Spec.map (Spec.preimage ρ₁) := by
    simp only [K, Spec.map_preimage]
    simpa only [τ₁, Category.assoc] using hr₁.symm
  have hb₂ : Spec.map (Spec.preimage τ₂) ≫ Spec.map D.scalar =
      Spec.map K.scalar ≫ Spec.map (Spec.preimage ρ₂) := by
    simp only [K, Spec.map_preimage]
    simpa only [τ₂, Category.assoc] using hr₂.symm
  let : IsOpenImmersion (Spec.map (Spec.preimage ρ₁)) := by
    rw [Spec.map_preimage]; infer_instance
  let : IsOpenImmersion (Spec.map (Spec.preimage ρ₂)) := by
    rw [Spec.map_preimage]; infer_instance
  let : IsOpenImmersion (Spec.map (Spec.preimage τ₁)) := by
    rw [Spec.map_preimage]; infer_instance
  let : IsOpenImmersion (Spec.map (Spec.preimage τ₂)) := by
    rw [Spec.map_preimage]; infer_instance
  have hsq₁ := chartMap_refinement a b f g h C K (Spec.preimage ρ₁) (Spec.preimage τ₁)
    hsource₁ hτ₁ hb₁ n M
  have hsq₂ := chartMap_refinement a b f g h D K (Spec.preimage ρ₂) (Spec.preimage τ₂)
    hsource₂ hτ₂ hb₂ n M
  have hc := canonicalRestrictionHomEquiv_refinement C.target K.target
    (Spec.map (Spec.preimage τ₁)) hτ₁.symm E F _ _ hsq₁
  have hd := canonicalRestrictionHomEquiv_refinement D.target K.target
    (Spec.map (Spec.preimage τ₂)) hτ₂.symm E F _ _ hsq₂
  have hle₁ : K.target.opensRange ≤ C.target.opensRange := by
    rintro y ⟨z, hz⟩
    refine ⟨(Spec.map (Spec.preimage τ₁)) z, ?_⟩
    exact (congrArg (fun k : Spec K.targetRing ⟶ V => k z) hτ₁).trans hz
  have hle₂ : K.target.opensRange ≤ D.target.opensRange := by
    rintro y ⟨z, hz⟩
    refine ⟨(Spec.map (Spec.preimage τ₂)) z, ?_⟩
    exact (congrArg (fun k : Spec K.targetRing ⟶ V => k z) hτ₂).trans hz
  have hle : K.target.opensRange ≤ C.target.opensRange ⊓ D.target.opensRange :=
    le_inf hle₁ hle₂
  have hxK : x ∈ K.target.opensRange := by
    obtain ⟨y, hy⟩ := hxz
    refine ⟨y, ?_⟩
    change C.target (Limits.pullback.fst C.target D.target (z y)) = x
    rw [hy]
    exact hxT
  refine ⟨K.target.opensRange, hle, hxK, ?_⟩
  change H.val.presheaf.map (homOfLE hle).op
      (H.val.presheaf.map (homOfLE inf_le_left).op sC) =
    H.val.presheaf.map (homOfLE hle).op
      (H.val.presheaf.map (homOfLE inf_le_right).op sD)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact hc.trans hd.symm

/-- The internally constructed actual affine arrows satisfy the native module-Hom overlap
compatibility condition. This is a proved fact, not a constructor input. -/
theorem chartMap_compatible :
    InternalHom.RestrictionHomCompatible
      (fun C : AffineBaseChangeChart g => C.target)
      ((pullback g).obj (((pushforward f).rightDerived n).obj M))
      (((pushforward b).rightDerived n).obj ((pullback a).obj M))
      (fun C => chartMap a b f g h C.source C.target C.scalar C.comm n M) :=
  canonicalRestrictionHomCompatible_of_sections
    (fun C : AffineBaseChangeChart g => Spec C.targetRing) (fun C => C.target) _ _ _
    (chartMap_homSections_matching a b f g h n M)

end AlgebraicGeometry.Scheme.Modules.Nonflat
