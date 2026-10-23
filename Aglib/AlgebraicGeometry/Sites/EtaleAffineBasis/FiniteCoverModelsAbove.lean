/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteCoverModels

/-! # Actual finite affine covering models above a prescribed stage -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- A finite affine etale cover of a ring-colimit spectrum has a covering model
above any specified stage. The output arrow keeps previously defined sections
available at the new stage. -/
theorem exists_affine_etale_cover_model_of_isColimit_above
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (i : I)
    {J : Type v} [Finite J] (Y : J → Over (Spec c.pt))
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : Spec c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x) :
    ∃ (k : I) (_ : i ⟶ k) (Z : J → Over (Spec (F.obj k))),
      (∀ j, IsAffine (Z j).left) ∧ (∀ j, Etale (Z j).hom) ∧
      (∀ j, Nonempty ((Over.pullback (Spec.map (c.ι.app k))).obj (Z j) ≅ Y j)) ∧
      ∀ x : Spec (F.obj k), ∃ j, ∃ y : (Z j).left, (Z j).hom y = x := by
  classical
  obtain ⟨l, Z, hZ, he, e, hcov⟩ :=
    exists_affine_etale_cover_model_of_isColimit F c hc Y hcover
  let k := IsFiltered.max i l
  let q : l ⟶ k := IsFiltered.rightToMax i l
  let τ := Spec.map (F.map q)
  let Z' (j : J) := (Over.pullback τ).obj (Z j)
  have (j : J) : IsAffine (Z j).left := hZ j
  have (j : J) : Etale (Z j).hom := he j
  refine ⟨k, IsFiltered.leftToMax i l, Z', ?_, ?_, ?_, ?_⟩
  · intro j
    change IsAffine (pullback (Z j).hom τ)
    infer_instance
  · intro j
    change Etale (pullback.snd (Z j).hom τ)
    infer_instance
  · intro j
    have hστ : Spec.map (c.ι.app k) ≫ τ = Spec.map (c.ι.app l) := by
      dsimp [τ]
      rw [← Spec.map_comp, c.w]
    exact ⟨((Over.pullbackComp (Spec.map (c.ι.app k)) τ).app (Z j)).symm ≪≫
      eqToIso (congrArg (fun a : Spec c.pt ⟶ Spec (F.obj l) ↦
        (Over.pullback a).obj (Z j)) hστ) ≪≫ Classical.choice (e j)⟩
  · intro x
    obtain ⟨j, y, hy⟩ := hcov (τ x)
    refine ⟨j, ?_⟩
    have hx : x ∈ Set.range (pullback.snd (Z j).hom τ) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨y, hy⟩
    exact hx

end AlgebraicGeometry.Scheme.EtaleAffineBasis
