/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteModels
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.CoverDescent
public import Mathlib.AlgebraicGeometry.Limits

/-! # Descent of actual finite affine etale covering families -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- A finite affine etale covering family of a ring-colimit spectrum has an
actual covering family model at one stage, with literal pullback comparisons. -/
theorem exists_affine_etale_cover_model_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    {J : Type v} [Finite J] (Y : J → Over (Spec c.pt))
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : Spec c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x) :
    ∃ (i : I) (Z : J → Over (Spec (F.obj i))),
      (∀ j, IsAffine (Z j).left) ∧ (∀ j, Etale (Z j).hom) ∧
      (∀ j, Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj (Z j) ≅ Y j)) ∧
      ∀ x : Spec (F.obj i), ∃ j, ∃ y : (Z j).left, (Z j).hom y = x := by
  classical
  obtain ⟨i, hi⟩ := exists_common_affine_etale_models_of_isColimit F c hc Y
  choose Z hZ he e using hi
  let σ := Spec.map (c.ι.app i)
  have hpb : ∀ x : Spec c.pt, ∃ j, ∃ y : (pullback σ (Z j).hom : Scheme),
      pullback.fst σ (Z j).hom y = x := by
    intro x
    obtain ⟨j, y, hy⟩ := hcover x
    let ej := Classical.choice (e j)
    refine ⟨j, (pullbackSymmetry σ (Z j).hom).inv (ej.inv.left y), ?_⟩
    have h₁ := congrArg (fun a : (Y j).left ⟶ Spec c.pt ↦ a y) (Over.w ej.inv)
    have h₂ := congrArg (fun a : pullback (Z j).hom σ ⟶ Spec c.pt ↦ a (ej.inv.left y))
      (pullbackSymmetry_inv_comp_fst σ (Z j).hom)
    exact h₂.trans (h₁.trans hy)
  let D := F.op ⋙ Scheme.Spec
  let d := Scheme.Spec.mapCone c.op
  have hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  have (j : Iᵒᵖ) : CompactSpace (D.obj j) := inferInstanceAs (CompactSpace (Spec (F.obj j.unop)))
  have {j k : Iᵒᵖ} (a : j ⟶ k) : IsAffineHom (D.map a) :=
    inferInstanceAs (IsAffineHom (Spec.map (F.map a.unop)))
  have (j : J) : Etale (Z j).hom := he j
  obtain ⟨k, q, hk⟩ := exists_jointlySurjective_pullback_family D d hd
    (fun j ↦ (Z j).left) (fun j ↦ (Z j).hom) hpb
  let τ := Spec.map (F.map q.unop)
  let Z' (j : J) := (Over.pullback τ).obj (Z j)
  refine ⟨k.unop, Z', ?_, ?_, ?_, ?_⟩
  · intro j
    have : IsAffine (Z j).left := hZ j
    change IsAffine (pullback (Z j).hom τ)
    infer_instance
  · intro j
    change Etale (pullback.snd (Z j).hom τ)
    infer_instance
  · intro j
    have hστ : Spec.map (c.ι.app k.unop) ≫ τ = σ := by
      dsimp [τ, σ]
      rw [← Spec.map_comp, c.w]
    exact ⟨((Over.pullbackComp (Spec.map (c.ι.app k.unop)) τ).app (Z j)).symm ≪≫
      eqToIso (congrArg (fun a : Spec c.pt ⟶ Spec (F.obj i) ↦
        (Over.pullback a).obj (Z j)) hστ) ≪≫ Classical.choice (e j)⟩
  · intro x
    obtain ⟨j, y, hy⟩ := hk x
    refine ⟨j, (pullbackSymmetry τ (Z j).hom).hom y, ?_⟩
    have h := congrArg (fun a : pullback τ (Z j).hom ⟶ Spec (F.obj k.unop) ↦ a y)
      (pullbackSymmetry_hom_comp_snd τ (Z j).hom)
    exact h.trans hy

end AlgebraicGeometry.Scheme.EtaleAffineBasis
