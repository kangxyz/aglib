/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineModelDescent
public import Mathlib.CategoryTheory.Filtered.Small

/-! # Common finite stages for affine etale families -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- A finite affine etale family over a ring colimit descends to one common
stage, retaining the actual structural triangles and pullback isomorphisms. -/
theorem exists_common_affine_etale_models_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    {J : Type v} [Finite J] (Y : J → Over (Spec c.pt))
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom] :
    ∃ i : I, ∀ j, ∃ Yᵢ : Over (Spec (F.obj i)),
      IsAffine Yᵢ.left ∧ Etale Yᵢ.hom ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj Yᵢ ≅ Y j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i Z hZ he heq using fun j ↦
    exists_affine_etale_model_of_isColimit F c hc (Y j)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let q (j : J) : i j ⟶ k := (hk (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨k, fun j ↦ ?_⟩
  let : IsAffine (Z j).left := hZ j
  let : Etale (Z j).hom := he j
  let τ := Spec.map (F.map (q j))
  let σ := Spec.map (c.ι.app k)
  let Z' := (Over.pullback τ).obj (Z j)
  have hστ : σ ≫ τ = Spec.map (c.ι.app (i j)) := by
    dsimp [σ, τ]
    rw [← Spec.map_comp, c.w]
  let ebc : (Over.pullback σ).obj Z' ≅
      (Over.pullback (Spec.map (c.ι.app (i j)))).obj (Z j) :=
    ((Over.pullbackComp σ τ).app (Z j)).symm ≪≫
      eqToIso (congrArg (fun h : Spec c.pt ⟶ Spec (F.obj (i j)) ↦
        (Over.pullback h).obj (Z j)) hστ)
  refine ⟨Z', ?_, ?_, ⟨ebc ≪≫ Classical.choice (heq j)⟩⟩
  · change IsAffine (pullback (Z j).hom τ)
    infer_instance
  · change Etale (pullback.snd (Z j).hom τ)
    infer_instance

end AlgebraicGeometry.Scheme.EtaleAffineBasis
