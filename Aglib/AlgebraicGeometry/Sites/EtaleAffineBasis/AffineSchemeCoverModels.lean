/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteCoverModelsAbove
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeSectionEquality
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # Native affine covering models over affine-scheme limit cones -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v

/-- A finite affine etale cover of an actual affine-scheme inverse limit descends
above a prescribed stage. The comparison is an isomorphism in the original
Over category and preserves the structural map. -/
theorem exists_affineScheme_cover_model_above
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I)
    {J : Type v} [Finite J] (Y : J → Over c.pt)
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x) :
    ∃ (k : I) (_ : k ⟶ i) (Z : J → Over (D.obj k)),
      (∀ j, IsAffine (Z j).left) ∧ (∀ j, Etale (Z j).hom) ∧
      (∀ j, Nonempty ((Over.pullback (c.π.app k)).obj (Z j) ≅ Y j)) ∧
      ∀ x : D.obj k, ∃ j, ∃ y : (Z j).left, (Z j).hom y = x := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have (j : I) : IsAffine (((Functor.const I).obj c.pt).obj j) :=
    inferInstanceAs (IsAffine c.pt)
  let R := D.op ⋙ Scheme.Γ
  let d := Scheme.Γ.mapCocone c.op
  have hd : IsColimit d := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let Y' (j : J) : Over (Spec d.pt) := (Over.map c.pt.isoSpec.hom).obj (Y j)
  have (j : J) : IsAffine (Y' j).left := inferInstanceAs (IsAffine (Y j).left)
  have (j : J) : Etale (Y' j).hom := by
    change Etale ((Y j).hom ≫ c.pt.isoSpec.hom)
    infer_instance
  have hcov' : ∀ x : Spec d.pt, ∃ j, ∃ y : (Y' j).left, (Y' j).hom y = x := by
    intro x
    obtain ⟨j, y, hy⟩ := hcover (c.pt.isoSpec.inv x)
    refine ⟨j, y, ?_⟩
    change c.pt.isoSpec.hom ((Y j).hom y) = x
    rw [hy]
    exact congrArg (fun q : Spec d.pt ⟶ Spec d.pt ↦ q x) c.pt.isoSpec.inv_hom_id
  obtain ⟨k, q, Z', hZ, he, hm, hcov⟩ :=
    exists_affine_etale_cover_model_of_isColimit_above R d hd (op i) Y' hcov'
  let e : D.obj k.unop ≅ Spec (R.obj k) := (D.obj k.unop).isoSpec
  have (j : J) : IsAffine (Z' j).left := hZ j
  have (j : J) : Etale (Z' j).hom := he j
  let Z (j : J) := (Over.pullback e.hom).obj (Z' j)
  refine ⟨k.unop, q.unop, Z, ?_, ?_, ?_, ?_⟩
  · intro j
    change IsAffine (pullback (Z' j).hom e.hom)
    infer_instance
  · intro j
    change Etale (pullback.snd (Z' j).hom e.hom)
    infer_instance
  · intro j
    have hnat : c.π.app k.unop ≫ e.hom =
        c.pt.isoSpec.hom ≫ Spec.map (d.ι.app k) :=
      (Scheme.isoSpec_hom_naturality (c.π.app k.unop)).symm
    exact ⟨((Over.pullbackComp (c.π.app k.unop)
      e.hom).app (Z' j)).symm ≪≫
      eqToIso (congrArg (fun a ↦ (Over.pullback a).obj (Z' j)) hnat) ≪≫
      (Over.pullbackComp c.pt.isoSpec.hom (Spec.map (d.ι.app k))).app (Z' j) ≪≫
      (Over.pullback c.pt.isoSpec.hom).mapIso (Classical.choice (hm j)) ≪≫
      (asIso ((Over.mapPullbackAdj c.pt.isoSpec.hom).unit.app (Y j))).symm⟩
  · intro x
    obtain ⟨j, y, hy⟩ := hcov (e.hom x)
    refine ⟨j, ?_⟩
    have hx : x ∈ Set.range (pullback.snd (Z' j).hom e.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨y, hy⟩
    exact hx
end AlgebraicGeometry.Scheme.EtaleAffineBasis
