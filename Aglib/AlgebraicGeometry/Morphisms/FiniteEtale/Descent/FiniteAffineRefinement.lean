/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Replace an etale cover of a quasi-compact scheme by a finite affine family
and its actual surjective etale affine covering scheme. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineRefinement

universe u v
variable {X : Scheme.{u}}

/-- A finite affine family refining the original etale cover. The refinement
maps are open immersions, so the original local data can be restricted to it. -/
structure Data (𝒰 : X.Cover (Scheme.precoverage @Etale)) where
  /-- The affine etale cover used as the refinement. -/
  affine : Scheme.AffineCover.{u} @Etale X
  finite_index : Finite affine.I₀
  /-- The morphism from the affine cover to the original etale cover `𝒰`. -/
  refinement : affine.cover ⟶ 𝒰
  open_refinement : ∀ j, IsOpenImmersion (refinement.h₀ j)

attribute [instance] Data.finite_index Data.open_refinement

/-- Etale cover maps are open; compactness yields a finite affine refinement. -/
def choose (𝒰 : X.Cover (Scheme.precoverage @Etale)) [CompactSpace X] : Data 𝒰 := by
  apply Classical.choice
  have hEtale (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (𝒰.f i).isOpenMap)
  obtain ⟨𝒱, f, hfin, hopen⟩ := QuasiCompactCover.exists_hom (𝒰 := 𝒰)
  exact ⟨⟨𝒱, hfin, f, hopen⟩⟩

namespace Data
variable {𝒰 : X.Cover (Scheme.precoverage @Etale)} (D : Data 𝒰)

/-- A single affine scheme obtained from the finite family by disjoint union. -/
def coveringScheme : Scheme.{u} := ∐ fun i => Spec (D.affine.X i)

instance : IsAffine D.coveringScheme := by
  dsimp [coveringScheme]
  infer_instance

/-- The structural morphism from the affine covering scheme. -/
def coveringMap : D.coveringScheme ⟶ X := Sigma.desc D.affine.f

instance : Etale D.coveringMap :=
  IsZariskiLocalAtSource.sigmaDesc D.affine.map_prop

instance : Surjective D.coveringMap where
  surj x := by
    obtain ⟨y, hy⟩ := D.affine.covers x
    refine ⟨Sigma.ι (fun i => Spec (D.affine.X i)) (D.affine.idx x) y, ?_⟩
    change (Sigma.ι _ _ ≫ Sigma.desc D.affine.f) y = x
    rwa [Sigma.ι_comp_desc]

/-- Coordinates of the actual affine covering scheme. -/
def ring : CommRingCat.{u} := Γ(D.coveringScheme, ⊤)

/-- The covering map from the spectrum of the coordinate ring of the affine covering scheme to
`X`. -/
def specMap : Spec D.ring ⟶ X := D.coveringScheme.isoSpec.inv ≫ D.coveringMap

instance : Etale D.specMap := by
  dsimp [specMap]
  infer_instance

instance : Surjective D.specMap := by
  dsimp [specMap]
  infer_instance

end Data

variable {R : CommRingCat.{u}} {𝒰 : (Spec R).Cover (Scheme.precoverage @Etale)}

/-- The affine cover over an affine base gives an explicit faithfully flat
ring map, including the empty-base case. -/
theorem Data.ringMap_faithfullyFlat (D : Data 𝒰) :
    (Spec.preimage D.specMap).hom.FaithfullyFlat := by
  apply (flat_and_surjective_SpecMap_iff _).1
  rw [Spec.map_preimage]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.FiniteEtale.AffineRefinement

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ad622a629a406441a624898c789685803a13b8dd177095eec79cfe2e027270d8.
Definitions, hypotheses and universes are retained modulo native names. -/
