/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.RepresentablePullback

/-! # Original affine etale generators over arbitrary separated bases

The actual non-Noetherian affine-etale partitions provide the original
affine-local finite-partition input. For affine-source tests on a separated
scheme, the structural map is affine. Nonzero-modulus original free
representables are therefore constructible with no Noetherian premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge

/-- The exact original affine-local finite-etale partition family for an
affine structural map, on any base scheme. -/
theorem finiteEtalePartitions_of_isAffineHom
    {X : Scheme.{u}} (U : X.Etale) [IsAffineHom U.hom] :
    ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom := by
  intro V
  let f : ((siteBaseChange V.1.ι).obj U).left ⟶ V.1.toScheme :=
    ((siteBaseChange V.1.ι).obj U).hom
  have : IsAffineHom f := MorphismProperty.pullback_snd U.hom V.1.ι inferInstance
  obtain ⟨p, hp⟩ := exists_finitePartition_of_isAffineHom_of_etale (X := V.1.toScheme) f
  refine ⟨p, fun i => ?_⟩
  change IsFinite (pullback.snd U.hom (p.inclusion i ≫ V.1.ι))
  exact (isFinite_pullback_snd_comp_iff U.hom V.1.ι (p.inclusion i)).mpr (hp i)

/-- The original positive-modulus free representable of an affine etale
structural map is constructible over any scheme. -/
theorem freeZModRepresentable_isConstructible_of_isAffineHom
    {X : Scheme.{u}} (U : X.Etale) [IsAffineHom U.hom] (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) :=
  freeZModRepresentable_isConstructible_of_finiteEtalePartitions U n hn
    (finiteEtalePartitions_of_isAffineHom U)

/-- Actual affine-local partitions of an affine-source etale test over a
separated base, without a Noetherian assumption. -/
theorem finiteEtalePartitions_of_isAffine_of_isSeparated
    {X : Scheme.{u}} [IsSeparated (terminal.from X)] (U : X.Etale) [IsAffine U.left] :
    ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom := by
  let f : U.left ⟶ X := U.hom
  have : IsAffineHom (f ≫ terminal.from X) :=
    isAffineHom_of_isAffine (X := U.left) (Y := ⊤_ Scheme.{u}) _
  have : IsAffineHom U.hom := IsAffineHom.of_comp (X := U.left) f (terminal.from X)
  exact finiteEtalePartitions_of_isAffineHom U

/-- Every original affine-source etale free generator at nonzero modulus
is constructible on an arbitrary separated scheme. -/
theorem freeZModRepresentable_isConstructible_of_isAffine_of_isSeparated
    {X : Scheme.{u}} [IsSeparated (terminal.from X)]
    (U : X.Etale) [IsAffine U.left] (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) :=
  freeZModRepresentable_isConstructible_of_finiteEtalePartitions U n hn
    (finiteEtalePartitions_of_isAffine_of_isSeparated U)

/-- The literal original affine-etale site generators are constructible at
nonzero modulus over arbitrary separated bases. -/
theorem freeZModAffineRepresentable_isConstructible_of_isSeparated
    {X : Scheme.{u}} [IsSeparated (terminal.from X)]
    (U : X.AffineEtale) (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
      ((AffineEtale.Spec X).obj U)) := by
  have : IsAffine ((AffineEtale.Spec X).obj U).left :=
    inferInstanceAs (IsAffine (Spec U.left.unop))
  exact freeZModRepresentable_isConstructible_of_isAffine_of_isSeparated
    ((AffineEtale.Spec X).obj U) n hn

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
