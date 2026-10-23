/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.NoetherianAffine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.RepresentablePullback
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite

/-! # Original positive-modulus generators over separated locally Noetherian bases

The actual Noetherian affine-morphism partition feeds the accepted original
free-generator pullback comparison. Affine-source etale generators over a
separated locally Noetherian base satisfy the affine-morphism hypothesis.
The modulus is nonzero and the original coefficient universe is retained.
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

/-- Actual finite-etale partitions for every original affine-local base
change of an affine etale structural map over a locally Noetherian base. -/
theorem finiteEtalePartitions_of_isAffineHom_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Etale) [IsAffineHom U.hom] :
    ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom := by
  intro V
  have : IsNoetherian V.1.toScheme := ⟨⟩
  let f : ((siteBaseChange V.1.ι).obj U).left ⟶ V.1.toScheme :=
    ((siteBaseChange V.1.ι).obj U).hom
  have : IsAffineHom f := MorphismProperty.pullback_snd U.hom V.1.ι inferInstance
  obtain ⟨p, hp⟩ := exists_finitePartition_of_isAffineHom_of_noetherian
    (X := V.1.toScheme) f
  refine ⟨p, fun i => ?_⟩
  change IsFinite (pullback.snd U.hom (p.inclusion i ≫ V.1.ι))
  exact (isFinite_pullback_snd_comp_iff U.hom V.1.ι (p.inclusion i)).mpr (hp i)

/-- The actual affine-local partitions of an affine etale structural map
over a locally Noetherian base make its original positive-modulus free
representable constructible. -/
theorem freeZModRepresentable_isConstructible_of_isAffineHom_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Etale) [IsAffineHom U.hom]
    (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) :=
  freeZModRepresentable_isConstructible_of_finiteEtalePartitions U n hn
    (finiteEtalePartitions_of_isAffineHom_of_isLocallyNoetherian U)

/-- The exact original affine-local geometric partition family for an
affine-source etale test over a separated locally Noetherian base. -/
theorem finiteEtalePartitions_of_isAffine_of_isSeparated_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsSeparated (terminal.from X)]
    (U : X.Etale) [IsAffine U.left] :
    ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom := by
  let f : U.left ⟶ X := U.hom
  have : IsAffineHom (f ≫ terminal.from X) :=
    isAffineHom_of_isAffine (X := U.left) (Y := ⊤_ Scheme.{u}) _
  have : IsAffineHom U.hom := IsAffineHom.of_comp (X := U.left) f (terminal.from X)
  exact finiteEtalePartitions_of_isAffineHom_of_isLocallyNoetherian U

/-- Over a separated locally Noetherian scheme, every actual affine-source
etale test gives an original constructible positive-modulus free generator. -/
theorem freeZModRepresentable_isConstructible_of_isAffine_of_isSeparated_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsSeparated (terminal.from X)]
    (U : X.Etale) [IsAffine U.left] (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) :=
  freeZModRepresentable_isConstructible_of_finiteEtalePartitions U n hn
    (finiteEtalePartitions_of_isAffine_of_isSeparated_of_isLocallyNoetherian U)

/-- The original affine-etale site generators satisfy the same positive-
modulus constructibility endpoint under the explicit separated locally
Noetherian hypotheses. -/
theorem freeZModAffineRepresentable_isConstructible_of_isSeparated_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsSeparated (terminal.from X)]
    (U : X.AffineEtale) (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
      ((AffineEtale.Spec X).obj U)) := by
  have : IsAffine ((AffineEtale.Spec X).obj U).left :=
    inferInstanceAs (IsAffine (Spec U.left.unop))
  exact freeZModRepresentable_isConstructible_of_isAffine_of_isSeparated_of_isLocallyNoetherian
    ((AffineEtale.Spec X).obj U) n hn

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
