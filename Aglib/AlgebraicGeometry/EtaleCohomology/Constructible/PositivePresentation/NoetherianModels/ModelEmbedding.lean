/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.GeneratorModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.EmbeddingTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.AffineRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AffineFPTransport

/-! # Actual finite embeddings from Noetherian models of canonical stages

On a separated Noetherian model, native positive stages have geometric
constructibility and ambient finite presentation on every original affine
open. The original open-spectrum bridge therefore supplies the exact input
to the global finite-embedding producer. Original exact inverse image and
ordinary finite base change transport its actual record to the original
coefficient through the specified model isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

/-- A canonical positive stage on an actual separated Noetherian scheme has
an original finite constant product embedding. Every geometric and affine
FP input is supplied by the native original-stage producers. -/
def canonicalStageEmbeddingOfIsNoetherian
    (X : Scheme.{u}) [IsNoetherian X] [X.IsSeparated] (n : ℕ) (hn : n ≠ 0)
    (M : BoundedPresentation.Coefficient X n)
    (hM : BoundedPresentation.finiteColimitStages X n M) :
    FiniteConstantProductEmbedding M.obj := by
  let : IsSeparated (terminal.from X) :=
    (inferInstance : X.IsSeparated).isSeparated_terminal_from
  have hparts (U : X.AffineEtale) :
      ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom := by
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact finiteEtalePartitions_of_isAffine_of_isSeparated
      ((Scheme.AffineEtale.Spec X).obj U)
  have hconstructible : IsConstructible M.obj :=
    finiteColimitStage_isConstructible_of_finiteEtalePartitions X n hn hparts M hM
  have hFP (V : X.affineOpens) :
      IsFinitelyPresentable.{u + 1} ((inverseImage V.1.ι).obj M.obj) :=
    finiteColimitStage_affineRestriction_isFinitelyPresentable X n V M hM
  exact Global.finiteConstantProductEmbeddingOfIsNoetherian X M.obj hconstructible
    (Proper.affineRestriction_isFinitelyPresentable_spec_open M.obj hFP)

/-- A genuine canonical-stage model over actual separated Noetherian stages
gives the original finite constant product embedding on the limit scheme.
The finite family, actual finite pullbacks, and finite values are constructed. -/
theorem exists_finiteConstantProductEmbedding_of_hasStageModel
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
    [∀ i, IsNoetherian (X.obj i).unop] [∀ i, (X.obj i).unop.IsSeparated]
    (n : ℕ) (hn : n ≠ 0) (A : BoundedPresentation.Coefficient c.pt.unop n)
    (hA : HasStageModel X c n A) : Nonempty (FiniteConstantProductEmbedding A.obj) := by
  obtain ⟨i₀⟩ := IsFiltered.nonempty (C := I)
  obtain ⟨i, _, M, hM, ⟨e⟩⟩ := hA i₀
  let t := canonicalStageEmbeddingOfIsNoetherian (X.obj i).unop n hn M hM
  let t' := finiteConstantProductEmbeddingInverseImage (c.ι.app i).unop t
  exact ⟨finiteConstantProductEmbeddingOfMono e.inv.hom t'⟩

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
