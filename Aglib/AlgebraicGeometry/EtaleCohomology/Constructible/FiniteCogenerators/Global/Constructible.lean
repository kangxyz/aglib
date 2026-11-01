/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentation.Affine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackPartition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AffineFPTransport

/-! # Finite constant cogenerators without an affine compactness premise

The actual constructible partition on each original affine open makes its
original restriction constructible. The ordinary affine constructible-to-FP
theorem supplies exactly the compactness input of the existing global finite
constant-product construction. No affine FP hypothesis remains in this
consumer, and no new coefficient category or finite-normalization assumption
is introduced. Noetherianity is used only by the original global cogenerator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A constructible coefficient has ordinarily finitely presentable original
affine-open restrictions, over an arbitrary base scheme. -/
theorem affineRestriction_isFinitelyPresentable_of_isConstructible
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F)
    (V : X.affineOpens) :
    IsFinitelyPresentable.{u + 1} ((inverseImage V.1.ι).obj F) := by
  have : IsAffine V.1.toScheme := V.property
  obtain ⟨t⟩ := hF V
  exact isFinitelyPresentable_of_isConstructible_of_isAffine _
    (isConstructible_of_partition t)

namespace FiniteCogenerators.Global

/-- A genuine constructible abelian sheaf on a Noetherian scheme embeds in
an actual finite product of finite-morphism direct images of finite constant
coefficients. The original affine compactness input is proved, not assumed. -/
def finiteConstantProductEmbeddingOfConstructible
    (X : Scheme.{u}) [IsNoetherian X] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsConstructible F) : FiniteConstantProductEmbedding F :=
  finiteConstantProductEmbeddingOfIsNoetherian X F hF
    (Proper.affineRestriction_isFinitelyPresentable_spec_open F
      (affineRestriction_isFinitelyPresentable_of_isConstructible F hF))

end FiniteCogenerators.Global
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
