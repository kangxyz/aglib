/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianPasting
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeSourceIso

/-! # Universal Cartesian source maps through the original source transport -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Hom.DenseCompactification

universe u
variable {X X₁ X₂ S T U : Scheme.{u}}
  (f : X ⟶ S) (f₁ : X₁ ⟶ T) (f₂ : X₂ ⟶ U)
  (b : T ⟶ S) (c : U ⟶ T) (a : X₁ ⟶ X) (d : X₂ ⟶ X₁)
  (sq₁ : IsPullback a f₁ f b) (sq₂ : IsPullback d f₂ f₁ c)

/-- The pulled-back universal map is the original compactification source transport. -/
theorem cartesianPresentationPullbackIso_eq_sourceIso :
    cartesianPresentationPullbackIso f f₁ b c a sq₁ =
      pullbackSourceIso f₁ sq₁.flip.isoPullback sq₁.flip.isoPullback_hom_fst c := rfl

/-- The pasted universal source isomorphism retains both given Cartesian sources,
the original source-base-change transport, and the native pullback associator. -/
theorem cartesianPresentation_isoPullback_pasting_sourceIso :
    (sq₂.paste_horiz sq₁).flip.isoPullback =
      (sq₂.flip.isoPullback ≪≫
        pullbackSourceIso f₁ sq₁.flip.isoPullback sq₁.flip.isoPullback_hom_fst c) ≪≫
          iteratedSourceIso (f := f) b c := by
  simpa only [cartesianPresentationPullbackIso_eq_sourceIso, iteratedSourceIso,
    Iso.trans_assoc] using cartesianPresentation_isoPullback_pasting f f₁ f₂ b c a d sq₁ sq₂

end AlgebraicGeometry.Scheme.EtaleCohomology
