/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCover
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.HomLocality

/-! # Uniqueness of the actual nonflat comparison from its affine formula

The prescribed original affine arrows determine at most one global morphism.
This is the uniqueness part only; the separate overlap argument is needed
to construct a morphism satisfying the normalization.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The actual global arrow has the prescribed original map on every affine chart pair. -/
def IsNormalized
    (β : (pullback g).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj ((pullback a).obj M)) : Prop :=
  ∀ C : AffineBaseChangeChart g,
    (restrictFunctor C.target).map β =
      chartMap a b f g h C.source C.target C.scalar C.comm n M

/-- The exact affine formula determines the actual global nonflat comparison uniquely. -/
theorem IsNormalized.hom_ext
    {β γ : (pullback g).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj ((pullback a).obj M)}
    (hβ : IsNormalized a b f g h n M β) (hγ : IsNormalized a b f g h n M γ) : β = γ := by
  apply hom_ext_of_restrict_jointlySurjective
    (fun C : AffineBaseChangeChart g => Spec C.targetRing) (fun C => C.target)
    (affineBaseChangeCharts_cover g) β γ
  intro C
  exact (hβ C).trans (hγ C).symm

end AlgebraicGeometry.Scheme.Modules.Nonflat
