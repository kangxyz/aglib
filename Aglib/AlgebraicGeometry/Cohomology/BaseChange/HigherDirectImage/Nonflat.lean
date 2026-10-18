/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Matching
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Uniqueness

/-! # The canonical nonflat higher-direct-image comparison

For a qcqs morphism and quasicoherent coefficients, the actual geometric affine
cohomology mates agree on common affine refinements. The original module-Hom
sheaf glues these arrows to a canonical sheaf comparison after arbitrary base
change. The constructor has no flatness, finiteness, or supplied compatibility
premise. Its restriction to every affine chart pair is the original local map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The canonical comparison for the actual higher direct images after arbitrary base
change. Its affine geometric normalization and overlap compatibility are constructed
internally; no flatness or supplied descent data is required. -/
def higherDirectImageBaseChangeMap :
    (pullback g).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj ((pullback a).obj M) :=
  InternalHom.glueRestrictionHom
    (fun C : Nonflat.AffineBaseChangeChart g => Spec C.targetRing) (fun C => C.target)
    (Nonflat.affineBaseChangeCharts_cover g) _ _
    (fun C => Nonflat.chartMap a b f g h C.source C.target C.scalar C.comm n M)
    (Nonflat.chartMap_compatible a b f g h n M)

/-- On every affine chart pair, the canonical global comparison is exactly the original
affine geometric cohomology mate through the native open-restriction comparisons. -/
theorem higherDirectImageBaseChangeMap_chart (C : Nonflat.AffineBaseChangeChart g) :
    (restrictFunctor C.target).map (higherDirectImageBaseChangeMap a b f g h n M) =
      Nonflat.chartMap a b f g h C.source C.target C.scalar C.comm n M :=
  InternalHom.glueRestrictionHom_restrict
    (fun C : Nonflat.AffineBaseChangeChart g => Spec C.targetRing) (fun C => C.target)
    (Nonflat.affineBaseChangeCharts_cover g) _ _ _
    (Nonflat.chartMap_compatible a b f g h n M) C

/-- The canonical comparison satisfies the original affine normalization on all charts. -/
theorem higherDirectImageBaseChangeMap_isNormalized :
    Nonflat.IsNormalized a b f g h n M (higherDirectImageBaseChangeMap a b f g h n M) :=
  higherDirectImageBaseChangeMap_chart a b f g h n M

/-- The original affine formula uniquely determines the global comparison. -/
theorem higherDirectImageBaseChangeMap_unique
    (β : (pullback g).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj ((pullback a).obj M))
    (hβ : Nonflat.IsNormalized a b f g h n M β) :
    β = higherDirectImageBaseChangeMap a b f g h n M :=
  Nonflat.IsNormalized.hom_ext a b f g h n M hβ
    (higherDirectImageBaseChangeMap_isNormalized a b f g h n M)

end AlgebraicGeometry.Scheme.Modules
