/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.HomLocality

/-! # Coefficient naturality of the canonical nonflat comparison

The actual affine coefficient squares detect the global coefficient square
through the original module-Hom sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical nonflat comparison is natural in quasicoherent coefficients, with the
original higher-image and geometric pullback coefficient maps on all four sides. -/
@[reassoc]
theorem higherDirectImageBaseChangeMap_naturality
    {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) {M N : U.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (μ : M ⟶ N) :
    (pullback g).map (((pushforward f).rightDerived n).map μ) ≫
      higherDirectImageBaseChangeMap a b f g h n N =
        higherDirectImageBaseChangeMap a b f g h n M ≫
          ((pushforward b).rightDerived n).map ((pullback a).map μ) := by
  apply Nonflat.hom_ext_of_restrict_jointlySurjective
    (fun C : Nonflat.AffineBaseChangeChart g => Spec C.targetRing) (fun C => C.target)
    (Nonflat.affineBaseChangeCharts_cover g)
  intro C
  simp only [Functor.map_comp, higherDirectImageBaseChangeMap_chart]
  exact Nonflat.chartMap_naturality a b f g h C.source C.target C.scalar C.comm n μ

end AlgebraicGeometry.Scheme.Modules
