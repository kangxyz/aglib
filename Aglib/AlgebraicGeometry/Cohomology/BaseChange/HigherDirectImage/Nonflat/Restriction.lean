/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Presentation

/-! # Restricting the canonical comparison on actual cartesian charts

The original affine restriction formula holds for every supplied cartesian
presentation of the chart sources, through the original higher-image open
comparisons. No choice of a fibre-product isomorphism replaces the map identity.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine pair of open charts, the canonical comparison has the original local
formula for every actual cartesian presentation of the source charts. -/
theorem higherDirectImageBaseChangeMap_restrict_affine
    {W U V X U₀ W₀ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]
    (p : U₀ ⟶ U) (d : U₀ ⟶ Spec R) [IsOpenImmersion p]
    (hU : IsPullback p d f j)
    (c : W₀ ⟶ W) (e : W₀ ⟶ Spec S) [IsOpenImmersion c]
    (hW : IsPullback c e b v)
    (q : W₀ ⟶ U₀) (hq : q ≫ p = c ≫ a) (hb : q ≫ d = e ≫ Spec.map σ) :
    (restrictFunctor v).map (higherDirectImageBaseChangeMap a b f g h n M) =
      Nonflat.localMap a b f g h j v σ hv n M p d hU c e hW q hq hb := by
  let C : Nonflat.AffineBaseChangeChart g :=
    { sourceRing := R
      targetRing := S
      source := j
      target := v
      scalar := σ
      source_open := inferInstance
      target_open := inferInstance
      comm := hv }
  exact (higherDirectImageBaseChangeMap_chart a b f g h n M C).trans
    (Nonflat.localMap_eq_chartMap a b f g h j v σ hv n M p d hU c e hW q hq hb).symm

end AlgebraicGeometry.Scheme.Modules
