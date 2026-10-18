/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficientNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.RefinementPasting

/-! # Coefficient naturality of the actual chart comparison

The local affine comparison, original chart coefficient, and native open
comparison isomorphisms preserve the same coefficient square.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

set_option maxRecDepth 2000 in
-- The specialization carries the original four module functors and coefficient presentations.
/-- Every actual affine chart arrow is natural in its original quasicoherent coefficient. -/
theorem chartMap_naturality
    {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
    (n : ℕ) {M M' : U.Modules} [M.IsQuasicoherent] [M'.IsQuasicoherent] (μ : M ⟶ M') :
    (restrictFunctor v).map ((pullback g).map (((pushforward f).rightDerived n).map μ)) ≫
      chartMap a b f g h j v σ hv n M' =
        chartMap a b f g h j v σ hv n M ≫
          (restrictFunctor v).map
            (((pushforward b).rightDerived n).map ((pullback a).map μ)) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := chartUpper a b f g h j v σ hv
  let ν := (pullback a).map μ
  let μ₀ := (restrictFunctor p).map μ
  let ν₀ := (restrictFunctor c).map ν
  let ψ := chartCoefficient a p c q (chartUpper_fst a b f g h j v σ hv)
    ((pullbackPushforwardAdjunction a).unit.app M)
  let ψ' := chartCoefficient a p c q (chartUpper_fst a b f g h j v σ hv)
    ((pullbackPushforwardAdjunction a).unit.app M')
  let P := pullback (Spec.map σ)
  let O := pullbackOpenSquare v (Spec.map σ) g j hv.symm
  let A := higherDirectImageOpenRestrictionIso p d f j (IsPullback.of_hasPullback f j) n
  let B := higherDirectImageOpenRestrictionIso c e b v (IsPullback.of_hasPullback b v) n
  have hψ : μ₀ ≫ ψ' = ψ ≫ (pushforward q).map ν₀ :=
    chartCoefficient_naturality a p c q (chartUpper_fst a b f g h j v σ hv)
      ((pullbackPushforwardAdjunction a).unit.app M)
      ((pullbackPushforwardAdjunction a).unit.app M') μ ν
      ((pullbackPushforwardAdjunction a).unit.naturality μ)
  have ho := O.hom.naturality (((pushforward f).rightDerived n).map μ)
  have ha := congrArg P.map (A.hom.naturality μ)
  simp only [Functor.map_comp] at ha
  have hc := higherDirectImageAffineMap_naturality q e d σ
    (chartUpper_snd a b f g h j v σ hv)
    (M := M.restrict p) (M' := M'.restrict p)
    (N := ((pullback a).obj M).restrict c) (N' := ((pullback a).obj M').restrict c)
    ψ ψ' μ₀ ν₀ hψ n
  have hb := B.inv.naturality ν
  have H := localComparison_naturality
    (O.hom.app (((pushforward f).rightDerived n).obj M)) (P.map (A.hom.app M))
    (higherDirectImageAffineMap (M := M.restrict p) (N := ((pullback a).obj M).restrict c)
      q e d σ (chartUpper_snd a b f g h j v σ hv) ψ n)
    (B.inv.app ((pullback a).obj M))
    (O.hom.app (((pushforward f).rightDerived n).obj M')) (P.map (A.hom.app M'))
    (higherDirectImageAffineMap (M := M'.restrict p) (N := ((pullback a).obj M').restrict c)
      q e d σ (chartUpper_snd a b f g h j v σ hv) ψ' n)
    (B.inv.app ((pullback a).obj M')) _ _ _ _ _ ho ha hc hb
  exact H

end AlgebraicGeometry.Scheme.Modules.Nonflat
