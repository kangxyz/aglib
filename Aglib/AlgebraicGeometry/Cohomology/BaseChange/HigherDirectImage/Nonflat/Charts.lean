/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Native local arrows for nonflat higher-image base change

An affine chart pair determines an actual arrow between the restrictions of
the two global sheaves. The source and target identifications are the native
pullback/open and higher-image/open comparisons. The middle arrow is the
original nonflat affine cohomology mate with its actual restricted coefficient.
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
  (h : IsPullback a b f g)
  {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
  (hv : Spec.map σ ≫ j = v ≫ g)

/-- The original induced morphism between the actual source fibre products of a chart pair. -/
def chartUpper : Limits.pullback b v ⟶ Limits.pullback f j :=
  (IsPullback.of_hasPullback f j).lift
    (Limits.pullback.fst b v ≫ a) (Limits.pullback.snd b v ≫ Spec.map σ) (by
      have H := (IsPullback.of_hasPullback b v).paste_horiz h
      simpa only [Category.assoc, hv] using H.w)

/-- The chart map retains the original source projection. -/
@[reassoc]
theorem chartUpper_fst :
    chartUpper a b f g h j v σ hv ≫ Limits.pullback.fst f j =
      Limits.pullback.fst b v ≫ a :=
  (IsPullback.of_hasPullback f j).lift_fst _ _ _

/-- The chart map retains the original target projection and scalar morphism. -/
@[reassoc]
theorem chartUpper_snd :
    chartUpper a b f g h j v σ hv ≫ Limits.pullback.snd f j =
      Limits.pullback.snd b v ≫ Spec.map σ :=
  (IsPullback.of_hasPullback f j).lift_snd _ _ _

/-- Every chart pair of the original cartesian square is cartesian, with its actual induced
source map. -/
theorem chartUpper_isPullback :
    IsPullback (chartUpper a b f g h j v σ hv) (Limits.pullback.snd b v)
      (Limits.pullback.snd f j) (Spec.map σ) := by
  have H := (IsPullback.of_hasPullback b v).paste_horiz h
  have H' : IsPullback (Limits.pullback.fst b v ≫ a) (Limits.pullback.snd b v)
      f (Spec.map σ ≫ j) := by simpa only [hv] using H
  exact H'.of_right' (IsPullback.of_hasPullback f j)

variable [QuasiCompact f] [QuasiSeparated f] [IsOpenImmersion j] [IsOpenImmersion v]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The actual local comparison on explicit cartesian chart squares. The output is a map
between restrictions of the original global sheaves, independently of the presentation of
the chart fibre products. -/
def localMap {U₀ W₀ : Scheme.{u}}
    (p : U₀ ⟶ U) (d : U₀ ⟶ Spec R) [IsOpenImmersion p]
    (hU : IsPullback p d f j)
    (c : W₀ ⟶ W) (e : W₀ ⟶ Spec S) [IsOpenImmersion c]
    (hW : IsPullback c e b v)
    (q : W₀ ⟶ U₀) (hqU : q ≫ p = c ≫ a) (hqB : q ≫ d = e ≫ Spec.map σ) :
    ((pullback g).obj (((pushforward f).rightDerived n).obj M)).restrict v ⟶
      (((pushforward b).rightDerived n).obj ((pullback a).obj M)).restrict v := by
  letI : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  letI : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  letI : QuasiCompact d := MorphismProperty.of_isPullback hU inferInstance
  letI : QuasiSeparated d := MorphismProperty.of_isPullback hU inferInstance
  letI : QuasiCompact e := MorphismProperty.of_isPullback hW inferInstance
  letI : QuasiSeparated e := MorphismProperty.of_isPullback hW inferInstance
  let N := (pullback a).obj M
  let ψ := chartCoefficient a p c q hqU
    ((pullbackPushforwardAdjunction a).unit.app M)
  exact (pullbackOpenSquare v (Spec.map σ) g j hv.symm).hom.app
      (((pushforward f).rightDerived n).obj M) ≫
    (pullback (Spec.map σ)).map
      ((higherDirectImageOpenRestrictionIso p d f j hU n).hom.app M) ≫
    higherDirectImageAffineMap (M := M.restrict p) (N := N.restrict c)
      q e d σ hqB ψ n ≫
    (higherDirectImageOpenRestrictionIso c e b v hW n).inv.app N

/-- Equal original chart projections and geometric arrows give the same actual local map;
the proofs of the cartesian and commutative-square conditions introduce no extra choice. -/
theorem localMap_congr {U₀ W₀ : Scheme.{u}}
    (p p' : U₀ ⟶ U) (d : U₀ ⟶ Spec R) [IsOpenImmersion p] [IsOpenImmersion p']
    (hU : IsPullback p d f j) (hU' : IsPullback p' d f j)
    (c c' : W₀ ⟶ W) (e : W₀ ⟶ Spec S) [IsOpenImmersion c] [IsOpenImmersion c']
    (hW : IsPullback c e b v) (hW' : IsPullback c' e b v)
    (q q' : W₀ ⟶ U₀)
    (hqU : q ≫ p = c ≫ a) (hqB : q ≫ d = e ≫ Spec.map σ)
    (hqU' : q' ≫ p' = c' ≫ a) (hqB' : q' ≫ d = e ≫ Spec.map σ)
    (hp : p = p') (hc : c = c') (hq : q = q') :
    localMap a b f g h j v σ hv n M p d hU c e hW q hqU hqB =
      localMap a b f g h j v σ hv n M p' d hU' c' e hW' q' hqU' hqB' := by
  subst p'
  subst c'
  subst q'
  rfl

/-- The actual local comparison on an affine chart pair of the original square. No
flatness assumption occurs in the middle affine scalar mate. -/
def chartMap :
    ((pullback g).obj (((pushforward f).rightDerived n).obj M)).restrict v ⟶
      (((pushforward b).rightDerived n).obj ((pullback a).obj M)).restrict v := by
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := chartUpper a b f g h j v σ hv
  exact localMap a b f g h j v σ hv n M p d (IsPullback.of_hasPullback f j)
    c e (IsPullback.of_hasPullback b v) q
    (chartUpper_fst a b f g h j v σ hv) (chartUpper_snd a b f g h j v σ hv)

end AlgebraicGeometry.Scheme.Modules.Nonflat
