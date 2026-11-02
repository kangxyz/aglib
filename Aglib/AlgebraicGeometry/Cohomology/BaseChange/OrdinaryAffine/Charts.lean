/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartGeometry
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCover
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Original ordinary base-change descent along affine chart pairs

The original chart projection, open base-change isomorphisms and pasting law
identify restriction of the original global mate with each original affine
cartesian mate. This complete descent needs no higher-image comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual ordinary cartesian mate on the original affine chart pair. -/
abbrev ordinaryAffineChartMate {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (M : X.Modules) (C : Nonflat.AffineBaseChangeChart g) :=
  let a := Limits.pullback.fst f g
  let b := Limits.pullback.snd f g
  let h := IsPullback.of_hasPullback f g
  let e := Nonflat.chartUpper a b f g h C.source C.target C.scalar C.comm
  (cartesianBaseChangeMap e (Limits.pullback.snd b C.target)
    (Limits.pullback.snd f C.source) (Spec.map C.scalar)
    (Nonflat.chartUpper_isPullback a b f g h C.source C.target C.scalar C.comm)).app
      ((pullback (Limits.pullback.fst f C.source)).obj M)

/-- Invertibility on all original affine chart mates descends to the original global mate. -/
theorem moduleBaseChangeMap_isIso_of_affine_chart_mates
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (M : X.Modules)
    (hβ : ∀ C : Nonflat.AffineBaseChangeChart g, IsIso (ordinaryAffineChartMate f g M C)) :
    IsIso (moduleBaseChangeMap f g M) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap]
  let a := Limits.pullback.fst f g
  let b := Limits.pullback.snd f g
  let h := IsPullback.of_hasPullback f g
  change IsIso ((cartesianBaseChangeMap a b f g h).app M)
  apply isIso_of_restrict_openCover
    (fun C : Nonflat.AffineBaseChangeChart g => Spec C.targetRing)
    (fun C => C.target) (Nonflat.affineBaseChangeCharts_cover g)
  intro C
  let j := C.source
  let v := C.target
  let s := Spec.map C.scalar
  let aU := Limits.pullback.fst f j
  let bU := Limits.pullback.snd f j
  let hU := IsPullback.of_hasPullback f j
  let c := Limits.pullback.fst b v
  let d := Limits.pullback.snd b v
  let hV := IsPullback.of_hasPullback b v
  let e := Nonflat.chartUpper a b f g h j v C.scalar C.comm
  have he : e ≫ aU = c ≫ a := Nonflat.chartUpper_fst a b f g h j v C.scalar C.comm
  have hlocal : IsPullback e d bU s :=
    Nonflat.chartUpper_isPullback a b f g h j v C.scalar C.comm
  let Hlocal := hlocal.paste_horiz hU
  let H := hV.paste_horiz h
  let N := (pullback aU).obj M
  let : IsIso ((cartesianBaseChangeMap aU bU f j hU).app M) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion aU bU f j hU M
  let : IsIso ((cartesianBaseChangeMap e d bU s hlocal).app N) :=
    hβ C
  have hcomp := cartesianBaseChangeMap_comp aU bU f j hU e d s hlocal Hlocal M
  have houter : IsIso ((cartesianBaseChangeMap (e ≫ aU) d f (s ≫ j) Hlocal).app M) := by
    have : IsIso ((pullbackComp s j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (e ≫ aU) d f (s ≫ j) Hlocal).app M) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left ((pullbackComp s j).hom.app ((pushforward f).obj M)) _
  have htransport (a₁ a₂ : Limits.pullback b v ⟶ X) (g₁ g₂ : Spec C.targetRing ⟶ S)
      (ha : a₁ = a₂) (hg : g₁ = g₂)
      (H₁ : IsPullback a₁ d f g₁) (H₂ : IsPullback a₂ d f g₂) :
      IsIso ((cartesianBaseChangeMap a₁ d f g₁ H₁).app M) ↔
        IsIso ((cartesianBaseChangeMap a₂ d f g₂ H₂).app M) := by
    subst a₂
    subst g₂
    rfl
  have houter' : IsIso ((cartesianBaseChangeMap (c ≫ a) d f (v ≫ g) H).app M) :=
    (htransport (e ≫ aU) (c ≫ a) (s ≫ j) (v ≫ g) he C.comm Hlocal H).mp houter
  let : IsIso ((cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion c d b v hV ((pullback a).obj M)
  have hcomp' := cartesianBaseChangeMap_comp a b f g h c d v hV H M
  have : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M) ≫
      (cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M) ≫
      (pushforward d).map ((pullbackComp c a).hom.app M)) := by
    rw [← hcomp']
    infer_instance
  have : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M) ≫
      (cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M)) :=
    IsIso.of_isIso_comp_right _ ((pushforward d).map ((pullbackComp c a).hom.app M))
  have hp : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M)) :=
    IsIso.of_isIso_comp_right _ ((cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M))
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback v)
    ((cartesianBaseChangeMap a b f g h).app M)).mpr hp


end AlgebraicGeometry.Scheme.Modules
