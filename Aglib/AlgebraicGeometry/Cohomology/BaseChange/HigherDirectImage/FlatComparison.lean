/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Affine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Composition
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Open
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartAdjoint

/-!
# Agreement with the original flat higher-image comparison

The original flat comparison has the original geometric affine formula on
every pair of open charts. Pasting its native base-change maps in the two
orders gives the restriction formula. The original restricted coefficient
is the mate of the native pullback/open-square isomorphism, so the checked
affine normalization applies without changing the coefficient. Uniqueness
of the global nonflat comparison then identifies the two actual arrows.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

section OpenNormalization

variable {W U V X W₀ U₀ V₀ X₀ : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [Flat g]
  (j : X₀ ⟶ X) (v : V₀ ⟶ V) (s : V₀ ⟶ X₀)
  [IsOpenImmersion j] [IsOpenImmersion v] [Flat s]
  (hv : s ≫ j = v ≫ g)
  (p : U₀ ⟶ U) (d : U₀ ⟶ X₀) [IsOpenImmersion p]
  (hU : IsPullback p d f j)
  (c : W₀ ⟶ W) (e : W₀ ⟶ V₀) [IsOpenImmersion c]
  (hW : IsPullback c e b v)
  (q : W₀ ⟶ U₀) (hq : IsPullback q e d s)
  (hqU : q ≫ p = c ≫ a) (M : U.Modules) (n : ℕ)

/-- Pasting in the two orders retains the native open-square comparisons.
This identity uses arbitrary coefficients and no quasicoherence hypothesis. -/
private theorem flatComparison_openNormalization :
    (restrictFunctor v).map
        ((higherDirectImageFlatBaseChangeMap a b f g h n).app M) ≫
      (higherDirectImageOpenRestrictionIso c e b v hW n).hom.app
        ((pullback a).obj M) =
    (pullbackOpenSquare v s g j hv.symm).hom.app
        (((pushforward f).rightDerived n).obj M) ≫
      (pullback s).map
        ((higherDirectImageOpenRestrictionIso p d f j hU n).hom.app M) ≫
      (higherDirectImageFlatBaseChangeMap q e d s hq n).app (M.restrict p) ≫
      ((pushforward e).rightDerived n).map
        ((pullbackOpenSquare c q a p hqU.symm).inv.app M) := by
  let P := (pushforward f).rightDerived n
  let B := (pushforward b).rightDerived n
  let D := (pushforward d).rightDerived n
  let E := (pushforward e).rightDerived n
  let N := (pullback a).obj M
  let vE := restrictFunctorIsoPullback v
  let jE := restrictFunctorIsoPullback j
  let pE := restrictFunctorIsoPullback p
  let cE := restrictFunctorIsoPullback c
  let cv := pullbackComp v g
  let cs := pullbackComp s j
  let eb := pullbackCongr hv.symm
  let ea := pullbackCongr hqU.symm
  let Aopen := higherDirectImageOpenRestrictionIso p d f j hU n
  let Bopen := higherDirectImageOpenRestrictionIso c e b v hW n
  let OT := pullbackOpenSquare v s g j hv.symm
  let OS := pullbackOpenSquare c q a p hqU.symm
  let kg := (higherDirectImageFlatBaseChangeMap a b f g h n).app M
  let kp := (higherDirectImageFlatBaseChangeMap p d f j hU n).app M
  let kc := (higherDirectImageFlatBaseChangeMap c e b v hW n).app N
  let kq := (higherDirectImageFlatBaseChangeMap q e d s hq n).app ((pullback p).obj M)
  let kqr := (higherDirectImageFlatBaseChangeMap q e d s hq n).app (M.restrict p)
  let H := hW.paste_horiz h
  let H' := hq.paste_horiz hU
  let ko := (higherDirectImageFlatBaseChangeMap (c ≫ a) e f (v ≫ g) H n).app M
  let ko' := (higherDirectImageFlatBaseChangeMap (q ≫ p) e f (s ≫ j) H' n).app M
  let tail := cE.hom.app N ≫ (pullbackComp c a).hom.app M ≫ ea.hom.app M
  let tail' := (pullback q).map (pE.hom.app M) ≫ (pullbackComp q p).hom.app M
  have htail : OS.inv.app M ≫ tail = tail' := by
    dsimp only [OS, tail, tail', cE, pE, ea, N, pullbackOpenSquare,
      Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have htarget : OT.hom.app (P.obj M) ≫
      (pullback s).map (jE.hom.app (P.obj M)) ≫ cs.hom.app (P.obj M) =
      vE.hom.app ((pullback g).obj (P.obj M)) ≫ cv.hom.app (P.obj M) ≫
        eb.hom.app (P.obj M) := by
    dsimp only [OT, P, jE, vE, cs, cv, eb, pullbackOpenSquare,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
  have hc1 := higherDirectImageFlatBaseChangeMap_comp
    a b f g h c e v hW H M n
  change cv.hom.app (P.obj M) ≫ ko =
    (pullback v).map kg ≫ kc ≫ E.map ((pullbackComp c a).hom.app M) at hc1
  have hc2 := higherDirectImageFlatBaseChangeMap_comp
    p d f j hU q e s hq H' M n
  change cs.hom.app (P.obj M) ≫ ko' =
    (pullback s).map kp ≫ kq ≫ E.map ((pullbackComp q p).hom.app M) at hc2
  have hcong := higherDirectImageFlatBaseChangeMap_congr
    (c ≫ a) (q ≫ p) e f (v ≫ g) (s ≫ j) H H'
    hqU.symm hv.symm M n
  change eb.hom.app (P.obj M) ≫ ko' = ko ≫ E.map (ea.hom.app M) at hcong
  have hp := higherDirectImageFlatBaseChangeMap_eq_openRestriction p d f j hU n M
  change kp = jE.inv.app (P.obj M) ≫ Aopen.hom.app M ≫
    D.map (pE.hom.app M) at hp
  have hp' : jE.hom.app (P.obj M) ≫ kp =
      Aopen.hom.app M ≫ D.map (pE.hom.app M) := by
    rw [hp]
    simp only [Iso.hom_inv_id_app_assoc]
  have hc := higherDirectImageFlatBaseChangeMap_eq_openRestriction c e b v hW n N
  change kc = vE.inv.app (B.obj N) ≫ Bopen.hom.app N ≫
    E.map (cE.hom.app N) at hc
  have hqNat := (higherDirectImageFlatBaseChangeMap q e d s hq n).naturality
    (pE.hom.app M)
  change (pullback s).map (D.map (pE.hom.app M)) ≫ kq =
    kqr ≫ E.map ((pullback q).map (pE.hom.app M)) at hqNat
  have hvNat := vE.hom.naturality kg
  change (restrictFunctor v).map kg ≫ vE.hom.app (B.obj N) =
    vE.hom.app ((pullback g).obj (P.obj M)) ≫ (pullback v).map kg at hvNat
  have hleft : vE.hom.app ((pullback g).obj (P.obj M)) ≫ cv.hom.app (P.obj M) ≫
      eb.hom.app (P.obj M) ≫ ko' =
      (restrictFunctor v).map kg ≫ Bopen.hom.app N ≫ E.map tail := by
    calc
      _ = vE.hom.app ((pullback g).obj (P.obj M)) ≫ cv.hom.app (P.obj M) ≫
          ko ≫ E.map (ea.hom.app M) := by rw [hcong]
      _ = vE.hom.app ((pullback g).obj (P.obj M)) ≫ (pullback v).map kg ≫
          kc ≫ E.map ((pullbackComp c a).hom.app M) ≫ E.map (ea.hom.app M) := by
        rw [← Category.assoc (cv.hom.app (P.obj M)) ko, hc1]
        simp only [Category.assoc]
      _ = (restrictFunctor v).map kg ≫ vE.hom.app (B.obj N) ≫ kc ≫
          E.map ((pullbackComp c a).hom.app M) ≫ E.map (ea.hom.app M) := by
        rw [← Category.assoc (vE.hom.app ((pullback g).obj (P.obj M)))
          ((pullback v).map kg), ← hvNat]
        simp only [Category.assoc]
      _ = _ := by
        rw [hc]
        simp only [tail, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hright : OT.hom.app (P.obj M) ≫ (pullback s).map (Aopen.hom.app M) ≫
      kqr ≫ E.map tail' =
      vE.hom.app ((pullback g).obj (P.obj M)) ≫ cv.hom.app (P.obj M) ≫
        eb.hom.app (P.obj M) ≫ ko' := by
    calc
      _ = OT.hom.app (P.obj M) ≫ (pullback s).map (Aopen.hom.app M) ≫
          (pullback s).map (D.map (pE.hom.app M)) ≫ kq ≫
            E.map ((pullbackComp q p).hom.app M) := by
        dsimp only [tail']
        rw [Functor.map_comp, ← Category.assoc kqr
          (E.map ((pullback q).map (pE.hom.app M))), ← hqNat]
        simp only [Category.assoc]
      _ = OT.hom.app (P.obj M) ≫ (pullback s).map (jE.hom.app (P.obj M)) ≫
          (pullback s).map kp ≫ kq ≫ E.map ((pullbackComp q p).hom.app M) := by
        rw [← Functor.map_comp_assoc, ← hp', Functor.map_comp]
        simp only [Category.assoc]
      _ = OT.hom.app (P.obj M) ≫ (pullback s).map (jE.hom.app (P.obj M)) ≫
          cs.hom.app (P.obj M) ≫ ko' := by rw [hc2]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ ko') htarget
  let : IsIso tail := by dsimp only [tail]; infer_instance
  apply (cancel_mono (E.map tail)).mp
  change ((restrictFunctor v).map kg ≫ Bopen.hom.app N) ≫ E.map tail =
    (OT.hom.app (P.obj M) ≫ (pullback s).map (Aopen.hom.app M) ≫
      kqr ≫ E.map (OS.inv.app M)) ≫ E.map tail
  calc
    _ = vE.hom.app ((pullback g).obj (P.obj M)) ≫ cv.hom.app (P.obj M) ≫
        eb.hom.app (P.obj M) ≫ ko' := by
      simpa only [Category.assoc] using hleft.symm
    _ = OT.hom.app (P.obj M) ≫ (pullback s).map (Aopen.hom.app M) ≫
        kqr ≫ E.map tail' := hright.symm
    _ = _ := by simp only [Category.assoc, ← Functor.map_comp, htail]

end OpenNormalization

section AffineNormalization

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The original flat higher-image map has the unchanged geometric affine
normalization on every actual chart pair. -/
private theorem flatComparison_chart
    (C : Nonflat.AffineBaseChangeChart g) :
    (restrictFunctor C.target).map
        ((higherDirectImageFlatBaseChangeMap a b f g h n).app M) =
      Nonflat.chartMap a b f g h C.source C.target C.scalar C.comm n M := by
  let j := C.source
  let v := C.target
  let s := Spec.map C.scalar
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := Nonflat.chartUpper a b f g h j v C.scalar C.comm
  let hU := IsPullback.of_hasPullback f j
  let hW := IsPullback.of_hasPullback b v
  let hq := Nonflat.chartUpper_isPullback a b f g h j v C.scalar C.comm
  have hqU := Nonflat.chartUpper_fst a b f g h j v C.scalar C.comm
  have hqB := Nonflat.chartUpper_snd a b f g h j v C.scalar C.comm
  let : Flat s := MorphismProperty.of_postcomp (W' := @IsOpenImmersion)
    @Flat s j inferInstance (by
    change Flat (Spec.map C.scalar ≫ C.source)
    rw [C.comm]
    infer_instance)
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback hU inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback hU inferInstance
  let : QuasiCompact e := MorphismProperty.of_isPullback hW inferInstance
  let : QuasiSeparated e := MorphismProperty.of_isPullback hW inferInstance
  let N := (pullback a).obj M
  let OS := pullbackOpenSquare c q a p hqU.symm
  let ψ := Nonflat.chartCoefficient a p c q hqU
    ((pullbackPushforwardAdjunction a).unit.app M)
  let ψ₀ := (pullbackPushforwardAdjunction q).unit.app (M.restrict p)
  have hψ : ψ₀ ≫ (pushforward q).map (OS.inv.app M) = ψ := by
    have he := Nonflat.chartCoefficient_pullbackUnit_adjoint a p c q hqU M
    have he' := congrArg ((pullbackPushforwardAdjunction q).homEquiv _ _) he
    simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.id_obj] at he'
    change ψ = ψ₀ ≫ (pushforward q).map (OS.inv.app M) at he'
    exact he'.symm
  have hn := higherDirectImageAffineMap_naturality
    (M := M.restrict p) (M' := M.restrict p)
    (N := (pullback q).obj (M.restrict p)) (N' := N.restrict c) q e d C.scalar hqB
    ψ₀ ψ (𝟙 (M.restrict p)) (OS.inv.app M)
    (by simpa only [Category.id_comp] using hψ.symm) n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hf := flatComparison_openNormalization a b f g h j v s C.comm
    p d hU c e hW q hq hqU M n
  have hAffine := higherDirectImageFlatBaseChangeMap_app_eq_affineMap
    q e d C.scalar hq (M.restrict p) n
  apply (cancel_mono
    ((higherDirectImageOpenRestrictionIso c e b v hW n).hom.app N)).mp
  change (restrictFunctor v).map
      ((higherDirectImageFlatBaseChangeMap a b f g h n).app M) ≫
      (higherDirectImageOpenRestrictionIso c e b v hW n).hom.app N =
    Nonflat.localMap a b f g h j v C.scalar C.comm n M
      p d hU c e hW q hqU hqB ≫
      (higherDirectImageOpenRestrictionIso c e b v hW n).hom.app N
  dsimp only [Nonflat.localMap, N]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [hf, hAffine, ← hn]

/-- The original flat comparison satisfies the same original affine formula
as the canonical nonflat comparison, without additional geometric hypotheses. -/
theorem higherDirectImageFlatBaseChangeMap_isNormalized :
    Nonflat.IsNormalized a b f g h n M
      ((higherDirectImageFlatBaseChangeMap a b f g h n).app M) :=
  flatComparison_chart a b f g h n M

/-- For flat change of base, the canonical nonflat higher-image comparison is
the original native flat higher-image map, with its original cartesian square,
pullback unit, and coefficient module. -/
theorem higherDirectImageFlatBaseChangeMap_eq_baseChangeMap :
    (higherDirectImageFlatBaseChangeMap a b f g h n).app M =
      higherDirectImageBaseChangeMap a b f g h n M :=
  higherDirectImageBaseChangeMap_unique a b f g h n M _
    (higherDirectImageFlatBaseChangeMap_isNormalized a b f g h n M)

end AffineNormalization

end AlgebraicGeometry.Scheme.Modules
