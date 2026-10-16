/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine.Postnikov
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Locality.Derived
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Original derived flat base change over arbitrary bases

The original derived mate is invertible for qcqs direct image, flat change
of base and bounded-below coefficients with quasicoherent homology. An
affine refinement of the pulled-back target cover reduces the statement
to the actual affine theorem. Both reductions use the original derived
pasting equation and native open-cover reflection.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Retain the installed standard derived categories of actual module sheaves. -/
local instance generalDerivedBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

private theorem derivedFlatBaseChangeMap_isIso_congr
    {W U V X : Scheme.{u}} (a₁ a₂ : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
    (j₁ j₂ : V ⟶ X) [Flat j₁] [Flat j₂] (ha : a₁ = a₂) (hj : j₁ = j₂)
    (h₁ : IsPullback a₁ b f j₁) (h₂ : IsPullback a₂ b f j₂)
    (K : DerivedCategory.Plus U.Modules) :
    IsIso ((derivedFlatBaseChangeMap a₁ b f j₁ h₁).app K) ↔
      IsIso ((derivedFlatBaseChangeMap a₂ b f j₂ h₂).app K) := by
  subst a₂
  subst j₂
  rfl

private theorem flatPullback_homology_isQuasicoherent
    {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p]
    (K : DerivedCategory.Plus X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor Y.Modules i).obj
      ((derivedFlatPullbackPlus p).obj K)).IsQuasicoherent := by
  let : ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent := hK i
  have hq : ((pullback p).obj
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K)).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((pullback p).rightDerivedFunctorPlusHomologyIso i).app K).symm hq

/-- The original derived flat base-change map is invertible over arbitrary schemes for qcqs
morphisms and every bounded-below coefficient with quasicoherent original homology sheaves. -/
theorem derivedFlatBaseChangeMap_isIso_of_quasicoherent_homology
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus U.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.Plus.homologyFunctor U.Modules i).obj K).IsQuasicoherent) :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let 𝒰 := X.affineOpenCover
  let 𝒱 : V.OpenCover := 𝒰.openCover.pullback₁ j
  let 𝒮 : V.AffineOpenCover := Scheme.OpenCover.affineRefinement 𝒱
  let t := Scheme.OpenCover.fromAffineRefinement 𝒱
  apply isIso_of_derivedOpenPullback_openCover (fun i : 𝒮.I₀ => Spec (𝒮.X i)) 𝒮.f
    (fun x => ⟨𝒮.openCover.idx x, 𝒮.openCover.covers x⟩)
  intro i
  let i₀ := t.s₀ i
  let j₀ : Spec (𝒰.X i₀) ⟶ X := 𝒰.f i₀
  let v : Spec (𝒮.X i) ⟶ V := 𝒮.f i
  let r : Spec (𝒮.X i) ⟶ Spec (𝒰.X i₀) := t.h₀ i ≫ 𝒰.openCover.pullbackHom j i₀
  have hr : r ≫ j₀ = v ≫ j := by
    dsimp only [r, j₀, v]
    erw [Category.assoc, Scheme.Cover.pullbackHom_map, ← Category.assoc, t.w₀]
  change IsIso ((derivedFlatPullbackPlus v).map
    ((derivedFlatBaseChangeMap a b f j h).app K))
  let : IsOpenImmersion j₀ := inferInstanceAs (IsOpenImmersion (𝒰.f i₀))
  let : IsOpenImmersion v := inferInstanceAs (IsOpenImmersion (𝒮.f i))
  let : Flat (𝒰.openCover.pullbackHom j i₀) := by
    change Flat (pullback.snd j (𝒰.f i₀))
    infer_instance
  let : Flat r := inferInstance
  let a₀ := pullback.fst f j₀
  let f₀ := pullback.snd f j₀
  let h₀ := IsPullback.of_hasPullback f j₀
  let c := pullback.fst b v
  let d := pullback.snd b v
  let hV := IsPullback.of_hasPullback b v
  let H := hV.paste_horiz h
  have HU : IsPullback (c ≫ a) d f (r ≫ j₀) := by
    simpa only [hr] using H
  let e := h₀.lift (c ≫ a) (d ≫ r) (by simpa only [Category.assoc] using HU.w)
  have he : e ≫ a₀ = c ≫ a := h₀.lift_fst _ _ _
  have hlocal : IsPullback e d f₀ r := HU.of_right' h₀
  let Hlocal := hlocal.paste_horiz h₀
  let : Flat e := flat_cartesian_baseChange e d f₀ r hlocal
  let : QuasiCompact f₀ := inferInstanceAs (QuasiCompact (pullback.snd f j₀))
  let : QuasiSeparated f₀ := inferInstanceAs (QuasiSeparated (pullback.snd f j₀))
  let K₀ := (derivedFlatPullbackPlus a₀).obj K
  have hK₀ (n : ℤ) :
      ((DerivedCategory.Plus.homologyFunctor (Limits.pullback f j₀).Modules n).obj
        K₀).IsQuasicoherent :=
    flatPullback_homology_isQuasicoherent a₀ K hK n
  let φ := Spec.preimage r
  have hφ : Spec.map φ = r := Spec.map_preimage r
  have hφflat : φ.hom.Flat := Flat.SpecMap_iff.mp (by simpa only [hφ] using ‹Flat r›)
  have hlocal' : IsPullback e d f₀ (Spec.map φ) := by simpa only [hφ] using hlocal
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφflat
  have hlocalIso : IsIso ((derivedFlatBaseChangeMap e d f₀ r hlocal).app K₀) :=
    (derivedFlatBaseChangeMap_isIso_congr e e d f₀ (Spec.map φ) r rfl hφ
      hlocal' hlocal K₀).mp
        (derivedFlatBaseChangeMap_isIso_of_spec e d f₀ φ hlocal' hφflat K₀ hK₀)
  let := hlocalIso
  let : IsIso (derivedFlatBaseChangeMap a₀ f₀ f j₀ h₀) :=
    isIso_derivedFlatBaseChangeMap_of_isOpenImmersion a₀ f₀ f j₀ h₀
  have hcomp := derivedFlatBaseChangeMap_comp a₀ f₀ f j₀ h₀ e d r hlocal Hlocal K
  have houter : IsIso ((derivedFlatBaseChangeMap (e ≫ a₀) d f (r ≫ j₀) Hlocal).app K) := by
    have : IsIso ((derivedFlatPullbackPlusCompIso r j₀).hom.app
        ((derivedPushforwardPlus f).obj K) ≫
      (derivedFlatBaseChangeMap (e ≫ a₀) d f (r ≫ j₀) Hlocal).app K) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((derivedFlatPullbackPlusCompIso r j₀).hom.app ((derivedPushforwardPlus f).obj K)) _
  let : IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H).app K) :=
    (derivedFlatBaseChangeMap_isIso_congr (e ≫ a₀) (c ≫ a) d f (r ≫ j₀) (v ≫ j)
      he hr Hlocal H K).mp houter
  let : IsIso (derivedFlatBaseChangeMap c d b v hV) :=
    isIso_derivedFlatBaseChangeMap_of_isOpenImmersion c d b v hV
  have hcomp' := derivedFlatBaseChangeMap_comp a b f j h c d v hV H K
  have hfull : IsIso ((derivedFlatPullbackPlus v).map
        ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b v hV).app ((derivedFlatPullbackPlus a).obj K) ≫
      (derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K)) := by
    rw [← hcomp']
    infer_instance
  let : IsIso (((derivedFlatPullbackPlus v).map
        ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b v hV).app ((derivedFlatPullbackPlus a).obj K)) ≫
      (derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K)) := by
    simpa only [Category.assoc] using hfull
  let : IsIso ((derivedFlatPullbackPlus v).map
        ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b v hV).app ((derivedFlatPullbackPlus a).obj K)) :=
    IsIso.of_isIso_comp_right _
      ((derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K))
  exact IsIso.of_isIso_comp_right _
    ((derivedFlatBaseChangeMap c d b v hV).app ((derivedFlatPullbackPlus a).obj K))

end AlgebraicGeometry.Scheme.Modules
