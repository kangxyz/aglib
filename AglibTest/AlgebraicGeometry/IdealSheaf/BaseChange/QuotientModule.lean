/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen

/-! Focused consumer of the pullback of the structure module of a closed subscheme along an
arbitrary morphism (no flatness): the epimorphism `f^* I ⟶ I_{I.comap f}`, the image of
`f^* I ⟶ 𝒪_Y` and `f^* 𝒪_W ≅ 𝒪_{W.comap f}`, also along the base change `pullbackBaseChange` of
`P^n_A ×_{Spec A} S`, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

/-- The ideal comparison of the pulled-back closed subscheme is an epimorphism for every
morphism, with any square map. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (a : (I.comap f).subscheme ⟶ I.subscheme)
    (h : a ≫ I.subschemeι = (I.comap f).subschemeι ≫ f) :
    Epi (idealPullbackMap I.subschemeι (I.comap f).subschemeι f a h) :=
  Scheme.IdealSheafData.epi_idealPullbackMap I f a h

/-- The canonical square through Mathlib's `subschemeMap` carries the instance. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    Epi (idealPullbackMap I.subschemeι (I.comap f).subschemeι f
      (Scheme.IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f))
      (Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap f) I f (I.le_map_comap f))) :=
  inferInstance

/-- Surjectivity on sections over affine opens `V ≤ f ⁻¹ᵁ U`. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (a : (I.comap f).subscheme ⟶ I.subscheme)
    (h : a ≫ I.subschemeι = (I.comap f).subschemeι ≫ f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    Function.Surjective
      ((idealPullbackMap I.subschemeι (I.comap f).subschemeι f a h).val.app (Opposite.op V.1)) :=
  Scheme.IdealSheafData.surjective_idealPullbackMap_app I f a h U V hVU

/-- The image of `f^* I ⟶ f^* 𝒪_X ≅ 𝒪_Y` is the ideal module of `I.comap f`, compatibly with
the inclusions. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.pullbackIdealImageIso f).hom ≫ idealInclusion (I.comap f).subschemeι =
      Limits.image.ι (I.pullbackIdealToUnit f) :=
  Scheme.IdealSheafData.pullbackIdealImageIso_hom_inclusion I f

/-- The image factorisation is the composite of the epimorphism and the ideal inclusion. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    idealPullbackMap I.subschemeι (I.comap f).subschemeι f
        (Scheme.IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f))
        (Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap f) I f (I.le_map_comap f)) ≫
      idealInclusion (I.comap f).subschemeι = I.pullbackIdealToUnit f :=
  (I.pullbackIdealMonoFactorisation f).fac

/-- `f^* 𝒪_W ≅ 𝒪_{W.comap f}`, compatibly with the projections, for every `f`. -/
example {X Y : Scheme.{u}} (W : X.IdealSheafData) (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).map W.toQuotientModule ≫ (W.quotientModulePullbackIso f).hom =
      (Scheme.Modules.pullbackUnitIso f).hom ≫ (W.comap f).toQuotientModule := by
  simp

/-- The pushforward presentation `f^* i_* 𝒪_W ≅ i'_* 𝒪_{W.comap f}`, for every `f`. -/
example {X Y : Scheme.{u}} (W : X.IdealSheafData) (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward W.subschemeι).obj
        (SheafOfModules.unit W.subscheme.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (W.comap f).subschemeι).obj
        (SheafOfModules.unit (W.comap f).subscheme.ringCatSheaf) :=
  W.pushforwardUnitPullbackIso f

/-- The pullback of `𝒪_Z` to `P^n_A ×_{Spec A} T` along `pullbackBaseChange` is `𝒪_{Z_T}`, with no
flatness hypothesis, compatibly with the projections. -/
example {A : Type u} [CommRing A] (ι : Type u) {S T : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of A)) (Z : (pullback (ProjectiveSpace.toSpec A ι) s).IdealSheafData)
    (g : T ⟶ S) :
    (Scheme.Modules.pullback (ProjectiveSpace.pullbackBaseChange ι s g)).map Z.toQuotientModule ≫
        (Z.quotientModulePullbackIso (ProjectiveSpace.pullbackBaseChange ι s g)).hom =
      (Scheme.Modules.pullbackUnitIso (ProjectiveSpace.pullbackBaseChange ι s g)).hom ≫
        (Z.comap (ProjectiveSpace.pullbackBaseChange ι s g)).toQuotientModule := by
  simp

/--
info: 'AlgebraicGeometry.Scheme.Hom.surjective_idealPullbackMap_app_of_le_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.surjective_idealPullbackMap_app_of_le_map

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.surjective_idealPullbackMap_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.surjective_idealPullbackMap_app

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.epi_idealPullbackMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.epi_idealPullbackMap

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.pullbackIdealMonoFactorisationIsImage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.pullbackIdealMonoFactorisationIsImage

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.pullbackIdealImageIso_hom_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.pullbackIdealImageIso_hom_inclusion

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.quotientModulePullbackIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientModulePullbackIso

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.pullback_map_toQuotientModule_quotientModulePullbackIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.IdealSheafData.pullback_map_toQuotientModule_quotientModulePullbackIso_hom

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.pushforwardUnitPullbackIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.pushforwardUnitPullbackIso

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_comap

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.quotientModuleIsoPushforward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientModuleIsoPushforward

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.quotientModule_isQuasicoherent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientModule_isQuasicoherent

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.shortComplex_shortExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.shortComplex_shortExact
