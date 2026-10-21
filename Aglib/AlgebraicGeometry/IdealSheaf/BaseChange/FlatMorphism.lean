/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Actual ideal modules under flat base change

The canonical comparison of actual kernel ideal modules is an isomorphism when
the base-change morphism is flat and the original morphism is affine. The proof
uses exact geometric pullback and the canonical affine structure-module base
change. It requires no Noetherianity, closed immersion, or invertible ideal.

This is distinct from `BaseChange.Flat`, whose flatness hypothesis concerns a
quotient over a further base and permits an arbitrary base-change morphism.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {D S X : Scheme.{u}} (i : D ⟶ S) (b : X ⟶ S)

/-- The actual structure-module base-change comparison is adjoint to the
specified pushforward square map. -/
theorem structureModuleBaseChangeMap_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit D.ringCatSheaf))
        ((Scheme.Modules.pushforward (pullback.snd i b)).obj
          (SheafOfModules.unit (pullback i b).ringCatSheaf))
        (structureModuleBaseChangeMap i b) =
      squareStructureModuleMap i (pullback.snd i b) b (pullback.fst i b)
        (pullback.condition (f := i) (g := b)) := by
  let a := pullback.fst i b
  let j := pullback.snd i b
  let H := IsPullback.of_hasPullback i b
  let e := cartesianPushforwardSquare a j i b H
  have hn := e.hom.naturality (pullbackUnitIso a).hom
  dsimp only [Functor.comp_map] at hn
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (SheafOfModules.unit D.ringCatSheaf) ≫
      (Scheme.Modules.pushforward a).map (pullbackUnitIso a).hom =
        structureModuleMap a := pullbackUnitIso_homEquiv a
  simp only [structureModuleBaseChangeMap, Adjunction.homEquiv_unit,
    Functor.map_comp]
  change (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward b).map
        (moduleBaseChangeMap i b (SheafOfModules.unit D.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pushforward j).map (pullbackUnitIso a).hom) = _
  rw [← Category.assoc, ← moduleBaseChangeMap_unit, Category.assoc]
  change (Scheme.Modules.pushforward i).map
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app _) ≫
      e.hom.app _ ≫ (Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pushforward j).map (pullbackUnitIso a).hom) = _
  erw [← hn, ← Functor.map_comp_assoc, hu]
  rfl

/-- Affine structure-module base change commutes with the original structure
maps and the canonical pullback of the unit. -/
@[reassoc]
theorem structureModuleBaseChangeMap_comm :
    (Scheme.Modules.pullback b).map (structureModuleMap i) ≫
        structureModuleBaseChangeMap i b =
      (pullbackUnitIso b).hom ≫ structureModuleMap (pullback.snd i b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, structureModuleBaseChangeMap_adjoint,
    Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
  exact squareStructureModuleMap_comm i (pullback.snd i b) b (pullback.fst i b)
    (pullback.condition (f := i) (g := b))

/-- Flat base change of an affine morphism preserves its actual kernel ideal;
the isomorphism is the previously constructed canonical ideal comparison. -/
theorem idealPullbackMap_isIso_of_flat_standard [IsAffineHom i] [Flat b] :
    IsIso (idealPullbackMap i (pullback.snd i b) b (pullback.fst i b)
      (pullback.condition (f := i) (g := b))) := by
  have : IsIso (structureModuleBaseChangeMap i b) :=
    structureModuleBaseChangeMap_isIso i affineModuleBaseChange X b
  let e := PreservesKernel.iso (Scheme.Modules.pullback b) (structureModuleMap i) ≪≫
    kernel.mapIso ((Scheme.Modules.pullback b).map (structureModuleMap i))
      (structureModuleMap (pullback.snd i b)) (pullbackUnitIso b)
      (asIso (structureModuleBaseChangeMap i b)) (structureModuleBaseChangeMap_comm i b)
  have he : idealPullbackMap i (pullback.snd i b) b (pullback.fst i b)
      (pullback.condition (f := i) (g := b)) = e.hom := by
    apply (cancel_mono (idealInclusion (pullback.snd i b))).mp
    rw [idealPullbackMap_inclusion]
    simp only [e, Iso.trans_hom, idealInclusion, Category.assoc, kernel.mapIso_hom,
      kernel.map, kernel.lift_ι]
    rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  rw [he]
  infer_instance

/-- Along a displayed cartesian square, flatness of the base-change morphism
and affineness of the original morphism invert the actual ideal comparison. -/
theorem idealPullbackMap_isIso_of_flat {D' : Scheme.{u}} (i' : D' ⟶ X)
    (a : D' ⟶ D) (h : a ≫ i = i' ≫ b) (H : IsPullback a i' i b)
    [IsAffineHom i] [Flat b] : IsIso (idealPullbackMap i i' b a h) := by
  let e := H.isoPullback
  have hX' : (Iso.refl D).hom ≫ i = i ≫ (Iso.refl S).hom := by simp
  have hY : e.hom ≫ pullback.snd i b = i' ≫ (Iso.refl X).hom := by
    simpa only [e, Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd
  have hb : (Iso.refl X).hom ≫ b = b ≫ (Iso.refl S).hom := by simp
  have := idealPullbackMap_isIso_of_iso_square i i (Iso.refl S).hom
    (Iso.refl D).hom hX'
  have := idealPullbackMap_isIso_of_iso_square (pullback.snd i b) i'
    (Iso.refl X).hom e.hom hY
  have := idealPullbackMap_isIso_of_flat_standard i b
  exact idealPullbackMap_isIso_of_isoSquares i i' b a h i (pullback.snd i b)
    b (pullback.fst i b) (pullback.condition (f := i) (g := b))
    (Iso.refl S) (Iso.refl D) (Iso.refl X) e hX' hY hb

end AlgebraicGeometry.Scheme.Hom
