/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImageMaps
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.UnitQuotient
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Actual affine-cover restriction modules and their original quotient units

The comparison is assembled together with its entire original-unit certificate,
first over abstract objects and then specialized once to the literal affine
base-change comparison. No flatness of a thickening is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- Compose an original-unit comparison and a coefficient comparison as one packet. -/
def unitIsoCompositeData {C : Type*} [Category C] {M P Q R : C}
    (u : M ⟶ P) (v : M ⟶ Q) (w : M ⟶ R)
    (e : P ≅ Q) (he : u ≫ e.hom = v) (a : P ≅ R) (ha : u ≫ a.hom = w) :
    {z : Q ≅ R // v ≫ z.hom = w} :=
  ⟨e.symm ≪≫ a, by rw [← he]; simpa only [Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using ha⟩

open Modules

variable {Y X Z : Scheme.{u}} (p : Y ⟶ X) [IsAffineHom p] (j : Z ⟶ X)

/-- The actual quotient of the original direct image is the actual direct image
of the literal pulled-back cover, with its original structure-map equation. -/
def pullbackStructureComparisonData :
    {e : (pushforward j).obj ((Modules.pullback j).obj (pushforwardStructureSheaf p)) ≅
      pushforwardStructureSheaf (Limits.pullback.fst p j ≫ p) //
      (pullbackPushforwardAdjunction j).unit.app (pushforwardStructureSheaf p) ≫ e.hom =
        Modules.Algebra.structurePullbackMap (Limits.pullback.fst p j) rfl} := by
  let O := SheafOfModules.unit Y.ringCatSheaf
  let : O.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun B k _ => ((Modules.Coherent.Support.unit_coherent Y) B k).1)
  let k := Limits.pullback.fst p j
  let a : (pushforward p).obj ((pushforward k).obj ((Modules.pullback k).obj O)) ≅
      pushforwardStructureSheaf (k ≫ p) :=
    (pushforward p).mapIso ((pushforward k).mapIso (pullbackUnitIso k)) ≪≫
      (pushforwardComp k p).app (SheafOfModules.unit _) ≪≫
        (pushforwardCongr (rfl : k ≫ p = k ≫ p)).app (SheafOfModules.unit _)
  refine unitIsoCompositeData
    ((pushforward p).map ((pullbackPushforwardAdjunction k).unit.app O))
    ((pullbackPushforwardAdjunction j).unit.app (pushforwardStructureSheaf p))
    (Modules.Algebra.structurePullbackMap k rfl)
    (affinePushforwardUnitIso p j O) (affinePushforwardUnitIso_unit p j O) a ?_
  have hk : (pullbackPushforwardAdjunction k).unit.app O ≫
      (pushforward k).map (pullbackUnitIso k).hom =
        SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom := by
    simpa only [Adjunction.homEquiv_unit] using pullbackUnitIso_homEquiv k
  dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Modules.Algebra.structurePullbackMap]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hk]
  exact Category.assoc _ _ _

/-- Transport a whole comparison packet contravariantly through the original
isomorphism over a fixed base. -/
def structureComparisonTransport {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {P Q R : C} (g : Q ⟶ P) (e : R ≅ Q) (h : R ⟶ P)
    (he : e.hom ≫ g = h) {M : D} (u : F.obj (op P) ⟶ M)
    (c : {E : M ≅ F.obj (op Q) // u ≫ E.hom = F.map g.op}) :
    {E : M ≅ F.obj (op R) // u ≫ E.hom = F.map h.op} := by
  refine ⟨c.val ≪≫ F.mapIso e.op, ?_⟩
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, ← Category.assoc,
    c.property, ← F.map_comp, ← op_comp, he]

/-- Original affine base change for any displayed cartesian cover square,
retaining its original structure-module arrow in the same packet. -/
def cartesianStructureComparisonData {W : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ Z)
    (H : IsPullback a b p j) :
    {e : (pushforward j).obj ((Modules.pullback j).obj (pushforwardStructureSheaf p)) ≅
      pushforwardStructureSheaf (b ≫ j) //
      (pullbackPushforwardAdjunction j).unit.app (pushforwardStructureSheaf p) ≫ e.hom =
        Modules.Algebra.structurePullbackMap a H.w} := by
  let g : Over.mk (Limits.pullback.fst p j ≫ p) ⟶ Over.mk p :=
    Over.homMk (Limits.pullback.fst p j) rfl
  have hw : H.isoPullback.hom ≫ (Limits.pullback.fst p j ≫ p) = b ≫ j := by
    rw [← Category.assoc, H.isoPullback_hom_fst, H.w]
  let e : Over.mk (b ≫ j) ≅ Over.mk (Limits.pullback.fst p j ≫ p) :=
    Over.isoMk H.isoPullback hw
  let h : Over.mk (b ≫ j) ⟶ Over.mk p := Over.homMk a H.w
  have he : e.hom ≫ g = h := by
    apply Over.OverMorphism.ext
    exact H.isoPullback_hom_fst
  exact structureComparisonTransport (Modules.Algebra.structureSheafFunctor X)
    g e h he ((pullbackPushforwardAdjunction j).unit.app (pushforwardStructureSheaf p))
    (pullbackStructureComparisonData p j)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
