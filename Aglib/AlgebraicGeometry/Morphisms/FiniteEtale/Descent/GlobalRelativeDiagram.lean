/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalLocalCoverMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.RelativeFiniteEtaleGluing
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# GlobalRelativeDiagram

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u

variable {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f] [Flat f] [QuasiCompact f]
  (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence]
  (Y : Scheme.FiniteEtale T)

/-- The locally directed open charts of `𝒰`, regarded as objects and arrows over `X`. -/
def chartDiagram : 𝒰.I₀ ⥤ Over X :=
  Over.lift 𝒰.functorOfLocallyDirected 𝒰.functorOfLocallyDirectedHomBase

/-- The chart diagram pulled back to `T`, then along the cover `Y`, and viewed over `T`. -/
def geometricLocalDiagram : 𝒰.I₀ ⥤ Over T :=
  chartDiagram 𝒰 ⋙ Over.pullback f ⋙ Over.pullback Y.obj.hom ⋙ Over.map Y.obj.hom

/-- The projection from the geometric local cover diagram to the pulled-back chart diagram,
given by the counit of `Over.mapPullbackAdj Y.obj.hom`. -/
def geometricLocalStructure : geometricLocalDiagram f 𝒰 Y ⟶ chartDiagram 𝒰 ⋙ Over.pullback f where
  app i := (Over.mapPullbackAdj Y.obj.hom).counit.app
    ((Over.pullback f).obj ((chartDiagram 𝒰).obj i))
  naturality _i _j d := (Over.mapPullbackAdj Y.obj.hom).counit.naturality
    ((Over.pullback f).map ((chartDiagram 𝒰).map d))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem geometricLocalStructure_equifibered : (geometricLocalStructure f 𝒰 Y).Equifibered := by
  intro i j d
  apply IsPullback.of_map (Over.forget T) ((geometricLocalStructure f 𝒰 Y).naturality d)
  exact overPullback_map_isPullback Y.obj.hom
    ((Over.pullback f).map ((chartDiagram 𝒰).map d))

/-- The finite étale model over `𝒰.X i` obtained by the assumed base-change equivalence
from the restriction of `Y` to the pullback of that chart. -/
def localModel (i : 𝒰.I₀) : Scheme.FiniteEtale (𝒰.X i) :=
  (baseChange (pullback.fst (𝒰.f i) f)).asEquivalence.inverse.obj
    ((baseChange (pullback.snd (𝒰.f i) f)).obj Y)

/-- The counit isomorphism identifying the base change of `localModel` with the
restriction of `Y` to the chart pullback. -/
def localModelIso (i : 𝒰.I₀) :
    (baseChange (pullback.fst (𝒰.f i) f)).obj (localModel f 𝒰 Y i) ≅
      (baseChange (pullback.snd (𝒰.f i) f)).obj Y :=
  (baseChange (pullback.fst (𝒰.f i) f)).asEquivalence.counitIso.app _

/-- The local model viewed over `X` by composing its structure map with `𝒰.f i`. -/
def localModelOver (i : 𝒰.I₀) : Over X :=
  (Over.map (𝒰.f i)).obj (localModel f 𝒰 Y i).obj

/-- The structure morphism from the local model over `X` to its open chart over `X`. -/
def localModelStructure (i : 𝒰.I₀) : localModelOver f 𝒰 Y i ⟶ (chartDiagram 𝒰).obj i :=
  Over.homMk (localModel f 𝒰 Y i).obj.hom rfl

/-- The pullback symmetry exchanging `A ×[T] B` and `B ×[T] A` as objects over `T`. -/
def localTargetSymmetryIso (A B : Over T) :
    (Over.map B.hom).obj ((Over.pullback B.hom).obj A) ≅
      (Over.map A.hom).obj ((Over.pullback A.hom).obj B) :=
  Over.isoMk (pullbackSymmetry A.hom B.hom) (by
    change (pullbackSymmetry A.hom B.hom).hom ≫
      (pullback.snd B.hom A.hom ≫ A.hom) = pullback.snd A.hom B.hom ≫ B.hom
    rw [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.condition])

@[reassoc (attr := simp)] theorem localTargetSymmetryIso_hom_fst (A B : Over T) :
    (localTargetSymmetryIso A B).hom.left ≫ pullback.fst B.hom A.hom =
      pullback.snd A.hom B.hom := pullbackSymmetry_hom_comp_fst _ _

/-- Transport a supplied comparison `α` over `U ×[X] T` to the comparison over `T`,
using pullback composition and symmetry. -/
def localObjectIso {U : Scheme.{u}} (i : U ⟶ X) (A : Over U) (Z : Over T)
    (α : (Over.pullback (pullback.fst i f)).obj A ≅
      (Over.pullback (pullback.snd i f)).obj Z) :
    (Over.pullback f).obj ((Over.map i).obj A) ≅
      (Over.map Z.hom).obj ((Over.pullback Z.hom).obj (Over.mk (pullback.snd i f))) :=
  localPullbackPushforwardIso f i A ≪≫
    (Over.map (pullback.snd i f)).mapIso α ≪≫
    localTargetSymmetryIso Z (Over.mk (pullback.snd i f))

omit [Surjective f] [Flat f] [QuasiCompact f] in
theorem localObjectIso_structure {U : Scheme.{u}} (i : U ⟶ X) (A : Over U) (Z : Over T)
    (α : (Over.pullback (pullback.fst i f)).obj A ≅
      (Over.pullback (pullback.snd i f)).obj Z) :
    (Over.pullback f).map (Over.homMk A.hom rfl : (Over.map i).obj A ⟶ Over.mk i) =
      (localObjectIso f i A Z α).hom ≫
        (Over.mapPullbackAdj Z.hom).counit.app (Over.mk (pullback.snd i f)) := by
  apply Over.OverMorphism.ext
  have H : α.hom.left ≫ pullback.snd Z.hom (Over.mk (pullback.snd i f)).hom =
      pullback.snd A.hom (pullback.fst i f) := Over.w α.hom
  simp only [localObjectIso, Iso.trans_hom, Over.comp_left, Functor.mapIso_hom,
    Over.map_map_left, Over.mapPullbackAdj_counit_app, Over.homMk_left, Category.assoc]
  rw [localTargetSymmetryIso_hom_fst, H]
  exact localPullbackPushforwardIso_structure f i A

/-- The comparison over `T` between the pulled-back local model and the corresponding
object of `geometricLocalDiagram`. -/
def localModelGeometricIso (i : 𝒰.I₀) :
    (Over.pullback f).obj (localModelOver f 𝒰 Y i) ≅ (geometricLocalDiagram f 𝒰 Y).obj i :=
  localObjectIso f (𝒰.f i) (localModel f 𝒰 Y i).obj Y.obj
    ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget _).mapIso (localModelIso f 𝒰 Y i))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem localModelGeometricIso_structure (i : 𝒰.I₀) :
    (Over.pullback f).map (localModelStructure f 𝒰 Y i) =
      (localModelGeometricIso f 𝒰 Y i).hom ≫ (geometricLocalStructure f 𝒰 Y).app i :=
  localObjectIso_structure f (𝒰.f i) (localModel f 𝒰 Y i).obj Y.obj
    ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget _).mapIso (localModelIso f 𝒰 Y i))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem localModel_arrow_lifts {i j : 𝒰.I₀} (d : i ⟶ j) :
    ∃ g : localModelOver f 𝒰 Y i ⟶ localModelOver f 𝒰 Y j,
      (Over.pullback f).map g = (localModelGeometricIso f 𝒰 Y i).hom ≫
        (geometricLocalDiagram f 𝒰 Y).map d ≫ (localModelGeometricIso f 𝒰 Y j).inv :=
  local_overMap_surjective f (𝒰.f i) (𝒰.f j) (𝒰.trans d) (𝒰.trans_map d)
    (localModel f 𝒰 Y i) (localModel f 𝒰 Y j) _

/-- The diagram over `X` lifted from `geometricLocalDiagram` using the local models,
their geometric comparisons and the proved arrow lifts. -/
def descendedLocalDiagram : 𝒰.I₀ ⥤ Over X :=
  CategoryTheory.Functor.DiagramLift.diagramLift (Over.pullback f) (geometricLocalDiagram f 𝒰 Y)
    (localModelOver f 𝒰 Y) (localModelGeometricIso f 𝒰 Y) (localModel_arrow_lifts f 𝒰 Y)

/-- The structure transformation from the descended local diagram to the chart diagram,
whose components are the local model structure morphisms. -/
def descendedLocalStructure : descendedLocalDiagram f 𝒰 Y ⟶ chartDiagram 𝒰 :=
  CategoryTheory.Functor.DiagramLift.diagramLiftStructure (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y)
    (localModelOver f 𝒰 Y) (localModelGeometricIso f 𝒰 Y) (localModel_arrow_lifts f 𝒰 Y)
    (chartDiagram 𝒰) (geometricLocalStructure f 𝒰 Y) (localModelStructure f 𝒰 Y)
    (localModelGeometricIso_structure f 𝒰 Y)

theorem descendedLocalStructure_equifibered : (descendedLocalStructure f 𝒰 Y).Equifibered := by
  let : (Over.pullback f).ReflectsIsomorphisms := overPullback_reflectsIsomorphisms f
  exact CategoryTheory.Functor.DiagramLift.diagramLiftStructure_equifibered (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y)
    (localModelOver f 𝒰 Y) (localModelGeometricIso f 𝒰 Y) (localModel_arrow_lifts f 𝒰 Y)
    (chartDiagram 𝒰) (geometricLocalStructure f 𝒰 Y) (localModelStructure f 𝒰 Y)
    (localModelGeometricIso_structure f 𝒰 Y) (geometricLocalStructure_equifibered f 𝒰 Y)

/-- Actual equifibered scheme diagram; its compatibility is proved from the
local equivalences and faithful-flat reflection, not assumed as gluing data. -/
def relativeDescentData : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := descendedLocalDiagram f 𝒰 Y ⋙ Over.forget X
  natTrans := Functor.whiskerRight (descendedLocalStructure f 𝒰 Y) (Over.forget X)
  equifibered {_i _j} d := ((descendedLocalStructure_equifibered f 𝒰 Y) d).map (Over.forget X)

/-- The finite étale cover over `X` obtained by relative gluing of the descended local models. -/
def globalCoverCandidate : Scheme.FiniteEtale X := by
  let D := relativeDescentData f 𝒰 Y
  have (i : 𝒰.I₀) : IsFinite (D.natTrans.app i) :=
    inferInstanceAs (IsFinite (localModel f 𝒰 Y i).obj.hom)
  have (i : 𝒰.I₀) : Etale (D.natTrans.app i) :=
    inferInstanceAs (Etale (localModel f 𝒰 Y i).obj.hom)
  exact Scheme.FiniteEtale.RelativeGluing.gluedCover D

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bddd422a3c03c9182ef903a066eefecd01c454a251245872d268f90a3e5a3ee9.
Definitions, hypotheses and universes are retained modulo native names. -/
