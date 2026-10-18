/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalGluedCover

/-!
# Effectiveness for supplied local finite étale models and actual arrow lifts

The inputs are concrete local covers, their actual base-change isomorphisms,
and arrows whose pullbacks are prescribed. No local equivalence/fullness is
assumed. Faithfulness proves the diagram laws; fpqc reflection proves its
equifiberedness. Actual scheme gluing and the fixed colimit comparison then
give the global cover and its reconstruction isomorphism.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global.Explicit

universe u
variable {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f] [Flat f] [QuasiCompact f]
  (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  (Y : Scheme.FiniteEtale T) (M : ∀ i : 𝒰.I₀, Scheme.FiniteEtale (𝒰.X i))
  (e : ∀ i : 𝒰.I₀,
    (baseChange (pullback.fst (𝒰.f i) f)).obj (M i) ≅
      (baseChange (pullback.snd (𝒰.f i) f)).obj Y)

/-- The local model over `X`, obtained by composing its structure map with the chart map
`𝒰.f i`. -/
def modelOver (i : 𝒰.I₀) : Over X := (Over.map (𝒰.f i)).obj (M i).obj

/-- The structure morphism from the local model over `X` to the corresponding chart. -/
def modelStructure (i : 𝒰.I₀) : modelOver 𝒰 M i ⟶ (chartDiagram 𝒰).obj i :=
  Over.homMk (M i).obj.hom rfl

/-- The comparison from the pullback of the local model to the geometric local diagram, induced
by `e i`. -/
def modelIso (i : 𝒰.I₀) :
    (Over.pullback f).obj (modelOver 𝒰 M i) ≅ (geometricLocalDiagram f 𝒰 Y).obj i :=
  localObjectIso f (𝒰.f i) (M i).obj Y.obj ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget
    _).mapIso (e i))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem modelIso_structure (i : 𝒰.I₀) :
    (Over.pullback f).map (modelStructure 𝒰 M i) =
      (modelIso f 𝒰 Y M e i).hom ≫ (geometricLocalStructure f 𝒰 Y).app i :=
  localObjectIso_structure f (𝒰.f i) (M i).obj Y.obj
    ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget _).mapIso (e i))

variable (h : ∀ {i j : 𝒰.I₀} (d : i ⟶ j),
  ∃ g : modelOver 𝒰 M i ⟶ modelOver 𝒰 M j,
    (Over.pullback f).map g = (modelIso f 𝒰 Y M e i).hom ≫
      (geometricLocalDiagram f 𝒰 Y).map d ≫ (modelIso f 𝒰 Y M e j).inv)

/-- The diagram of local models over `X`, using the transition morphisms supplied by `h`. -/
def modelDiagram : 𝒰.I₀ ⥤ Over X :=
  CategoryTheory.Functor.DiagramLift.diagramLift (Over.pullback f) (geometricLocalDiagram f 𝒰 Y)
    (modelOver 𝒰 M) (modelIso f 𝒰 Y M e) h

/-- The natural transformation from the model diagram to the chart diagram, with components
`modelStructure`. -/
def modelDiagramStructure : modelDiagram f 𝒰 Y M e h ⟶ chartDiagram 𝒰 :=
  CategoryTheory.Functor.DiagramLift.diagramLiftStructure (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y)
    (modelOver 𝒰 M) (modelIso f 𝒰 Y M e) h (chartDiagram 𝒰)
    (geometricLocalStructure f 𝒰 Y) (modelStructure 𝒰 M) (modelIso_structure f 𝒰 Y M e)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem geometricStructure_equifibered : (geometricLocalStructure f 𝒰 Y).Equifibered := by
  intro i j d
  apply IsPullback.of_map (Over.forget T) ((geometricLocalStructure f 𝒰 Y).naturality d)
  exact overPullback_map_isPullback Y.obj.hom
    ((Over.pullback f).map ((chartDiagram 𝒰).map d))

theorem modelDiagramStructure_equifibered :
    (modelDiagramStructure f 𝒰 Y M e h).Equifibered := by
  let : (Over.pullback f).ReflectsIsomorphisms := overPullback_reflectsIsomorphisms f
  exact CategoryTheory.Functor.DiagramLift.diagramLiftStructure_equifibered (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y)
    (modelOver 𝒰 M) (modelIso f 𝒰 Y M e) h (chartDiagram 𝒰)
    (geometricLocalStructure f 𝒰 Y) (modelStructure 𝒰 M) (modelIso_structure f 𝒰 Y M e)
    (geometricStructure_equifibered f 𝒰 Y)

/-- Relative gluing data for the local models, obtained by forgetting their maps to `X`. -/
def gluingData : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := modelDiagram f 𝒰 Y M e h ⋙ Over.forget X
  natTrans := Functor.whiskerRight (modelDiagramStructure f 𝒰 Y M e h) (Over.forget X)
  equifibered {_i _j} d :=
    ((modelDiagramStructure_equifibered f 𝒰 Y M e h) d).map (Over.forget X)

/-- The finite étale cover over `X` obtained by gluing the local models with transition data
`h`. -/
def gluedCover : Scheme.FiniteEtale X := by
  let D := gluingData f 𝒰 Y M e h
  have (i : 𝒰.I₀) : IsFinite (D.natTrans.app i) := inferInstanceAs (IsFinite (M i).obj.hom)
  have (i : 𝒰.I₀) : Etale (D.natTrans.app i) := inferInstanceAs (Etale (M i).obj.hom)
  exact Scheme.FiniteEtale.RelativeGluing.gluedCover D

/-- The cocone over the model diagram whose vertex is the glued cover and whose legs are gluing
inclusions. -/
def gluedCocone : Cocone (modelDiagram f 𝒰 Y M e h) where
  pt := (gluedCover f 𝒰 Y M e h).obj
  ι :=
    { app i := Over.homMk (colimit.ι (gluingData f 𝒰 Y M e h).functor i)
        ((gluingData f 𝒰 Y M e h).ι_toBase i)
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (gluingData f 𝒰 Y M e h).functor.map d ≫
            colimit.ι (gluingData f 𝒰 Y M e h).functor j =
          colimit.ι (gluingData f 𝒰 Y M e h).functor i ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (gluingData f 𝒰 Y M e h).functor d }

/-- The colimit structure on the model cocone, reflected from the underlying scheme colimit. -/
def gluedCoconeIsColimit : IsColimit (gluedCocone f 𝒰 Y M e h) := by
  apply isColimitOfReflects (Over.forget X)
  change IsColimit (colimit.cocone (gluingData f 𝒰 Y M e h).functor)
  exact colimit.isColimit _

/-- The comparison from the model diagram to the open-cover diagram of the glued cover. -/
def diagramCoverIso : modelDiagram f 𝒰 Y M e h ≅
    overCoverDiagram (gluedCover f 𝒰 Y M e h).obj (gluingData f 𝒰 Y M e h).cover :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (Iso.refl _) (by
    change (𝟙 ((modelDiagram f 𝒰 Y M e h).obj i).left) ≫
        (colimit.ι (gluingData f 𝒰 Y M e h).functor i ≫
          (gluingData f 𝒰 Y M e h).toBase) = (M i).obj.hom ≫ 𝒰.f i
    rw [Category.id_comp]
    exact (gluingData f 𝒰 Y M e h).ι_toBase i)) (by
      intro i j d
      apply Over.OverMorphism.ext
      change ((modelDiagram f 𝒰 Y M e h).map d).left ≫ 𝟙 _ =
        𝟙 _ ≫ ((modelDiagram f 𝒰 Y M e h).map d).left
      simp)

/-- The colimit structure on the glued cocone after pullback along `f`. -/
def pulledGluedCoconeIsColimit :
    IsColimit ((Over.pullback f).mapCocone (gluedCocone f 𝒰 Y M e h)) := by
  let : PreservesColimit
      (overCoverDiagram (gluedCover f 𝒰 Y M e h).obj (gluingData f 𝒰 Y M e h).cover)
      (Over.pullback f) :=
    overPullback_preserves_overCoverDiagram (gluedCover f 𝒰 Y M e h).obj
      (gluingData f 𝒰 Y M e h).cover f
  let : PreservesColimit (modelDiagram f 𝒰 Y M e h) (Over.pullback f) :=
    preservesColimit_of_iso_diagram (Over.pullback f) (diagramCoverIso f 𝒰 Y M e h).symm
  exact isColimitOfPreserves (Over.pullback f) (gluedCoconeIsColimit f 𝒰 Y M e h)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem targetComponentIso_hom_ι (i : 𝒰.I₀) :
    (geometricTargetComponentIso f 𝒰 Y i).hom ≫
      (overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)).ι.app i =
        (geometricLocalCocone f 𝒰 Y).ι.app i := by
  apply Over.OverMorphism.ext
  change (_ ≫ _) ≫ pullback.fst (Y.obj.hom ≫ f) (𝒰.f i) =
    pullback.snd (pullback.snd (𝒰.f i) f) Y.obj.hom
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_hom_snd]

/-- The comparison from the geometric local diagram to the diagram of the induced open cover of
`Y`. -/
def targetDiagramIso :
    geometricLocalDiagram f 𝒰 Y ≅ overCoverDiagram Y.obj (targetOpenCover f 𝒰 Y) :=
  NatIso.ofComponents (geometricTargetComponentIso f 𝒰 Y) (by
    intro i j d
    let c := overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)
    have : Mono (c.ι.app j).left := inferInstanceAs (Mono ((targetOpenCover f 𝒰 Y).f j))
    let : Mono (c.ι.app j) := Over.mono_of_mono_left _
    apply (cancel_mono (c.ι.app j)).mp
    rw [Category.assoc, targetComponentIso_hom_ι,
      (geometricLocalCocone f 𝒰 Y).w d, Category.assoc, c.w d]
    exact (targetComponentIso_hom_ι f 𝒰 Y i).symm)

/-- The colimit structure on the geometric local cocone, transported from the open-cover
colimit. -/
def localCoconeIsColimit : IsColimit (geometricLocalCocone f 𝒰 Y) := by
  let e := targetDiagramIso f 𝒰 Y
  let c := overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)
  have hc := (IsColimit.precomposeHomEquiv e c).symm
    (overCoverCoconeIsColimit Y.obj (targetOpenCover f 𝒰 Y))
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  change ((geometricTargetComponentIso f 𝒰 Y i).hom ≫ c.ι.app i) ≫ 𝟙 _ =
    (geometricLocalCocone f 𝒰 Y).ι.app i
  rw [Category.comp_id]
  exact targetComponentIso_hom_ι f 𝒰 Y i

/-- Reconstruction for the actual supplied local models, isomorphisms and arrows. -/
def baseChangeIso : (baseChange f).obj (gluedCover f 𝒰 Y M e h) ≅ Y :=
  ObjectProperty.isoMk _
    ((pulledGluedCoconeIsColimit f 𝒰 Y M e h).coconePointsIsoOfNatIso
      (localCoconeIsColimit f 𝒰 Y)
      (CategoryTheory.Functor.DiagramLift.diagramLiftIso (Over.pullback f) (geometricLocalDiagram
        f 𝒰 Y)
        (modelOver 𝒰 M) (modelIso f 𝒰 Y M e) h))

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global.Explicit

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 34aa2bed18d344d29ed6502ec6526291079b86d844ac485f8192826697aa5c7e.
Definitions, hypotheses and universes are retained modulo native names. -/
