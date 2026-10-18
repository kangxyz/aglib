/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalExplicitDescent

/-!
# Relative gluing from supplied objects and arrows in the over category

This interface preserves the exact over-category objects used by finite-stage
limit descent. It constructs effectiveness from their actual structural maps,
base-change isomorphisms and arrow lifts.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global.OverModels

universe u
variable {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f] [Flat f] [QuasiCompact f]
  (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  (Y : Scheme.FiniteEtale T) (A : 𝒰.I₀ → Over X)
  (m : ∀ i, A i ⟶ (chartDiagram 𝒰).obj i)
  (α : ∀ i, (Over.pullback f).obj (A i) ≅ (geometricLocalDiagram f 𝒰 Y).obj i)
  (hm : ∀ i, (Over.pullback f).map (m i) =
    (α i).hom ≫ (geometricLocalStructure f 𝒰 Y).app i)
  (h : ∀ {i j : 𝒰.I₀} (d : i ⟶ j), ∃ g : A i ⟶ A j,
    (Over.pullback f).map g = (α i).hom ≫ (geometricLocalDiagram f 𝒰 Y).map d ≫ (α j).inv)

/-- The diagram of the supplied models `A`, using the arrow lifts supplied by `h`. -/
def modelDiagram : 𝒰.I₀ ⥤ Over X :=
  CategoryTheory.Functor.DiagramLift.diagramLift (Over.pullback f) (geometricLocalDiagram f 𝒰 Y)
    A α h

/-- The natural structural maps from the model diagram to the chart diagram, using `m` and `hm`. -/
def modelStructure : modelDiagram f 𝒰 Y A α h ⟶ chartDiagram 𝒰 :=
  CategoryTheory.Functor.DiagramLift.diagramLiftStructure (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y) A α h
    (chartDiagram 𝒰) (geometricLocalStructure f 𝒰 Y) m hm

theorem modelStructure_equifibered : (modelStructure f 𝒰 Y A m α hm h).Equifibered := by
  let : (Over.pullback f).ReflectsIsomorphisms := overPullback_reflectsIsomorphisms f
  exact CategoryTheory.Functor.DiagramLift.diagramLiftStructure_equifibered (Over.pullback f)
    (geometricLocalDiagram f 𝒰 Y)
    A α h (chartDiagram 𝒰) (geometricLocalStructure f 𝒰 Y) m hm
    (Explicit.geometricStructure_equifibered f 𝒰 Y)

/-- The relative gluing data obtained from the model diagram and its equifibered structural
maps. -/
def gluingData : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := modelDiagram f 𝒰 Y A α h ⋙ Over.forget X
  natTrans := Functor.whiskerRight (modelStructure f 𝒰 Y A m α hm h) (Over.forget X)
  equifibered {_i _j} d :=
    ((modelStructure_equifibered f 𝒰 Y A m α hm h) d).map (Over.forget X)

variable [∀ i, IsFinite (m i).left] [∀ i, Etale (m i).left]

/-- The finite etale cover obtained by gluing the supplied finite etale chart models. -/
def gluedCover : Scheme.FiniteEtale X := by
  let D := gluingData f 𝒰 Y A m α hm h
  have (i : 𝒰.I₀) : IsFinite (D.natTrans.app i) := inferInstanceAs (IsFinite (m i).left)
  have (i : 𝒰.I₀) : Etale (D.natTrans.app i) := inferInstanceAs (Etale (m i).left)
  exact Scheme.FiniteEtale.RelativeGluing.gluedCover D

/-- The cocone from the model diagram to the glued cover, with the canonical gluing inclusions. -/
def gluedCocone : Cocone (modelDiagram f 𝒰 Y A α h) where
  pt := (gluedCover f 𝒰 Y A m α hm h).obj
  ι :=
    { app i := Over.homMk (colimit.ι (gluingData f 𝒰 Y A m α hm h).functor i)
        (((gluingData f 𝒰 Y A m α hm h).ι_toBase i).trans (Over.w (m i)))
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (gluingData f 𝒰 Y A m α hm h).functor.map d ≫
            colimit.ι (gluingData f 𝒰 Y A m α hm h).functor j =
          colimit.ι (gluingData f 𝒰 Y A m α hm h).functor i ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (gluingData f 𝒰 Y A m α hm h).functor d }

/-- The colimit structure of the glued cocone in the category of schemes over `X`. -/
def gluedCoconeIsColimit : IsColimit (gluedCocone f 𝒰 Y A m α hm h) := by
  apply isColimitOfReflects (Over.forget X)
  change IsColimit (colimit.cocone (gluingData f 𝒰 Y A m α hm h).functor)
  exact colimit.isColimit _

/-- The identification of the model diagram with the cover diagram of its glued object. -/
def diagramCoverIso : modelDiagram f 𝒰 Y A α h ≅
    overCoverDiagram (gluedCover f 𝒰 Y A m α hm h).obj (gluingData f 𝒰 Y A m α hm h).cover :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (Iso.refl _) (by
    change (𝟙 (A i).left) ≫
        (colimit.ι (gluingData f 𝒰 Y A m α hm h).functor i ≫
          (gluingData f 𝒰 Y A m α hm h).toBase) = (A i).hom
    rw [Category.id_comp]
    exact ((gluingData f 𝒰 Y A m α hm h).ι_toBase i).trans (Over.w (m i)))) (by
      intro i j d
      apply Over.OverMorphism.ext
      change ((modelDiagram f 𝒰 Y A α h).map d).left ≫ 𝟙 _ =
        𝟙 _ ≫ ((modelDiagram f 𝒰 Y A α h).map d).left
      simp)

/-- The colimit structure on the glued cocone after pullback along `f`. -/
def pulledGluedCoconeIsColimit :
    IsColimit ((Over.pullback f).mapCocone (gluedCocone f 𝒰 Y A m α hm h)) := by
  let : PreservesColimit
      (overCoverDiagram (gluedCover f 𝒰 Y A m α hm h).obj (gluingData f 𝒰 Y A m α hm h).cover)
      (Over.pullback f) :=
    overPullback_preserves_overCoverDiagram (gluedCover f 𝒰 Y A m α hm h).obj
      (gluingData f 𝒰 Y A m α hm h).cover f
  let : PreservesColimit (modelDiagram f 𝒰 Y A α h) (Over.pullback f) :=
    preservesColimit_of_iso_diagram (Over.pullback f) (diagramCoverIso f 𝒰 Y A m α hm h).symm
  exact isColimitOfPreserves (Over.pullback f) (gluedCoconeIsColimit f 𝒰 Y A m α hm h)

/-- Reconstruction using actual over-category local models and their lifts. -/
def baseChangeIso : (baseChange f).obj (gluedCover f 𝒰 Y A m α hm h) ≅ Y :=
  ObjectProperty.isoMk _
    ((pulledGluedCoconeIsColimit f 𝒰 Y A m α hm h).coconePointsIsoOfNatIso
      (Explicit.localCoconeIsColimit f 𝒰 Y)
      (CategoryTheory.Functor.DiagramLift.diagramLiftIso (Over.pullback f) (geometricLocalDiagram
        f 𝒰 Y) A α h))

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global.OverModels

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ccbd56ca32a4e5b00b87b25f673f6a3eb352b6f089abf928014c8f67eb6f34d1.
Definitions, hypotheses and universes are retained modulo native names. -/
