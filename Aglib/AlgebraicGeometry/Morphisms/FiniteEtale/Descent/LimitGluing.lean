/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.RelativeFiniteEtaleGluing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOpenCoverColimits

/-!
# Reconstruction from a specified equifibered finite-etale diagram

This interface uses an actual diagram, its laws and its equifibered structure.
It imposes no flatness, surjectivity or faithfulness on the base-change map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

section Glue

variable {X : Scheme.{u}} (𝒰 : X.OpenCover)
  [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  (F : 𝒰.I₀ ⥤ Over X)
  (m : F ⟶ Over.lift 𝒰.functorOfLocallyDirected 𝒰.functorOfLocallyDirectedHomBase)
  (hm : m.Equifibered)

/-- The supplied actual over-category diagram as native relative gluing data. -/
def gluingData : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := F ⋙ Over.forget X
  natTrans := Functor.whiskerRight m (Over.forget X)
  equifibered {_i _j} d := (hm d).map (Over.forget X)

variable [∀ i, IsFinite (m.app i).left] [∀ i, Etale (m.app i).left]

/-- The finite-etale scheme obtained by the native relative gluing construction. -/
def gluedCover : FiniteEtale X := by
  let G := gluingData 𝒰 F m hm
  have (i : 𝒰.I₀) : IsFinite (G.natTrans.app i) :=
    inferInstanceAs (IsFinite (m.app i).left)
  have (i : 𝒰.I₀) : Etale (G.natTrans.app i) :=
    inferInstanceAs (Etale (m.app i).left)
  exact RelativeGluing.gluedCover G

/-- The actual gluing inclusions form a cocone in the over category. -/
def gluedCocone : Cocone F where
  pt := (gluedCover 𝒰 F m hm).obj
  ι :=
    { app i := Over.homMk (colimit.ι (gluingData 𝒰 F m hm).functor i)
        (((gluingData 𝒰 F m hm).ι_toBase i).trans (Over.w (m.app i)))
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (gluingData 𝒰 F m hm).functor.map d ≫
            colimit.ι (gluingData 𝒰 F m hm).functor j =
          colimit.ι (gluingData 𝒰 F m hm).functor i ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (gluingData 𝒰 F m hm).functor d }

/-- Gluing is a colimit also in the over category. -/
def gluedCoconeIsColimit : IsColimit (gluedCocone 𝒰 F m hm) := by
  apply isColimitOfReflects (Over.forget X)
  change IsColimit (colimit.cocone (gluingData 𝒰 F m hm).functor)
  exact colimit.isColimit _

/-- The supplied diagram is the open-cover diagram of its native glued object. -/
def diagramCoverIso : F ≅
    overCoverDiagram (gluedCover 𝒰 F m hm).obj (gluingData 𝒰 F m hm).cover :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (Iso.refl _) (by
    change (𝟙 (F.obj i).left) ≫
        (colimit.ι (gluingData 𝒰 F m hm).functor i ≫
          (gluingData 𝒰 F m hm).toBase) = (F.obj i).hom
    rw [Category.id_comp]
    exact ((gluingData 𝒰 F m hm).ι_toBase i).trans (Over.w (m.app i)))) (by
      intro i j d
      apply Over.OverMorphism.ext
      change (F.map d).left ≫ 𝟙 _ = 𝟙 _ ≫ (F.map d).left
      simp)

/-- Arbitrary base change preserves the cocone of an equifibered gluing diagram. -/
def pulledGluedCoconeIsColimit {T : Scheme.{u}} (f : T ⟶ X) :
    IsColimit ((Over.pullback f).mapCocone (gluedCocone 𝒰 F m hm)) := by
  let : PreservesColimit
      (overCoverDiagram (gluedCover 𝒰 F m hm).obj (gluingData 𝒰 F m hm).cover)
      (Over.pullback f) :=
    overPullback_preserves_overCoverDiagram (gluedCover 𝒰 F m hm).obj
      (gluingData 𝒰 F m hm).cover f
  let : PreservesColimit F (Over.pullback f) :=
    preservesColimit_of_iso_diagram (Over.pullback f) (diagramCoverIso 𝒰 F m hm).symm
  exact isColimitOfPreserves (Over.pullback f) (gluedCoconeIsColimit 𝒰 F m hm)

/-- A specified comparison to a colimit diagram reconstructs the prescribed cover,
without any faithful-flatness hypothesis on the base-change map. -/
def baseChangeIsoOfCocone {T : Scheme.{u}} (f : T ⟶ X)
    (Y : FiniteEtale T) (G : 𝒰.I₀ ⥤ Over T)
    (s : Cocone G) (hs : IsColimit s) (e : F ⋙ Over.pullback f ≅ G)
    (hY : s.pt ≅ Y.obj) : (baseChange f).obj (gluedCover 𝒰 F m hm) ≅ Y :=
  ObjectProperty.isoMk _
    ((pulledGluedCoconeIsColimit 𝒰 F m hm f).coconePointsIsoOfNatIso hs e ≪≫ hY)

end Glue

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
