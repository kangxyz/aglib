module

import Aglib.AlgebraicGeometry.Blowup.Construction
import Aglib.AlgebraicGeometry.Blowup.Properness

/-! Public consumers of actual global blowup construction, properness and saturated atlases. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Blowup
universe u

namespace AglibTest.BlowupGlobal

/-- All four exact original theorem-family types have proved suppliers on one coherent basis. -/
example : NoetherianBlowupExistence.{u} ∧ NoetherianBlowupProper.{u} ∧
    BlowupFlatBaseChange.{u} ∧ BlowupAffineAtlas.{u} :=
  ⟨noetherianBlowupExistence, noetherianBlowupProper, blowupFlatBaseChange, blowupAffineAtlas⟩

/-- The actual constructed datum has the final-object property on arbitrary test schemes,
with exactly the original Cartier image-ideal premise. -/
example {X : Scheme.{u}} (I : X.IdealSheafData) (T : Scheme.{u}) (f : T ⟶ X)
    (hf : cartierPullback I f) :
    ∃! g : T ⟶ (blowupDatum I).Y, g ≫ (blowupDatum I).map = f :=
  (blowupDatum I).universal T f hf

/-- The local chart is literally cartesian over its original affine base open. -/
example {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (Construction.localDatum I U).map (colimit.ι (Construction.diagram I) U)
      U.1.ι (blowupDatum I).map :=
  Construction.local_isPullback I U

/-- Locally Noetherian bases now have an actual proper universal representative. -/
example {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    ∃ B : BlowupDatum I, IsProper B.map :=
  ⟨blowupDatum I, (blowupDatum I).isProper_of_isLocallyNoetherian⟩

/-- Every given affine universal representative has the literal original ratio-localization
overlaps. The direct atlas construction itself needs no Noetherian ring premise. -/
example {A : Type u} [CommRing A] {I : Ideal A}
    (B : BlowupDatum (affineCenter A I)) (a b : I) :
    Set.range (affineOverlapMap A I a b ≫ (affineAtlas B).chart a) =
      Set.range ((affineAtlas B).chart a) ∩ Set.range ((affineAtlas B).chart b) :=
  (affineAtlas B).overlap a b

/-- The atlas keeps the original saturated rings and base scalar maps on every chart. -/
example {A : Type u} [CommRing A] {I : Ideal A}
    (B : BlowupDatum (affineCenter A I)) (a : I) :
    (affineAtlas B).chart a ≫ B.map = affineChartMap A I a :=
  (affineAtlas B).triangle a

end AglibTest.BlowupGlobal
