module

import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange

/-! Exact consumers of the universal flat-base-change family and its actual maps. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Blowup
universe u

namespace AglibTest.BlowupFlatBaseChange

/-- The original quantified family now has a proved supplier, without an extra family input. -/
example : Scheme.Blowup.BlowupFlatBaseChange.{u} := blowupFlatBaseChange

/-- The canonical map is cartesian for the exact actual centre equality and arbitrary flat
base map, with both universal representatives given. -/
example {X X' : Scheme.{u}} {I : X.IdealSheafData} {I' : X'.IdealSheafData}
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    IsPullback (BaseChange.map f hI B B') B'.map B.map f :=
  BaseChange.isPullback_of_flat f hf hI B B'

/-- The comparison uses the literal pullback and the original canonical projection maps. -/
example {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] (B' : BlowupDatum (I.comap f)) :
    ∃ e : B'.Y ≅ pullback B.map f,
      e.hom ≫ pullback.fst B.map f = BaseChange.map f rfl B B' ∧
        e.hom ≫ pullback.snd B.map f = B'.map :=
  ⟨flatComparisonIso B f B', flatComparisonIso_hom_fst B f B',
    flatComparisonIso_hom_snd B f B'⟩

/-- The constructed datum retains the exact literal pullback object and second projection. -/
example {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] :
    (flatPullbackDatum B f).Y = pullback B.map f ∧
      (flatPullbackDatum B f).map = pullback.snd B.map f := ⟨rfl, rfl⟩

/-- The old conditional native flat-map consumer is discharged by the new proved family. -/
example {X X' : Scheme.{u}} {I : X.IdealSheafData} {I' : X'.IdealSheafData}
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') : Flat (BaseChange.map f hI B B') :=
  BaseChange.flat blowupFlatBaseChange f hf hI B B'

/-- The lower supplier concerns the actual comap ideal and has no quotient-flat premise. -/
example {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) [Flat f]
    (hI : Scheme.Modules.Invertible.IsLocallyRankOne X (Scheme.Hom.idealModule I.subschemeι)) :
    Scheme.Modules.Invertible.IsLocallyRankOne Y (Scheme.Hom.idealModule (I.comap f).subschemeι) :=
  I.isLocallyRankOne_comap_of_flat f hI

end AglibTest.BlowupFlatBaseChange
