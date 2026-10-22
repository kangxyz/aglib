/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Admissible
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Two-step common refinements of admissible blowups

After blowing up `I`, blow up the actual inverse-image ideal of `J`. The
second blowup has a canonical map to every given blowup of `J`, by its
universal property. This is a two-step refinement, not an identification of
the composite with a single blowup. No arbitrary preservation of Cartier
ideals, or nonflat base-change assertion, is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.TwoStepRefinement

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The second native blowup, with the literal inverse-image centre. -/
def datum (BI : BlowupDatum I) (J : X.IdealSheafData) :
    BlowupDatum (J.comap BI.map) := blowupDatum (J.comap BI.map)

/-- The actual two-step structural morphism. -/
def map (BI : BlowupDatum I) (J : X.IdealSheafData) : (datum BI J).Y ⟶ X :=
  (datum BI J).map ≫ BI.map

/-- Comparison with the first blowup is the second blowdown itself. -/
def toLeft (BI : BlowupDatum I) (J : X.IdealSheafData) : (datum BI J).Y ⟶ BI.Y :=
  (datum BI J).map

@[reassoc (attr := simp)]
theorem toLeft_map (BI : BlowupDatum I) (J : X.IdealSheafData) :
    toLeft BI J ≫ BI.map = map BI J := rfl

/-- Cartierness needed for comparison with the second given blowup is supplied
by the second native blowup, not by pulling back the first Cartier ideal. -/
theorem cartier (BI : BlowupDatum I) (J : X.IdealSheafData) :
    cartierPullback J (map BI J) := by
  have h : J.comap (map BI J) = (J.comap BI.map).comap (datum BI J).map :=
    IdealSheafData.comap_comp J (datum BI J).map BI.map
  exact (congrArg (fun K : (datum BI J).Y.IdealSheafData =>
    Modules.Invertible.IsLocallyRankOne (datum BI J).Y
      (Scheme.Hom.idealModule K.subschemeι)) h).mpr (datum BI J).cartier

/-- The universal-property comparison with the given blowup of `J`. -/
def toRight (BI : BlowupDatum I) (BJ : BlowupDatum J) : (datum BI J).Y ⟶ BJ.Y :=
  BJ.lift (map BI J) (cartier BI J)

@[reassoc (attr := simp)]
theorem toRight_map (BI : BlowupDatum I) (BJ : BlowupDatum J) :
    toRight BI BJ ≫ BJ.map = map BI J :=
  BJ.lift_map (map BI J) (cartier BI J)

/-- Properness of the second native blowdown over a locally Noetherian base. -/
theorem toLeft_isProper [IsLocallyNoetherian X] (BI : BlowupDatum I)
    (J : X.IdealSheafData) : IsProper (toLeft BI J) := by
  let : IsProper BI.map := BI.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian BI.Y := LocallyOfFiniteType.isLocallyNoetherian BI.map
  exact (datum BI J).isProper_of_isLocallyNoetherian

/-- The two-step structural map is proper. -/
theorem map_isProper [IsLocallyNoetherian X] (BI : BlowupDatum I)
    (J : X.IdealSheafData) : IsProper (map BI J) := by
  let : IsProper BI.map := BI.isProper_of_isLocallyNoetherian
  let : IsProper (datum BI J).map := toLeft_isProper BI J
  exact inferInstanceAs (IsProper ((datum BI J).map ≫ BI.map))

/-- The comparison with the second given blowup is also proper. -/
theorem toRight_isProper [IsLocallyNoetherian X] (BI : BlowupDatum I)
    (BJ : BlowupDatum J) : IsProper (toRight BI BJ) := by
  let : IsProper BJ.map := BJ.isProper_of_isLocallyNoetherian
  let : IsProper (toRight BI BJ ≫ BJ.map) := by
    rw [toRight_map]
    exact map_isProper BI J
  exact IsProper.of_comp (toRight BI BJ) BJ.map

/-- The second centre is the unit ideal over the inverse image of a protected
open for `J`; this uses the original restriction square. -/
theorem centre_comap_eq_top (BI : BlowupDatum I) (U : X.Opens)
    (hJ : J.comap U.ι = ⊤) : (J.comap BI.map).comap (BI.map ⁻¹ᵁ U).ι = ⊤ := by
  rw [← IdealSheafData.comap_comp, ← morphismRestrict_ι,
    IdealSheafData.comap_comp, hJ, IdealSheafData.comap_top]

/-- Two admissible blowups have a two-step common refinement that is unchanged
on their common protected open. No Noetherianity is needed for this identity. -/
theorem restrict_isIso (BI : BlowupDatum I) (U : X.Opens)
    (hI : I.comap U.ι = ⊤) (hJ : J.comap U.ι = ⊤) :
    IsIso (map BI J ∣_ U) := by
  change IsIso (((datum BI J).map ≫ BI.map) ∣_ U)
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso'
    ((datum BI J).restrict_isIso_of_comap_eq_top _ (centre_comap_eq_top BI U hJ))
    (BI.restrict_isIso_of_comap_eq_top U hI)

/-- The protected-open identification retains the literal restricted composite. -/
def restrictIso (BI : BlowupDatum I) (U : X.Opens)
    (hI : I.comap U.ι = ⊤) (hJ : J.comap U.ι = ⊤) :
    (map BI J ⁻¹ᵁ U).toScheme ≅ U.toScheme := by
  let := restrict_isIso BI U hI hJ
  exact asIso (map BI J ∣_ U)

@[simp]
theorem restrictIso_hom (BI : BlowupDatum I) (U : X.Opens)
    (hI : I.comap U.ι = ⊤) (hJ : J.comap U.ι = ⊤) :
    (restrictIso BI U hI hJ).hom = map BI J ∣_ U := rfl

@[reassoc]
theorem restrictIso_hom_ι (BI : BlowupDatum I) (U : X.Opens)
    (hI : I.comap U.ι = ⊤) (hJ : J.comap U.ι = ⊤) :
    (restrictIso BI U hI hJ).hom ≫ U.ι = (map BI J ⁻¹ᵁ U).ι ≫ map BI J :=
  morphismRestrict_ι (map BI J) U

end AlgebraicGeometry.Scheme.Blowup.TwoStepRefinement
