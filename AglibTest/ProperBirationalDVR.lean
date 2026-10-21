module

import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
import Aglib.AlgebraicGeometry.Morphisms.Proper.DVRRecognition

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

-- The exact pre-existing family has a universal supplier with no new family input.
example : Scheme.ProperBirationalDVRIsomorphismLocus.{u} :=
  Scheme.properBirationalDVRIsomorphismLocus

-- The stronger result works without a Noetherian or discrete-valuation assumption.
example {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (y : Y) [ValuationRing (Y.presheaf.stalk y)] :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) :=
  Scheme.exists_isIso_restrict_of_isProper_birational_at_valuationRing f hf y

-- The original DVR-recognition consumer accepts the supplier directly.
example {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (z₀ : Y) [IsDiscreteValuationRing (Y.presheaf.stalk z₀)]
    (hdvr : ∀ z : Y, z ≠ genericPoint Y →
      IsDiscreteValuationRing (Y.presheaf.stalk z)) : IsIso f :=
  Scheme.Hom.isIso_of_dvr_off_generic Scheme.properBirationalDVRIsomorphismLocus
    f hf z₀ hdvr
