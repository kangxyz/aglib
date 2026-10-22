/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty

/-!
# Blowups with an explicit protected open

Admissibility is expressed by the equality of the restricted centre ideal with
the unit ideal, not by another bundled modification object. The resulting
isomorphism has the literal restricted blowup morphism as its forward map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.BlowupDatum

variable {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)

/-- A blowup is unchanged over any open where its actual centre is the unit ideal. -/
theorem restrict_isIso_of_comap_eq_top (U : X.Opens) (hI : I.comap U.ι = ⊤) :
    IsIso (B.map ∣_ U) := by
  let : IsIso (pullback.snd B.map U.ι) :=
    B.pullback_snd_isIso_of_comap_eq_top U.ι hI
  rw [← (isPullback_morphismRestrict B.map U).flip.isoPullback_hom_snd]
  infer_instance

/-- The protected-open identification for an admissible native blowup datum. -/
def restrictIsoOfComapEqTop (U : X.Opens) (hI : I.comap U.ι = ⊤) :
    (B.map ⁻¹ᵁ U).toScheme ≅ U.toScheme := by
  let := B.restrict_isIso_of_comap_eq_top U hI
  exact asIso (B.map ∣_ U)

@[simp]
theorem restrictIsoOfComapEqTop_hom (U : X.Opens) (hI : I.comap U.ι = ⊤) :
    (B.restrictIsoOfComapEqTop U hI).hom = B.map ∣_ U := rfl

/-- The protected-open identification commutes with the ambient structural map. -/
@[reassoc]
theorem restrictIsoOfComapEqTop_hom_ι (U : X.Opens) (hI : I.comap U.ι = ⊤) :
    (B.restrictIsoOfComapEqTop U hI).hom ≫ U.ι = (B.map ⁻¹ᵁ U).ι ≫ B.map :=
  morphismRestrict_ι B.map U

end AlgebraicGeometry.Scheme.Blowup.BlowupDatum
