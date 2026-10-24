/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Fppf

/-!
# Sections of the fppf Picard sheaf

For a morphism of schemes `p : X ⟶ S`, the sheafification unit
`toFppfPicardSheaf p : P_{X/S} ⟶ Pic_{X/S,(fppf)}` of [Fppf](Fppf.lean) is locally injective
(`toFppfPicardSheaf_isLocallyInjective`) and locally surjective
(`toFppfPicardSheaf_isLocallySurjective`) for `Scheme.fppfTopology.over S`; these are Mathlib's
`Presheaf.isLocallyInjective_toSheafify'` and `Presheaf.isLocallySurjective_toSheafify'`, stated as
instances because `toFppfPicardSheaf` is not reducible. So every section of `Pic_{X/S,(fppf)}` is
fppf-locally the image of a class, and two classes with the same image agree in `P_{X/S}`
fppf-locally. The underlying presheaf of sets `(fppfPicardSheaf p).obj ⋙ forget AddCommGrpCat` is
an fppf sheaf (`isSheaf_fppfPicardSheaf_forget`). No hypothesis on `p` is used.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The sheafification unit `P_{X/S} ⟶ Pic_{X/S,(fppf)}` is locally injective. -/
instance toFppfPicardSheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (toFppfPicardSheaf p) :=
  Presheaf.isLocallyInjective_toSheafify' (J := Scheme.fppfTopology.over S)
    (relativePicardFunctor p)

/-- The sheafification unit `P_{X/S} ⟶ Pic_{X/S,(fppf)}` is locally surjective
(Mathlib's `Presheaf.isLocallySurjective_toSheafify'`). -/
instance toFppfPicardSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (toFppfPicardSheaf p) :=
  Presheaf.isLocallySurjective_toSheafify' (J := Scheme.fppfTopology.over S)
    (relativePicardFunctor p)

/-- The underlying presheaf of sets of `Pic_{X/S,(fppf)}` is an fppf sheaf. -/
theorem isSheaf_fppfPicardSheaf_forget :
    Presieve.IsSheaf (Scheme.fppfTopology.over S)
      ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose (Scheme.fppfTopology.over S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (fppfPicardSheaf p)).property

end AlgebraicGeometry.Scheme.RelativePicard
