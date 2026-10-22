/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.ClosedIdentification
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Actual schematic-image comparison under an ambient map

A commuting triangle of quasi-compact maps induces a map of their actual
schematic images. Properness of the new ambient scheme over a base and
separatedness of the old one make this comparison proper and surjective.
No commutation of schematic image with arbitrary base change is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme

variable {U P' P : Scheme.{u}} (f' : U ⟶ P') (f : U ⟶ P)
    (β : P' ⟶ P) (w : f' ≫ β = f) [QuasiCompact f'] [QuasiCompact f]

/-- The actual comparison of schematic images induced by an ambient triangle. -/
def imageComparison : f'.image ⟶ f.image := by
  let : IsSchemeTheoreticallyDominant f'.toImage :=
    isSchemeTheoreticallyDominant_toImage f'
  let : IsSchemeTheoreticallyDominant f.toImage :=
    isSchemeTheoreticallyDominant_toImage f
  have hw : f.toImage ≫ f.imageι = f'.toImage ≫ (f'.imageι ≫ β) := by
    simpa only [Hom.toImage_imageι, Hom.toImage_imageι_assoc] using w.symm
  exact IsClosedImmersion.lift f.imageι (f'.imageι ≫ β)
    (ker_eq_of_common_schematicallyDense_source f.imageι (f'.imageι ≫ β)
      f.toImage f'.toImage hw).le

@[reassoc (attr := simp)]
lemma imageComparison_imageι : imageComparison f' f β w ≫ f.imageι = f'.imageι ≫ β :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma toImage_imageComparison : f'.toImage ≫ imageComparison f' f β w = f.toImage := by
  apply (cancel_mono f.imageι).mp
  rw [Category.assoc, imageComparison_imageι, Hom.toImage_imageι_assoc,
    Hom.toImage_imageι]
  exact w

/-- The comparison is proper whenever its source ambient scheme is proper
over the base and its target ambient scheme is separated over that base. -/
theorem imageComparison_isProper {S : Scheme.{u}} (p' : P' ⟶ S) (p : P ⟶ S)
    [IsProper p'] [IsSeparated p] (hβ : β ≫ p = p') :
    IsProper (imageComparison f' f β w) := by
  let : IsProper (imageComparison f' f β w ≫ (f.imageι ≫ p)) := by
    rw [← Category.assoc, imageComparison_imageι, Category.assoc, hβ]
    infer_instance
  exact IsProper.of_comp _ (f.imageι ≫ p)

/-- A proper image comparison is surjective because its image contains the
original dense image factor. -/
theorem imageComparison_surjective [IsProper (imageComparison f' f β w)] :
    Surjective (imageComparison f' f β w) := by
  have : IsDominant (f'.toImage ≫ imageComparison f' f β w) := by
    rw [toImage_imageComparison]
    infer_instance
  let : IsDominant (imageComparison f' f β w) := IsDominant.of_comp f'.toImage _
  exact surjective_of_isDominant_of_isClosed_range _
    (imageComparison f' f β w).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme
