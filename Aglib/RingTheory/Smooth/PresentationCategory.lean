/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Smooth/PresentationCategory.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ce78f98e406393e8fd15eaa25d1a8d8a467643ef36c35c9fcbff8c4a9e348ced`.
-/

@[expose] public section

open CategoryTheory
namespace CommAlgCat
universe u
variable (F : Type u) [CommRing F]

/-- The actual full subcategory of smooth finitely presented F-algebras. -/
def smoothProperty : ObjectProperty (CommAlgCat.{u} F) :=
  fun A => Algebra.Smooth F A

abbrev SmoothAlgebra := (smoothProperty F).FullSubcategory
abbrev smoothInclusion : SmoothAlgebra F ⥤ CommAlgCat.{u} F :=
  (smoothProperty F).ι

/-- All smooth presentations of R, with their actual commuting algebra maps. -/
abbrev smoothPresentations (R : CommAlgCat.{u} F) :=
  CostructuredArrow (smoothInclusion F) R

end CommAlgCat
