/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Quasi-compact schemes with all scheme morphisms

This full subcategory restricts objects only. Its morphisms have no flatness,
separatedness or quasi-compactness premise.
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/QuasiCompact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 37]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section


universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- Quasi-compactness of a scheme, with no restriction on its morphisms. -/
abbrev quasiCompactSchemeProperty : ObjectProperty AlgebraicGeometry.Scheme.{u} :=
  fun X => CompactSpace X

/-- Quasi-compact schemes with all scheme morphisms. -/
abbrev QuasiCompactSchemes := quasiCompactSchemeProperty.{u}.FullSubcategory

instance quasiCompactSchemes_compactSpace (X : QuasiCompactSchemes.{u}) :
    CompactSpace X.obj := X.property

/-- The full-subcategory inclusion of quasi-compact schemes into all schemes. -/
abbrev quasiCompactSchemesInclusion : QuasiCompactSchemes.{u} ⥤ AlgebraicGeometry.Scheme.{u} :=
  quasiCompactSchemeProperty.{u}.ι

end AlgebraicGeometry.Scheme
