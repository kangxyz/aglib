/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Category
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic

/-!
# Uniqueness of dense compactification refinements

The existing schematic-density extensionality theorem for a relatively separated
target applies to the original open and base triangles. It does not require
reducedness or quasi-compactness of the dense source map.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A refinement is determined by its restriction to the original schematically
dense source and its structural morphism. -/
instance (C D : DenseCompactification f) : Subsingleton (C ⟶ D) where
  allEq a b := Refinement.ext <|
    Scheme.QuasiDomination.hom_ext_of_schemeTheoreticallyDominant C.j D.p
      (a.base_fac.trans b.base_fac.symm) (a.open_fac.trans b.open_fac.symm)

/-- The identity refinement equalizes any pair of parallel refinements. -/
lemma id_comp_eq {C D : DenseCompactification f} (a b : C ⟶ D) :
    𝟙 C ≫ a = 𝟙 C ≫ b :=
  Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
