/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatPullback
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.FieldBaseChange

/-!
# SimplexFieldPullback for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `SimplexFieldPullback.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9f6c006f3353c87995a047c2ed901b976b5b0e6c922fa767dd4852da5acdc327`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
universe u
variable {K L : Type u} [Field K] [Field L]

/-- Pullback of ordinary finite dominant prime cycles along the literal
field-coefficient map on the j-simplex, in every degree j. -/
def simplexFieldPullback (f : K →+* L) (j : ℕ) :
    FreeAbelianGroup (FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K j)) →+
      FreeAbelianGroup (FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L j)) := by
  let := (AlgebraicSimplex.coefficientMap f j).toAlgebra
  let : Module.Flat (AlgebraicSimplex.CoordinateRing K j)
    (AlgebraicSimplex.CoordinateRing L j) := AlgebraicSimplex.coefficientMap_flat f j
  exact flatPullback

/-- Actual original objects have their full finite cycle transported by the
constructed literal field-extension operator in every simplex degree. -/
theorem simplexObjectCycle_field_baseChange (f : K →+* L) (j : ℕ)
    (X : Object (AlgebraicSimplex.CoordinateRing K j)) :
    let := (AlgebraicSimplex.coefficientMap f j).toAlgebra
    objectCycle (X.baseChange (AlgebraicSimplex.CoordinateRing L j)) =
      simplexFieldPullback f j (objectCycle X) := by
  let := (AlgebraicSimplex.coefficientMap f j).toAlgebra
  let : Module.Flat (AlgebraicSimplex.CoordinateRing K j)
    (AlgebraicSimplex.CoordinateRing L j) := AlgebraicSimplex.coefficientMap_flat f j
  exact objectCycle_flat_baseChange X

end AlgebraicGeometry.Torus.FiniteCorrespondence
