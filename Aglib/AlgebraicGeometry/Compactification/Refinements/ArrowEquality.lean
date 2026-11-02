/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Category

/-! # Equality transport retaining the literal compactification fields -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification
variable {X S : Scheme.{u}} {f g : X ⟶ S} (e : f = g)

/-- Equality of structural arrows changes only the factorization proof. -/
def ofArrowEq (C : DenseCompactification f) : DenseCompactification g where
  Xbar := C.Xbar
  j := C.j
  p := C.p
  isOpenImmersion_j := C.toCompactification.isOpenImmersion_j
  isProper_p := C.toCompactification.isProper_p
  fac := C.fac.trans e
  isSchemeTheoreticallyDominant_j := C.isSchemeTheoreticallyDominant_j

/-- Literal-field transport is the original equality transport, not an alternative choice. -/
theorem ofArrowEq_eq_cast (C : DenseCompactification f) :
    ofArrowEq e C = Eq.mp (congrArg DenseCompactification e) C := by
  subst g
  rfl

/-- The equality transport keeps original refinement maps unchanged. -/
def arrowEq : DenseCompactification f ⥤ DenseCompactification g where
  obj := ofArrowEq e
  map a :=
    { hom := a.hom
      isProper_hom := a.isProper_hom
      open_fac := a.open_fac
      base_fac := a.base_fac }
  map_id _ := rfl
  map_comp _ _ := rfl

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
