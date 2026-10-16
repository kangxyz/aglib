/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Strict-perfect closure under shifts and cones

The proofs retain explicit bounds on terms. Cone terms are finite biproducts
of vector bundles, so no global projectivity assumption is required.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Closure.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `f00f011637c12cdae0c63d884912fd2c4bb7addcaa3eeb5b398bacf853b029b9`.
Admitted subset: strictPerfect_shift and strictPerfect_mappingCone.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable {X : Scheme.{u}} {P Q : CochainComplex X.Modules ℤ}

/-- Every integer shift of a strict-perfect complex is strict perfect. -/
theorem strictPerfect_shift (hP : strictPerfect X P) (n : ℤ) :
    strictPerfect X ((shiftFunctor (CochainComplex X.Modules ℤ) n).obj P) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hP
  constructor
  · refine ⟨a - n, b - n, fun j hj => ?_⟩
    change IsZero (P.X (j + n))
    exact hb (j + n) (by omega)
  · intro j
    exact hv (j + n)

/-- The actual mapping cone of a map between strict-perfect complexes is
strict perfect, regardless of whether the map is a cofibration. -/
theorem strictPerfect_mappingCone (hP : strictPerfect X P) (hQ : strictPerfect X Q)
    (f : P ⟶ Q) : strictPerfect X (CochainComplex.mappingCone f) := by
  obtain ⟨⟨a, b, hbP⟩, hvP⟩ := hP
  obtain ⟨⟨c, d, hbQ⟩, hvQ⟩ := hQ
  constructor
  · refine ⟨min (a - 1) c, max (b - 1) d, fun j hj => ?_⟩
    apply (CochainComplex.mappingCone.isZero_X_iff f j).2
    exact ⟨hbP (j + 1) (by omega), hbQ j (by omega)⟩
  · intro j
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f j (j + 1) rfl
    apply (finiteLocallyFree_iff_of_iso e).2
    exact (sheafExactStructure X).prop_biprod
      (finiteLocallyFree X) (hvP (j + 1)) (hvQ j)
end AlgebraicGeometry.Scheme.Modules.Complex
