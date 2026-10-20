/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.PrincipalColength
public import Aglib.AlgebraicGeometry.ResidueField.StalkScalars
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeLength
public import Aglib.RingTheory.Artinian.FiniteAlgebra
public import Aglib.RingTheory.Length.ResidueDimension
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Local colengths and residue-weighted dimensions

These independent B04 constructions concern the actual stalks, structural
constants maps, and finite coordinate algebras used by `ProperCurveProductFormula`
and `Abel.FiniteCartierIdealDegree`. The local comparisons do not require regular
or DVR stalks. The finite algebra calculation allows nilpotents and multiple
points; it uses maximal-ideal-power factors rather than a reduced product of
fields.

Input basis: `Picard/Degree.lean:117` and `Abel/Degree.lean:71`, at entry
`f1a725686388bcc5d2eb9c9ec0971d7400cf4c7a`, unchanged through the disjoint handoff
commit `914476dd55baa6feaef45710e946922ea011eb0c`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This file supplies the algebraic and scalar-map components. It does not assert
proper coherent cohomology finiteness, the finite-support sheaf Euler comparison,
or either remaining universal family.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.FiniteSupportLengths



section StalkScalars
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
/-- The existing divisor weight uses exactly the stalk-induced residue scalars. -/
theorem weight_eq_residue_finrank (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := stalkConstantsAlgebra X p x
    letI := residueAlgebraFromStalk X p x
    Degree.weight X p ⟨x, hx⟩ = (Module.finrank k (X.residueField x) : ℤ) := by
  let := stalkConstantsAlgebra X p x
  let := residueAlgebraFromStalk X p x
  unfold Degree.weight
  rw [residueAlgebra_eq_stalk X p x]

end StalkScalars


section StalkColength
universe u
variable (X : Scheme.{u})
variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
variable [IsIntegral X] [IsNoetherian X]
/-- The exact integer weight used by the existing divisor degree appears in the dimension. -/
theorem stalkQuotient_finrank_eq_weight_mul_colength
    (x : X) (hx : IsClosed ({x} : Set X)) (hcodim : Order.coheight x = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    letI := stalkConstantsAlgebra X p x
    (Module.finrank k (X.presheaf.stalk x ⧸ Ideal.span {a}) : ℤ) =
      (stalkColength X x a : ℤ) * Degree.weight X p ⟨x, hx⟩ := by
  let := stalkConstantsAlgebra X p x
  let := residueAlgebraFromStalk X p x
  rw [weight_eq_residue_finrank X p x hx, stalkQuotient_finrank X p x hx hcodim a ha]
  exact Nat.cast_mul _ _

end StalkColength






end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.FiniteSupportLengths
