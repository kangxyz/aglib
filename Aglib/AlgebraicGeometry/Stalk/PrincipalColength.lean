/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.StalkScalars
public import Aglib.RingTheory.Length.ResidueDimension
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# PrincipalColength

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.PrincipalColength`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `10d81d0f488e8bd3998f4620a33da45a3ca270dc5c9f4c956801cb9454cde23e`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing
namespace AlgebraicGeometry.Scheme
section StalkColength

universe u
variable (X : Scheme.{u})

/-- Actual colength of a principal ideal in the actual scheme stalk. -/
def stalkColength (x : X) (a : X.presheaf.stalk x) : ℕ :=
  (Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸ Ideal.span {a})).toNat

variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
variable [IsIntegral X] [IsNoetherian X]

/-- A nonzero principal quotient at a codimension-one closed point is finite over `k`. -/
theorem stalkQuotient_finite (x : X) (hx : IsClosed ({x} : Set X))
    (hcodim : Order.coheight x = 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    let := stalkConstantsAlgebra X p x
    Module.Finite k (X.presheaf.stalk x ⧸ Ideal.span {a}) := by
  let := stalkConstantsAlgebra X p x
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hcodim.le
  let : Module.Finite k (ResidueField (X.presheaf.stalk x)) :=
    residue_finite_from_stalk X p x hx
  exact Module.finite_over_field_of_finite_local_length k (X.presheaf.stalk x) _
    (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_iff_ne_zero.mpr ha))

/-- The actual principal stalk quotient has residue-weighted colength dimension. -/
theorem stalkQuotient_finrank (x : X) (hx : IsClosed ({x} : Set X))
    (hcodim : Order.coheight x = 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    let := stalkConstantsAlgebra X p x
    let := residueAlgebraFromStalk X p x
    Module.finrank k (X.presheaf.stalk x ⧸ Ideal.span {a}) =
      stalkColength X x a * Module.finrank k (X.residueField x) := by
  let := stalkConstantsAlgebra X p x
  let := residueAlgebraFromStalk X p x
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hcodim.le
  let : Module.Finite k (ResidueField (X.presheaf.stalk x)) :=
    residue_finite_from_stalk X p x hx
  exact Module.finrank_eq_local_length_mul_residue_finrank k (X.presheaf.stalk x) _
    (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_iff_ne_zero.mpr ha))

end StalkColength
end AlgebraicGeometry.Scheme
