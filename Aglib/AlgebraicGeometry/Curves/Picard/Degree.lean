/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/



/-!
# Residue-field weighted degree on actual divisors

C2 degree foundation, K2-018 `lem:k2018-geometric-exact-order`, frozen basis
`7f86e4a`. Residue scalars come from the actual composite
`Spec κ(x) → X → Spec k`. Finite-dimensionality at closed points is proved
from local finite type. The proper-curve product formula is a separately named
standard premise on the constructed orders: Stacks Tag 02RU, Lemma 42.18.3
(checked 2026-10-09 at https://stacks.math.columbia.edu/tag/02RU).
No identification with line-bundle Picard classes is asserted in this module.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))

/-- Integer-valued residue-field weight of an actual closed point. -/
def weight (x : ClosedPoint X) : ℤ :=
  letI := residueAlgebra X p x.val
  Module.finrank k (X.residueField x.val)

/-- The finite residue-weighted sum defining divisor degree. -/
def degDiv : Divisor X →+ ℤ :=
  (Finsupp.linearCombination ℤ (weight X p)).toAddMonoidHom

@[simp] theorem degDiv_single (x : ClosedPoint X) (m : ℤ) :
    degDiv X p (Finsupp.single x m) = m * weight X p x := by
  simp [degDiv]

/-- Expanded finite-sum formula, with each actual residue-field degree visible. -/
theorem degDiv_apply (D : Divisor X) :
    degDiv X p D = ∑ x ∈ D.support, D x * weight X p x := by
  simp [degDiv, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Over algebraically closed constants every actual closed-point weight is one. -/
theorem weight_eq_one [IsAlgClosed k] [LocallyOfFiniteType p] (x : ClosedPoint X) :
    weight X p x = 1 := by
  let := residueAlgebra X p x.val
  have hb : Function.Bijective (algebraMap k (X.residueField x.val)) := by
    change Function.Bijective (residueFieldIsoBase p x.val x.property).inv
    exact ConcreteCategory.bijective_of_isIso _
  simpa [weight] using congrArg (fun n : ℕ => (n : ℤ))
    (Module.finrank_of_bijective_algebraMap hb)

variable [IsIntegral X] [IsNoetherian X]

/-- The exact proper-curve local-order product formula used for descent.
This is a named conditional input, not an asserted theorem. The associated
application must also supply properness and dimension one.
Source: Stacks Tag 02RU, Lemma 42.18.3. This local predicate is the
conclusion of that theorem; `ProperCurveProductFormula` below states its full
universal geometric hypotheses. -/
def PrincipalProductFormula : Prop :=
  ∀ f : X.functionFieldˣ, degDiv X p (principal X (Additive.ofMul f)) = 0

/-- Degree descends through the constructed principal-divisor subgroup. -/
def divisorClassDegree (hprod : PrincipalProductFormula X p) :
    (Divisor X ⧸ (principal X).range) →+ ℤ :=
  QuotientAddGroup.lift _ (degDiv X p) (by
    rintro _ ⟨f, rfl⟩
    exact hprod f.toMul)

@[simp] theorem divisorClassDegree_mk (hprod : PrincipalProductFormula X p) (D : Divisor X) :
    divisorClassDegree X p hprod (QuotientAddGroup.mk D) = degDiv X p D := rfl

/-- Positive-level torsion in the full divisor class group has degree zero. -/
theorem torsion_degree_zero (hprod : PrincipalProductFormula X p) (n : ℕ) (hn : 0 < n)
    (L : Divisor X ⧸ (principal X).range) (hL : n • L = 0) :
    divisorClassDegree X p hprod L = 0 := by
  have h := congrArg (divisorClassDegree X p hprod) hL
  rw [map_nsmul, map_zero] at h
  exact (nsmul_right_injective (ne_of_gt hn)) h

/-- Full universal standard theorem boundary: Stacks Tag 02RU, Lemma 42.18.3.
It quantifies over actual schemes, residue fields, and the constructed local
orders. The theorem itself remains an explicit premise, not a global axiom. -/
def ProperCurveProductFormula : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (q : Y ⟶ Spec (.of k)) [IsProper q],
    topologicalKrullDim Y = 1 → PrincipalProductFormula Y q

/-- Apply the universal proper-curve theorem to the actual degree construction. -/
theorem principalProductFormula_of_proper
    (hstandard : ProperCurveProductFormula.{u}) [IsProper p]
    (hdim : topologicalKrullDim X = 1) : PrincipalProductFormula X p :=
  hstandard k X p hdim

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
