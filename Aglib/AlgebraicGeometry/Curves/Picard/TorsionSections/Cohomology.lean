/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.TorsionSections
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula

/-! # Actual zeroth cohomology detects degree-zero triviality

Positive dimension of the original module cohomology gives an actual nonzero
section through the native H0 comparison. The regular-curve section criterion
then trivializes the actual bundle. Proper geometrically integral constants
identify its H0 with the original ground field, so the dimension is exactly one.
These statements work over arbitrary fields and use no higher-cohomology
vanishing, Picard representability, torsion-finiteness or base-change premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.TorsionSections

open DivisorClass Degree

variable {k : Type u} [Field k] (X : FScheme k)

/-- An actual trivialization identifies original H0 with the ground field when
its structural constants map is bijective. -/
def lineBundleH0ConstantsEquiv (hc : Function.Bijective (constants X))
    (L : LineBundle X.left) (e : L.val ≅ SheafOfModules.unit X.left.ringCatSheaf) :
    moduleCohomology k X L.val 0 ≃ₗ[k] k :=
  (moduleCohomologyIso X e 0).trans (structureModuleH0ConstantsEquiv X hc)

/-- The original H0 dimension of a trivial bundle is one, not an assumed
rank and not a statement about any positive cohomological degree. -/
theorem lineBundle_h0_finrank_eq_one_of_trivial
    (hc : Function.Bijective (constants X)) (L : LineBundle X.left)
    (he : Nonempty (L.val ≅ SheafOfModules.unit X.left.ringCatSheaf)) :
    Module.finrank k (moduleCohomology k X L.val 0) = 1 := by
  obtain ⟨e⟩ := he
  rw [(lineBundleH0ConstantsEquiv X hc L e).finrank_eq, Module.finrank_self]

variable [IsIntegral X.left] [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

/-- Positive original H0 dimension produces an actual nonzero section and an
actual trivialization of a degree-zero line bundle. -/
theorem lineBundle_trivial_of_pos_h0_finrank
    (hdim : topologicalKrullDim X.left ≤ 1) (hprod : PrincipalProductFormula X.left X.hom)
    (L : LineBundle X.left) (hdegree : lineBundleDegree X.left X.hom hdim hprod L = 0)
    (hpos : 0 < Module.finrank k (moduleCohomology k X L.val 0)) :
    Nonempty (L.val ≅ SheafOfModules.unit X.left.ringCatSheaf) := by
  let : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  apply lineBundle_trivial_of_nonzero_section X.left X.hom hdim hprod L hdegree
    (moduleH0Equiv X L.val s)
  intro hz
  exact hs ((moduleH0Equiv X L.val).injective
    (hz.trans (moduleH0Equiv X L.val).map_zero.symm))

/-- Original H0 nonvanishing detects actual degree-zero triviality over any
field for which the structural constants map is bijective. -/
theorem lineBundle_pos_h0_finrank_iff_trivial
    (hdim : topologicalKrullDim X.left ≤ 1) (hprod : PrincipalProductFormula X.left X.hom)
    (hc : Function.Bijective (constants X)) (L : LineBundle X.left)
    (hdegree : lineBundleDegree X.left X.hom hdim hprod L = 0) :
    0 < Module.finrank k (moduleCohomology k X L.val 0) ↔
      Nonempty (L.val ≅ SheafOfModules.unit X.left.ringCatSheaf) := by
  refine ⟨lineBundle_trivial_of_pos_h0_finrank X hdim hprod L hdegree, ?_⟩
  intro h
  rw [lineBundle_h0_finrank_eq_one_of_trivial X hc L h]
  exact Nat.zero_lt_one

/-- On the nonvanishing locus the actual degree-zero bundle has H0 dimension
exactly one. -/
theorem lineBundle_h0_finrank_eq_one_of_pos
    (hdim : topologicalKrullDim X.left ≤ 1) (hprod : PrincipalProductFormula X.left X.hom)
    (hc : Function.Bijective (constants X)) (L : LineBundle X.left)
    (hdegree : lineBundleDegree X.left X.hom hdim hprod L = 0)
    (hpos : 0 < Module.finrank k (moduleCohomology k X L.val 0)) :
    Module.finrank k (moduleCohomology k X L.val 0) = 1 :=
  lineBundle_h0_finrank_eq_one_of_trivial X hc L
    (lineBundle_trivial_of_pos_h0_finrank X hdim hprod L hdegree hpos)

section ProperGeometricallyIntegral

variable [IsProper X.hom] [GeometricallyIntegral X.hom]

omit [LocallyOfFiniteType X.hom] in
/-- Proper geometrically integral constants supply the dimension-one theorem
without an algebraically closed field or a constants-map hypothesis. -/
theorem lineBundle_h0_finrank_eq_one_of_pos_of_proper
    (hdim : topologicalKrullDim X.left = 1) (L : LineBundle X.left)
    (hdegree : lineBundleDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0)
    (hpos : 0 < Module.finrank k (moduleCohomology k X L.val 0)) :
    Module.finrank k (moduleCohomology k X L.val 0) = 1 :=
  lineBundle_h0_finrank_eq_one_of_pos X hdim.le
    (properCurveProductFormula k X.left X.hom hdim)
    (constants_bijective_of_proper_geometricallyIntegral X) L hdegree hpos

omit [LocallyOfFiniteType X.hom] in
/-- The proper geometrically integral criterion uses the original H0, the
actual degree and an actual module-sheaf isomorphism. -/
theorem lineBundle_pos_h0_finrank_iff_trivial_of_proper
    (hdim : topologicalKrullDim X.left = 1) (L : LineBundle X.left)
    (hdegree : lineBundleDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    0 < Module.finrank k (moduleCohomology k X L.val 0) ↔
      Nonempty (L.val ≅ SheafOfModules.unit X.left.ringCatSheaf) :=
  lineBundle_pos_h0_finrank_iff_trivial X hdim.le
    (properCurveProductFormula k X.left X.hom hdim)
    (constants_bijective_of_proper_geometricallyIntegral X) L hdegree

end ProperGeometricallyIntegral

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.TorsionSections
