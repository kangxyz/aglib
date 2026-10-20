/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.DivisorIndependence`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`9ea8b9d44dc7bab268dd8f976590e73a1bbd1404f703dce59cdbd6e51145685c`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle classOf_tensorPower tensorPowerLineBundle)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Independence of generic trivialization and tensor-power degree

C2 exported consequences, K2-018 `lem:k2018-geometric-exact-order`, frozen
basis `7f86e4a`. The divisors constructed from any two nonempty generic
trivializing charts of the same actual line bundle have equal divisor classes;
their difference is an actual principal divisor. This follows from the two
constructed O(D) isomorphisms and the proved divisor/Picard equivalence.
Their residue-weighted degrees agree under the existing principal product
formula. The degree of an actual tensor power is n times the degree.
No additional standard input or comparison premise is introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorIndependence
open DivisorClass RationalTrivialization
universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (M : SheafOfModules.{u} X.ringCatSheaf) (hM : IsLocallyRankOne X M)
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (eU : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
variable (eV : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))

include hdim in
/-- Actual generic-chart divisors have the same class in the divisor quotient. -/
theorem rationalDivisor_class_eq :
    (QuotientAddGroup.mk (divisor X M U eU hM) : Divisor X ⧸ (principal X).range) =
      QuotientAddGroup.mk (divisor X M V eV hM) := by
  apply (divisorPicardEquiv X hdim).injective
  simp only [divisorPicardEquiv_mk]
  exact Quotient.sound
      ⟨(AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorInverse.toDivisorIso X M hM U eU
      hdim).symm ≪≫
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorInverse.toDivisorIso X M hM V eV hdim⟩

include hdim in
/-- With the displayed orientation, D_U-D_V is the divisor of an actual rational unit. -/
theorem rationalDivisor_sub_principal : ∃ g : X.functionFieldˣ,
    principal X (Additive.ofMul g) = divisor X M U eU hM - divisor X M V eV hM := by
  have he : (QuotientAddGroup.mk (divisor X M U eU hM - divisor X M V eV hM) :
      Divisor X ⧸ (principal X).range) = 0 := by
    change (QuotientAddGroup.mk' (principal X).range) (_ - _) = 0
    rw [map_sub]
    change (QuotientAddGroup.mk (divisor X M U eU hM) : Divisor X ⧸ (principal X).range) -
      QuotientAddGroup.mk (divisor X M V eV hM) = 0
    rw [rationalDivisor_class_eq X hdim M hM U V eU eV, sub_self]
  obtain ⟨g, hg⟩ := (QuotientAddGroup.eq_zero_iff _).mp he
  exact ⟨g.toMul, hg⟩

variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
variable (hprod :
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula X p)

include hdim hprod in
/-- Residue-weighted degree is independent of the chosen generic trivializing chart. -/
theorem rationalDivisor_degree_eq :
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.degDiv X p (divisor X M U eU hM) =
        AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.degDiv X p (divisor X M V eV hM) :=
  congrArg (AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.divisorClassDegree X p hprod)
    (rationalDivisor_class_eq X hdim M hM U V eU eV)

/-- Every constructed generic-chart divisor computes the actual line-bundle degree. -/
theorem rationalDivisor_degree :
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.degDiv X p (divisor X M U eU hM) =
      AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.lineBundleDegree X p hdim hprod
          (⟨M, hM⟩ : LineBundle X) := by
  rw [← AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.lineBundleDegree_divisor X p
      hdim hprod]
  exact (AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.lineBundleDegree_iso X p hdim hprod
    (L := (⟨M, hM⟩ : LineBundle X))
    (N := divisorLineBundle X hdim (divisor X M U eU hM))
    (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorInverse.toDivisorIso X M hM U eU
        hdim)).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorIndependence

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X]
variable [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (p : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
variable (hprod : PrincipalProductFormula X p)

/-- Degree of the actual nth tensor power, including n=0. -/
@[simp] theorem lineBundleDegree_tensorPower (L : LineBundle X) (n : ℕ) :
    lineBundleDegree X p hdim hprod (tensorPowerLineBundle X L n) =
      (n : ℤ) * lineBundleDegree X p hdim hprod L := by
  unfold lineBundleDegree
  rw [classOf_tensorPower, map_nsmul, nsmul_eq_mul]

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
