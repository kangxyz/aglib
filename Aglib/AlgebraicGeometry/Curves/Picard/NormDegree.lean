/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Norm
public import Aglib.AlgebraicGeometry.Curves.Divisors.Pullback
public import Aglib.AlgebraicGeometry.Curves.Picard.PullbackDegree
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle PicardGroup classOf pullbackClass pullbackLineBundle)

/-!
# Finite-map divisor and line-bundle degree from the actual norm/order formula

C2 numerical functoriality, K2-018 `lem:k2018-geometric-exact-order`, frozen
basis `7f86e4a`. The explicit standard input `FiniteMorphismNormOrder` is a
universal geometric corollary of Stacks Tag 02MJ, Lemma 10.121.8, inspected
2026-10-09 at https://stacks.math.columbia.edu/tag/02MJ. Its literal algebraic
statement assumes a Noetherian local domain A of dimension one and a finite
domain extension A ⊂ B, and sums the length orders over every maximal ideal
of semilocal B, with actual residue degrees. Separability, etaleness and
absolute properness are not hypotheses of that formula.

The retained GEOMETRIC corollary includes the following source-applicability
obligations. They are disclosed standard background, not Lean proofs here:
1. For y, A = O_{Y,y} and B = Γ(X ×_Y Spec A,O) (the FULL inverse image) is a
   finite domain extension, rather than replacing B by a single X stalk.
2. Generic restriction identifies Frac(B) with X.functionField, its extension
   with Scheme.functionFieldMap f, and its determinant norm with Algebra.norm.
3. Maximal ideals of this semilocal B are in bijection with ALL actual fibre
   points over y, with no omitted branch.
4. Their localizations and residue maps identify with actual X stalks and
   f.residueFieldMap; the length-defined orders identify with Scheme.ord.
The closed-DVR assumptions supply the needed local dimension-one property.

The family contains no divisor-degree or Picard-degree assertion. Applying
it to an actual pulled-back uniformizer proves the ramification/residue sum.
Actual residue-field scalar towers and finite residue dimensions from finite
type prove weight multiplication. Finite summation then proves divisor
pullback degree. The independently proved O(D) pullback isomorphism and
constructive divisor/Picard equivalence yield actual line-bundle scaling.
The principal product formulas used to define Picard degrees remain the
separate explicit inputs of Degree.lean; no properness is silently inferred.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.NormDegree
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable [hNX : AlgebraicGeometry.IsNoetherian X]
variable [hNY : AlgebraicGeometry.IsNoetherian Y]
variable (f : X ⟶ Y) [hDom : IsDominant f] [hFin : IsFinite f]

/-- Precise geometric norm/order corollary of Stacks 02MJ. See the module
header for the four retained full-semilocal realization obligations. -/
def FiniteMorphismNormOrder : Prop :=
  ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (_ : topologicalKrullDim X ≤ 1) (_ : topologicalKrullDim Y ≤ 1)
    (f : X ⟶ Y) [IsDominant f] [IsFinite f],
    letI := Scheme.functionFieldMapAlgebra f
    Module.Finite Y.functionField X.functionField →
    ∀ (z : X.functionFieldˣ) (y : ClosedPoint Y),
      Y.ord (fieldNorm f z) y.val =
        ∑ x : ClosedFibre f y, residueDegreeInt f x.val * X.ord (z : X.functionField) x.val.val

variable [hDX : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable [hDY : ∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]

theorem ramification_residue_sum (h : FiniteMorphismNormOrder.{u})
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hfin : letI := Scheme.functionFieldMapAlgebra f; Module.Finite Y.functionField X.functionField)
    (y : ClosedPoint Y) :
    ∑ x : ClosedFibre f y, Pullback.ramification f x.val * residueDegreeInt f x.val = fieldDegree f
      := by
  letI := Scheme.functionFieldMapAlgebra f
  have hn := h X Y hdimX hdimY f hfin (Scheme.functionFieldUnitMap f
    (Pullback.uniformizerUnit y)) y
  have hnmap : fieldNorm f (Scheme.functionFieldUnitMap f (Pullback.uniformizerUnit y)) =
      (Pullback.uniformizerUnit y : Y.functionField) ^ fieldDegree f :=
    Algebra.norm_algebraMap _
  rw [hnmap] at hn
  have ho : Y.ord ((Pullback.uniformizerUnit y : Y.functionField) ^ fieldDegree f) y.val =
    fieldDegree f := by
    change localOrder Y y (Additive.ofMul (Pullback.uniformizerUnit y ^ fieldDegree f)) = _
    rw [ofMul_pow, map_nsmul]
    change (fieldDegree f : ℤ) * Y.ord (Pullback.uniformizerUnit y : Y.functionField) y.val = _
    rw [Pullback.uniformizerUnit_order, mul_one]
  rw [ho] at hn
  rw [hn]
  apply Finset.sum_congr rfl
  intro x _
  rw [Pullback.order_fieldMap, x.property, Pullback.uniformizerUnit_order, mul_one, mul_comm]

variable {k : Type u} [Field k] (p : Y ⟶ Spec (.of k))

omit hNX hNY hDom hFin hDX hDY in
-- Retain finite dominance and the noetherian DVR-curve conditions for the residue-degree norm
-- interface; this scalar triangle is functoriality of the actual residue-field maps.
@[nolint unusedArguments]
theorem residueConstants_comp [IsNoetherian X] [IsNoetherian Y]
    [IsDominant f] [IsFinite f]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (x : ClosedPoint X) :
    ((f.residueFieldMap x.val).hom).comp (AlgebraicGeometry.Scheme.residueConstants Y p (f x.val)) =
      AlgebraicGeometry.Scheme.residueConstants X (f ≫ p) x.val := by
  have he : Spec.preimage (Y.fromSpecResidueField (f x.val) ≫ p) ≫ f.residueFieldMap x.val =
      Spec.preimage (X.fromSpecResidueField x.val ≫ (f ≫ p)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  exact congrArg CommRingCat.Hom.hom he
theorem residueTower (x : ClosedPoint X) :
    letI := AlgebraicGeometry.Scheme.residueAlgebra Y p (f x.val)
    letI := relativeResidueAlgebra f x
    letI := AlgebraicGeometry.Scheme.residueAlgebra X (f ≫ p) x.val
    IsScalarTower k (Y.residueField (f x.val)) (X.residueField x.val) := by
  letI := AlgebraicGeometry.Scheme.residueAlgebra Y p (f x.val)
  letI := relativeResidueAlgebra f x
  letI := AlgebraicGeometry.Scheme.residueAlgebra X (f ≫ p) x.val
  apply IsScalarTower.of_algebraMap_eq
  exact fun a => congrArg (fun g : k →+* X.residueField x.val => g a) (residueConstants_comp f p
    x).symm

-- Retain finite type of the structural map in the degree-weight interface; this equality is the
-- finrank tower identity for the already constructed residue algebras.
@[nolint unusedArguments]
theorem weight_mul_residueDegree [LocallyOfFiniteType p] (x : ClosedPoint X) :
    Degree.weight Y p (AlgebraicGeometry.Scheme.closedPointMap f x) * residueDegreeInt f x =
      Degree.weight X (f ≫ p) x := by
  letI := AlgebraicGeometry.Scheme.residueAlgebra Y p (f x.val)
  letI := relativeResidueAlgebra f x
  letI := AlgebraicGeometry.Scheme.residueAlgebra X (f ≫ p) x.val
  letI := residueTower f p x
  letI := AlgebraicGeometry.Scheme.residue_finite Y p (AlgebraicGeometry.Scheme.closedPointMap f x)
  letI := AlgebraicGeometry.Scheme.residue_finite X (f ≫ p) x
  change (Module.finrank k (Y.residueField (f x.val)) : ℤ) *
    (Module.finrank (Y.residueField (f x.val)) (X.residueField x.val) : ℤ) =
    (Module.finrank k (X.residueField x.val) : ℤ)
  exact_mod_cast Module.finrank_mul_finrank k (Y.residueField (f x.val)) (X.residueField x.val)

theorem divisorPullback_single (y : ClosedPoint Y) (m : ℤ) :
    Pullback.divisorPullback f (Finsupp.single y m) =
      ∑ x : ClosedFibre f y, Finsupp.single x.val (Pullback.ramification f x.val * m) := by
  classical
  ext z
  rw [Pullback.divisorPullback_apply, Finsupp.finsetSum_apply]
  by_cases hz : AlgebraicGeometry.Scheme.closedPointMap f z = y
  · rw [Finsupp.single_apply, ite_eq_left hz.symm]
    symm
    calc
      _ = (Finsupp.single z (Pullback.ramification f z * m)) z := by
        apply Finset.sum_eq_single (⟨z, hz⟩ : ClosedFibre f y)
        · intro b _ hb
          have hne : b.val ≠ z := fun h => hb (Subtype.ext h)
          simp only [Finsupp.single_apply, ite_eq_right hne]
        · simp
      _ = _ := Finsupp.single_eq_same
  · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hz), mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : b.val ≠ z := fun h => hz (h ▸ b.property)
    simp only [Finsupp.single_apply, ite_eq_right hne]

theorem degDiv_pullback_single [LocallyOfFiniteType p]
    (h : FiniteMorphismNormOrder.{u})
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hfin : letI := Scheme.functionFieldMapAlgebra f; Module.Finite Y.functionField X.functionField)
    (y : ClosedPoint Y) (m : ℤ) :
    Degree.degDiv X (f ≫ p) (Pullback.divisorPullback f (Finsupp.single y m)) =
      (fieldDegree f : ℤ) * Degree.degDiv Y p (Finsupp.single y m) := by
  classical
  rw [divisorPullback_single, map_sum, Degree.degDiv_single]
  simp_rw [Degree.degDiv_single]
  calc
    _ = (∑ x : ClosedFibre f y, Pullback.ramification f x.val * residueDegreeInt f x.val) *
        (m * Degree.weight Y p y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      have hw := weight_mul_residueDegree f p x.val
      rw [x.property] at hw
      rw [← hw]
      ring
    _ = _ := by rw [ramification_residue_sum f h hdimX hdimY hfin y]

theorem degDiv_pullback [LocallyOfFiniteType p]
    (h : FiniteMorphismNormOrder.{u})
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hfin : letI := Scheme.functionFieldMapAlgebra f; Module.Finite Y.functionField X.functionField)
    (D : Divisor Y) :
    Degree.degDiv X (f ≫ p) (Pullback.divisorPullback f D) =
      (fieldDegree f : ℤ) * Degree.degDiv Y p D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | @single_add y m D hy hm ih =>
    rw [map_add, map_add, map_add, mul_add, ih,
      degDiv_pullback_single f p h hdimX hdimY hfin]

/-- Numerical pullback degree for the actual invertible-sheaf Picard group.
The only new standard input is the geometric norm/order corollary; the
actual O(D) pullback comparison is proved independently. -/
theorem picardDegree_pullback [LocallyOfFiniteType p]
    (h : FiniteMorphismNormOrder.{u})
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hfin : letI := Scheme.functionFieldMapAlgebra f; Module.Finite Y.functionField X.functionField)
    (hprodX : Degree.PrincipalProductFormula X (f ≫ p))
    (hprodY : Degree.PrincipalProductFormula Y p) (L : PicardGroup Y) :
    Degree.picardDegree X (f ≫ p) hdimX hprodX (pullbackClass f L) =
      (fieldDegree f : ℤ) * Degree.picardDegree Y p hdimY hprodY L := by
  obtain ⟨a, rfl⟩ := (DivisorClass.divisorPicardEquiv Y hdimY).surjective L
  induction a using Quotient.inductionOn with
  | h D =>
    rw [DivisorClass.divisorPicardEquiv_mk, PullbackDegree.pullbackClass_divisor f hdimX hdimY,
      Degree.picardDegree_divisor, Degree.picardDegree_divisor]
    exact degDiv_pullback f p h hdimX hdimY hfin D

/-- Degree scaling of the actual Scheme.Modules pullback of a line bundle. -/
theorem lineBundleDegree_pullback [LocallyOfFiniteType p]
    (h : FiniteMorphismNormOrder.{u})
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hfin : letI := Scheme.functionFieldMapAlgebra f; Module.Finite Y.functionField X.functionField)
    (hprodX : Degree.PrincipalProductFormula X (f ≫ p))
    (hprodY : Degree.PrincipalProductFormula Y p) (L : LineBundle Y) :
    Degree.lineBundleDegree X (f ≫ p) hdimX hprodX (pullbackLineBundle f L) =
      (fieldDegree f : ℤ) * Degree.lineBundleDegree Y p hdimY hprodY L :=
  picardDegree_pullback f p h hdimX hdimY hfin hprodX hprodY (classOf Y L)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.NormDegree
