/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.OrderTransport
public import Aglib.AlgebraicGeometry.Morphisms.Finite.LocalNormAlgebra
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The geometric finite-morphism norm/order formula

The full local model, its maximal branches and its stalk and residue maps are
constructed in `SchemeLocalModel`. This module compares its length orders with
the actual scheme orders and applies the all-maximal-branches algebraic theorem.
-/




@[expose] public section

noncomputable section
open IsDiscreteValuationRing.FiniteNorm
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.NormDegree

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable [AlgebraicGeometry.IsNoetherian X] [hNoethY : AlgebraicGeometry.IsNoetherian Y]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable [hDVRY : ∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
variable (f : X ⟶ Y) [IsDominant f] [IsFinite f]
variable (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

attribute [local instance] LocalNormAlgebra.chartAlgebra LocalNormAlgebra.stalkAlgebra
  LocalNormAlgebra.functionFieldAlgebra LocalNormAlgebra.branchStalkAlgebra

local instance branch_isLocalHom (q : MaximalSpectrum (LocalNormAlgebra.Ring f U hU y)) :
    IsLocalHom (algebraMap (Y.presheaf.stalk y.val) (Localization.AtPrime q.asIdeal)) :=
  localizationAtMaximal_isLocalHom q.asIdeal

omit hNoethY hDVRY in
-- Retain target noetherianity and its DVR stalks in the finite local-norm branch interface; this
-- comparison uses the supplied branch stalk and fraction-field identifications.
/-- The length-defined branch order is precisely `Scheme.ord` at its actual fibre point. -/
@[nolint unusedArguments]
theorem branch_order [AlgebraicGeometry.IsNoetherian Y]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (hy : IsClosed ({y.val} : Set Y))
    (q : MaximalSpectrum (LocalNormAlgebra.Ring f U hU y)) (z : X.functionFieldˣ) :
    letI := LocalNormAlgebra.branch_isDiscreteValuationRing f U hU y hy q
    letI := branchFractionAlgebra (L := X.functionField) q
    letI := branchFraction_isFractionRing (L := X.functionField) q
    ((Ring.ordFrac (Localization.AtPrime q.asIdeal) (z : X.functionField)).unzeroD 1).toAdd =
      X.ord (z : X.functionField) (LocalNormAlgebra.branchPoint f U hU y q) := by
  letI := LocalNormAlgebra.branch_isDiscreteValuationRing f U hU y hy q
  letI := branchFractionAlgebra (L := X.functionField) q
  letI := branchFraction_isFractionRing (L := X.functionField) q
  let x : ClosedPoint X := ⟨LocalNormAlgebra.branchPoint f U hU y q,
    LocalNormAlgebra.branchPoint_closed f U hU y hy q⟩
  letI : IsDiscreteValuationRing (X.presheaf.stalk (LocalNormAlgebra.branchPoint f U hU y q)) :=
    inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk x.val))
  have he := ordFrac_eq_of_ringEquiv (LocalNormAlgebra.branchStalkEquiv f U hU y q).toRingEquiv
    (LocalNormAlgebra.branchStalkEquiv_fraction f U hU y q) z
  rw [he, Scheme.ord_eq_ordHom_of_coheight_eq_one (coheight_eq_one_of_dvr X x.val)]
  rfl

include hU in
/-- Norm/order identity over the entire inverse image of an affine neighborhood of a closed point.
-/
theorem norm_order_chart (hy : IsClosed ({y.val} : Set Y)) (z : X.functionFieldˣ) :
    Y.ord (fieldNorm f z) y.val =
      ∑ x : ClosedFibre f ⟨y.val, hy⟩,
        residueDegreeInt f x.val * X.ord (z : X.functionField) x.val.val := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := LocalNormAlgebra.stalkFieldAlgebra f U y
  letI := LocalNormAlgebra.stalk_field_scalarTower f U y
  letI := LocalNormAlgebra.stalk_model_scalarTower f U hU y
  letI : IsDiscreteValuationRing (Y.presheaf.stalk y.val) :=
    inferInstanceAs (IsDiscreteValuationRing (Y.presheaf.stalk (⟨y.val, hy⟩ : ClosedPoint Y).val))
  letI : Fintype (MaximalSpectrum (LocalNormAlgebra.Ring f U hU y)) := Fintype.ofFinite _
  letI (q : MaximalSpectrum (LocalNormAlgebra.Ring f U hU y)) :
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
    LocalNormAlgebra.branch_isDiscreteValuationRing f U hU y hy q
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one (coheight_eq_one_of_dvr Y y.val)]
  change ((Ring.ordFrac (Y.presheaf.stalk y.val) (Algebra.norm Y.functionField
    (z : X.functionField))).unzeroD 1).toAdd = _
  rw [fieldNorm_order_eq_sum_all_maximal (B := LocalNormAlgebra.Ring f U hU y)]
  apply Fintype.sum_equiv (LocalNormAlgebra.closedFibreEquiv f U hU y hy)
  intro q
  rw [LocalNormAlgebra.branch_residueDegree f U hU y hy q,
    branch_order f U hU y hy q z]
  rfl

/-- The universal geometric norm/order family of `NormDegree.lean:89` is realized
on repository source basis `914476dd55baa6feaef45710e946922ea011eb0c`.
The full local inverse image, all its maximal branches, its actual fraction fields,
its residue maps and its scheme orders are proved in the dependency closure.
No separability or perfectness assumption is used. -/
theorem finiteMorphismNormOrder : FiniteMorphismNormOrder.{u} := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ z y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := y.val) trivial
  letI : Nonempty U := ⟨⟨y.val, hy⟩⟩
  exact norm_order_chart f U hU ⟨y.val, hy⟩ y.property z

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.NormDegree
