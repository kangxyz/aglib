/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Coherence
public import Aglib.CategoryTheory.Iso.Composite
public import Aglib.AlgebraicGeometry.Curves.Picard.GenericTrivialization
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.GenericPower.Zero`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`dbfcce17dfa743552951649cec89370c8a8a6621d7ca7f9984494024b540f224`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.Power

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Zero power of the canonical generic divisor trivialization

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`, C4/C5.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The scheme is actual integral and Noetherian, of topological dimension at
most one, with DVRs at all closed points. The canonical generic map is the
adjoint of the actual fractional O(D) inclusion, fixed in GenericTrivialization.
This module proves the zero-power square using the genuine free structure
module and equality transport. The successor square and its induction are
proved separately in GenericPower.Successor.

For div(f) = nD the specified trivialization is multiplication by f, and its
canonical generic coordinate is the positive unit f. Thus compatible frames
have a^n=f; this does not identify normalized sections f*s^n=1 without inversion.
No comparison, generic representative identity or new theorem family is an
input. Small opaque equations isolate recursive dependent-isomorphism proof
terms without changing the maps or their exact source/target categories.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericPower
open DivisorClass GenericTrivialization
universe u

private theorem freeUnitCancel {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ E) (e : D ≅ E) :
    f ≫ g = f ≫ g ≫ e.inv ≫ 𝟙 D ≫ e.hom := by simp

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
/-- The actual equality-transport equation for the zeroth divisor power. -/
theorem divisorPowerIso_zero_hom (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (hunit : ∀ x : ClosedPoint X, X.ord (1 : X.functionField) x.val + (0 : Divisor X) x = 0) :
    (divisorPowerIso X hdim D 0).hom =
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso X).hom ≫
          (globalTrivialization X hdim 0 1 hunit).hom ≫
        (eqToIso (congrArg (divisorSheaf X) (zero_smul ℕ D).symm)).hom :=
  by
    rw [divisorPowerIso.eq_1]
    exact CategoryTheory.Iso.mpr_hom (C := X.Modules) (congrArg (divisorSheaf X) (zero_smul ℕ D))
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso X ≪≫
          globalTrivialization X hdim 0 1 hunit)

/-- The literal canonical generic tensor-power square. -/
def PowerCompatibility (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) (n : ℕ) : Prop :=
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map (divisorPowerIso X hdim
        D n).hom ≫
      genericMap X (n • D) =
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso
        ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D) n).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec X.functionField)
        (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
        (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
            X.functionField)) (genericIso X hdim D) n).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso (Spec
          X.functionField) n).hom

/-- The zero power uses the actual free-unit map and equality transport of the zero divisor. -/
theorem genericMap_power_zero (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    PowerCompatibility X hdim D 0 := by
  unfold PowerCompatibility
  have hunit : ∀ x : ClosedPoint X, X.ord (1 : X.functionField) x.val + (0 : Divisor X) x = 0 := by
    intro x
    have ho : X.ord (1 : X.functionField) x.val = 0 := (localOrder X x).map_zero
    simpa using ho
  have hzero := genericMap_globalTrivialization X hdim 0 1 hunit
  simp only [_root_.map_one, Units.val_one,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_one,
    Category.comp_id] at hzero
  have hz : (0 : ℕ) • D = 0 := zero_smul ℕ D
  rw [divisorPowerIso_zero_hom X hdim D hunit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [genericMap_eqToIso X hz.symm, hzero,
    pullbackPowerIso_zero_hom, powerIso_zero_hom, unitPowerIso_zero_hom]
  exact freeUnitCancel (C := (Spec X.functionField).Modules)
    ((Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso X).hom)
    (pullbackUnitIso ((X.fromSpecStalk (genericPoint X)))).hom
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso (Spec X.functionField))

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericPower
