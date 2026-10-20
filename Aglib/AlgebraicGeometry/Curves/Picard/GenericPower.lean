/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.GenericPower.Successor
public import Aglib.AlgebraicGeometry.Curves.Picard.KummerPairs
public import Aglib.AlgebraicGeometry.Curves.Picard.TrivializedPower
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.GenericPower`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`93a50a382055cd4264daa7b5fc834ab1f9e9399a454385c56c4e968e543ca7fc`.
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
# Canonical generic power trivialization for divisor pairs

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`, C4/C5.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The scheme is actual integral and Noetherian, of topological dimension at
most one, with DVRs at all closed points. The canonical generic map is the
adjoint of the actual fractional O(D) inclusion, fixed in GenericTrivialization.
The zero power uses the genuine free structure module and equality transport;
the successor square is derived from actual multiplication and tensor-pullback
naturality. The resulting induction identifies the actual divisor power map
with the canonical generic tensor power.

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
/-- The specified pulled power trivialization, expressed through its actual maps. -/
theorem pullbackPair_trivialization_hom {S T : Scheme.{u}} (f : S ⟶ T) {n : ℕ}
    (P : AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.Pair T n) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPair f
        P).trivialization.hom =
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso f
          P.lineBundle n).inv ≫
        (Scheme.Modules.pullback f).map P.trivialization.hom ≫ (pullbackUnitIso f).hom := rfl

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
/-- The divisor pair uses precisely multiplication by its specified rational function. -/
theorem divisorPair_trivialization_hom (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (a : AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs.pairs X n) :
    (AlgebraicGeometry.Scheme.OverField.Curve.Picard.TrivializedPower.ofDivisorPair X hdim n
        a).trivialization.hom =
      (divisorPowerIso X hdim a.val.1 n).hom ≫
        (eqToIso (congrArg (divisorSheaf X) a.property.symm)).hom ≫
          (principalTrivialization X hdim a.val.2.toMul).hom := rfl

/-- The canonical generic trivialization carries the actual divisor pair's tau
precisely to multiplication by its positive function representative. -/
theorem genericDivisorPair_compatibility (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (p : AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs.pairs X n) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec X.functionField)
      (L := (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPair
          ((X.fromSpecStalk (genericPoint X)))
        (AlgebraicGeometry.Scheme.OverField.Curve.Picard.TrivializedPower.ofDivisorPair X hdim
            n p)).lineBundle)
      (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
          X.functionField))
      (genericIso X hdim p.val.1) n).hom ≫
        (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso (Spec
            X.functionField) n).hom ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap (Spec
              X.functionField) _ ((Units.map (Scheme.ΓSpecIso
              X.functionField).inv.hom.toMonoidHom p.val.2.toMul)) =
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPair ((X.fromSpecStalk
          (genericPoint X)))
        (AlgebraicGeometry.Scheme.OverField.Curve.Picard.TrivializedPower.ofDivisorPair X hdim
            n p)).trivialization.hom := by
  rw [pullbackPair_trivialization_hom, divisorPair_trivialization_hom]
  apply (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso
      ((X.fromSpecStalk (genericPoint X)))
    (divisorLineBundle X hdim p.val.1) n).eq_inv_comp.mpr
  have hp := congrArg (fun a => a ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap (Spec X.functionField)
    (SheafOfModules.unit (Spec X.functionField).ringCatSheaf) ((Units.map (Scheme.ΓSpecIso
        X.functionField).inv.hom.toMonoidHom p.val.2.toMul)))
    (genericMap_power X hdim p.val.1 n)
  simp only [Category.assoc] at hp ⊢
  rw [← hp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [genericMap_principal]
  have he := congrArg (fun a => a ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap (Spec X.functionField)
    (SheafOfModules.unit (Spec X.functionField).ringCatSheaf) ((Units.map (Scheme.ΓSpecIso
        X.functionField).inv.hom.toMonoidHom p.val.2.toMul)))
    (genericMap_eqToIso X p.property.symm)
  simp only [Category.assoc] at he ⊢
  erw [he]

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericPower
