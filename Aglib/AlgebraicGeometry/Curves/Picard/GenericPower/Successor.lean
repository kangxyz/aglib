/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Iso.Composite
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Coherence
public import Aglib.AlgebraicGeometry.Curves.Picard.GenericPower.Zero
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.GenericPower.Successor`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`a95412f9fc1aac6f2caef086af143d94a17f2a5094afed05b05105b4e556ead4`.
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
  (LineBundle pullbackLineBundle tensorPowerLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap tensorSheafIso tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Successor powers of the canonical generic divisor trivialization

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

private theorem threeMapExpansion {C : Type*} [Category C] {A B D E G H : C}
    (f : A ⟶ D) (g : D ⟶ E) (h : E ⟶ H)
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ G) (e : G ⟶ H)
    (hf : f = a ≫ b) (hg : g = c) (hh : h = d ≫ e) :
    f ≫ g ≫ h = a ≫ b ≫ c ≫ d ≫ e := by
  rw [hf, hg, hh]
  simp only [Category.assoc]

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
/-- The native hom projection of the existing divisor-power equation.
Its original module category and full composite endpoint are retained. -/
theorem divisorPowerIso_succ_hom (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) (n : ℕ) :
    (divisorPowerIso X hdim D n.succ).hom =
      (tensorSheafIso X (Iso.refl (divisorLineBundle X hdim D).val)
        (divisorPowerIso X hdim D n) ≪≫ divisorTensorIso X hdim D (n • D) ≪≫
          eqToIso (congrArg (divisorSheaf X) (by rw [succ_nsmul, add_comm]))).hom :=
  congrArg Iso.hom (divisorPowerIso.eq_2 X hdim D n)

/-- The divisor-side successor expansion, isolated from all other recursive powers. -/
theorem genericMap_power_succ_left (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (n : ℕ) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
        (divisorPowerIso X hdim D (n + 1)).hom ≫ genericMap X ((n + 1) • D) =
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
        (tensorSheafIso X (Iso.refl (divisorLineBundle X hdim D).val)
          (divisorPowerIso X hdim D n)).hom ≫
      pullbackTensorMap ((X.fromSpecStalk (genericPoint X))) (divisorSheaf X D) (divisorSheaf X
          (n • D)) ≫
        tensorSheafMap (Spec X.functionField) (genericMap X D) (genericMap X (n • D)) ≫
          (tensorSheafLeftUnit (Spec X.functionField)
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).hom := by
  have hsucc : D + n • D = (n + 1) • D := by rw [succ_nsmul]; exact add_comm _ _
  have hb : (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
      (divisorTensorIso X hdim D (n • D)).hom ≫ genericMap X (D + n • D) =
      pullbackTensorMap ((X.fromSpecStalk (genericPoint X))) (divisorSheaf X D) (divisorSheaf X
          (n • D)) ≫
        tensorSheafMap (Spec X.functionField) (genericMap X D) (genericMap X (n • D)) ≫
          (tensorSheafLeftUnit (Spec X.functionField)
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).hom := by
    rw [divisorTensorIso_hom]
    exact genericMap_tensor X D (n • D)
  exact pullback_three_isos_tail ((X.fromSpecStalk (genericPoint X)))
    (divisorPowerIso X hdim D (n + 1))
    (tensorSheafIso X (Iso.refl (divisorLineBundle X hdim D).val)
      (divisorPowerIso X hdim D n)) (divisorTensorIso X hdim D (n • D))
    (eqToIso (congrArg (divisorSheaf X) hsucc)) (divisorPowerIso.eq_2 X hdim D n)
    (genericMap X ((n + 1) • D)) (genericMap X (D + n • D)) _
    (genericMap_eqToIso X hsucc) hb

/-- The positive generic map is the literal hom of the specified power isomorphism. -/
theorem generic_powerIso_succ_hom (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec X.functionField)
      (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
      (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
          X.functionField)) (genericIso X hdim D) (n + 1)).hom =
      tensorSheafMap (Spec X.functionField) (genericMap X D)
        (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec
            X.functionField)
          (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X
              hdim D))
          (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
              X.functionField)) (genericIso X hdim D) n).hom := by
  exact (powerIso_succ_hom (Spec X.functionField)
    (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
    (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
        X.functionField)) (genericIso X hdim D) n).trans
      (congrArg (fun e => tensorSheafMap (Spec X.functionField) e
        (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec
            X.functionField)
          (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X
              hdim D))
          (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
              X.functionField)) (genericIso X hdim D) n).hom)
        (genericIso_hom X hdim D))

/-- The three canonical power maps expand together, without the divisor recursion. -/
theorem genericMap_power_succ_right (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso
        ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D) (n + 1)).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec X.functionField)
        (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
        (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
            X.functionField)) (genericIso X hdim D) (n + 1)).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso (Spec
          X.functionField) (n + 1)).hom =
    pullbackTensorMap ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D).val
      (tensorPowerLineBundle X (divisorLineBundle X hdim D) n).val ≫
      tensorSheafMap (Spec X.functionField) (𝟙 _)
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso
            ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D) n).hom ≫
      tensorSheafMap (Spec X.functionField) (genericMap X D)
        (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec
            X.functionField)
          (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X
              hdim D))
          (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
              X.functionField)) (genericIso X hdim D) n).hom ≫
      (tensorSheafLeftUnit (Spec X.functionField)
        (tensorPowerLineBundle (Spec X.functionField)
            (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
            X.functionField)) n).val).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso (Spec
          X.functionField) n).hom := by
  exact threeMapExpansion _ _ _ _ _ _ _ _
    (pullbackPowerIso_succ_hom ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D) n)
    (generic_powerIso_succ_hom X hdim D n)
    (unitPowerIso_succ_hom (Spec X.functionField) n)

/-- The successor step composes the isolated actual equations and tensor calculation. -/
theorem genericMap_power_succ (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) (n : ℕ)
    (ih : PowerCompatibility X hdim D n) : PowerCompatibility X hdim D (n + 1) := by
  exact (genericMap_power_succ_left X hdim D n).trans
    ((tensor_iso_successor_step ((X.fromSpecStalk (genericPoint X)))
      (divisorLineBundle X hdim D).val
      (tensorPowerLineBundle X (divisorLineBundle X hdim D) n).val (divisorSheaf X (n • D))
      (tensorPowerLineBundle (Spec X.functionField)
        (pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
            n).val
      (tensorPowerLineBundle (Spec X.functionField)
          (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
          X.functionField)) n).val
      (divisorPowerIso X hdim D n) (genericMap X D) (genericMap X (n • D))
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso
          ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D) n).hom
      (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso (Spec X.functionField)
        (L := pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
        (M := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
            X.functionField)) (genericIso X hdim D) n).hom
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso (Spec
          X.functionField) n).hom ih).trans
        (genericMap_power_succ_right X hdim D n).symm)

/-- The canonical rational inclusion and actual divisor tensor-power map agree. -/
theorem genericMap_power (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) (n : ℕ) :
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
          X.functionField) n).hom := by
  change PowerCompatibility X hdim D n
  induction n with
  | zero => exact genericMap_power_zero X hdim D
  | succ n ih => exact genericMap_power_succ X hdim D n ih

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericPower
