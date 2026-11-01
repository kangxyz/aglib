/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.DegreeZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Uniqueness of an effective divisor in a rank-one linear system

If H0(O(D)) has dimension one over the original structural field, another
effective divisor in the same actual Picard class equals D. The class
comparison produces a rational function whose section is a scalar multiple
of the section one. That scalar is a unit, so its original principal divisor
vanishes. This is a field-valued divisor uniqueness result; it does not by
itself assert that an Abel morphism is birational or separable.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme Scheme.Cohomology Scheme.Modules.Invertible
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard

open DivisorClass

variable {k : Type u} [Field k] (X : FScheme k) [IsIntegral X.left]
  [IsNoetherian X.left]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

-- Keep the actual field action on sheaf sections and its original constants map.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An effective divisor with a one-dimensional original section space is
the unique effective divisor representing its actual Picard class. -/
theorem effective_divisor_eq_of_class_eq_of_h0_one
    (hdim : topologicalKrullDim X.left ≤ 1) (D E : Divisor X.left)
    (hD : ∀ x, 0 ≤ D x) (hE : ∀ x, 0 ≤ E x)
    (hclass : divisorToPicard X.left hdim D = divisorToPicard X.left hdim E)
    (h0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left D) 0) = 1) :
    D = E := by
  have hquot : (QuotientAddGroup.mk D : Divisor X.left ⧸ (principal X.left).range) =
      QuotientAddGroup.mk E := divisorClassToPicard_injective X.left hdim hclass
  obtain ⟨f, hf⟩ := QuotientAddGroup.eq.mp hquot
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  let z1 : fractionalSections X.left D ⊤ := ⟨1, Or.inr fun x _ => by
    have h : X.left.ord (1 : X.left.functionField) x.val = 0 := (localOrder X.left x).map_zero
    simpa only [h, zero_add] using hD x⟩
  let zf : fractionalSections X.left D ⊤ := ⟨(f.toMul : X.left.functionField), Or.inr fun x _ => by
    have h := congrArg (fun A : Divisor X.left => A x) hf
    change X.left.ord (f.toMul : X.left.functionField) x.val = -D x + E x at h
    linarith [hE x]⟩
  let q := divisorSheafSectionsEquiv X.left D ⊤
  let s1 := q.symm z1
  let sf := q.symm zf
  have hs1 : s1 ≠ 0 := by
    intro hs
    have hz : z1 = 0 := by
      simpa only [s1, LinearEquiv.apply_symm_apply, map_zero] using congrArg q hs
    exact one_ne_zero (congrArg Subtype.val hz)
  have hsections : Module.finrank k ((divisorSheaf X.left D).val.obj (op ⊤)) = 1 :=
    (moduleH0Equiv X (divisorSheaf X.left D)).finrank_eq.symm.trans h0
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hsections hs1 sf
  change (constants X a) • s1 = sf at ha
  have hfractions : (constants X a) • z1 = zf := by
    simpa only [s1, sf, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply] using congrArg q ha
  have hvalue := congrArg Subtype.val hfractions
  change X.left.germToFunctionField ⊤ (constants X a) * 1 =
    (f.toMul : X.left.functionField) at hvalue
  rw [mul_one] at hvalue
  have ha0 : a ≠ 0 := by
    intro ha0
    have hz : (f.toMul : X.left.functionField) = 0 := by
      simpa only [ha0, map_zero] using hvalue.symm
    exact f.toMul.ne_zero hz
  have hprincipal : principal X.left f = 0 := by
    ext x
    change X.left.ord (f.toMul : X.left.functionField) x.val = 0
    rw [← hvalue]
    exact Scheme.ord_of_isUnit ((isUnit_iff_ne_zero.mpr ha0).map (constants X))
      (show x.val ∈ (⊤ : X.left.Opens) from trivial)
  have hzero : -D + E = 0 := hf.symm.trans hprincipal
  have heq : E - D = 0 := by simpa only [sub_eq_add_neg, add_comm] using hzero
  exact (sub_eq_zero.mp heq).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Picard
