/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.CriticalPoint
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChange
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.ComputeDegree

/-!
# Integral split-node Weierstrass normal forms

Henselian lifts and admissible variable changes for the same Weierstrass equation. The residue
simple-tangent condition works in all characteristics. Generic j comparisons retain the actual
injective coefficient map and ellipticity hypotheses.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`EllipticCurve/Tate/Model/SplitNodal.lean`: source ranges [[65, 285]];
SHA-256 `009910a4aa56fda14a261fa278b3df361cc9fa8c10474d5e6e13b7ee296c8abd`.
-/

@[expose] public noncomputable section

universe u
open Polynomial IsLocalRing WeierstrassCurve

namespace WeierstrassCurve.SplitNodalNormalForm
variable {R : Type u} [CommRing R]

/-- The literal one-parameter split nodal deformation. -/
def equation (t : R) : WeierstrassCurve R where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := t

@[simp] theorem equation_c4 (t : R) : (equation t).c₄ = 1 := by
  simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, equation]

@[simp] theorem equation_discriminant (t : R) : (equation t).Δ = -t - 432 * t ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, equation]
  ring

/-- Lift one of the two distinct rational tangent directions. The simple-root
hypothesis explicitly retains what split ordinariness supplies. -/
theorem exists_tangent_lift [HenselianLocalRing R] (W : WeierstrassCurve R)
    (s₀ : ResidueField R)
    (hs₀ : s₀ ^ 2 + residue R W.a₁ * s₀ - residue R W.a₂ = 0)
    (hd₀ : 2 * s₀ + residue R W.a₁ ≠ 0) :
    ∃ s : R, s ^ 2 + W.a₁ * s - W.a₂ = 0 ∧
      residue R s = s₀ ∧ IsUnit (W.a₁ + 2 * s) := by
  obtain ⟨a, ha⟩ := residue_surjective s₀
  let f : R[X] := X ^ 2 + C W.a₁ * X - C W.a₂
  have hf : f.Monic := by dsimp [f]; monicity!
  have hfa : f.eval a ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa [f, ha] using hs₀
  have hda : IsUnit (f.derivative.eval a) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa [f, derivative_pow, derivative_mul, ha, map_ofNat] using hd₀
  obtain ⟨s, hs, hsa⟩ := HenselianLocalRing.is_henselian f hf a hfa hda
  have hres : residue R s = s₀ := by
    have h := (residue_eq_zero_iff _).mpr hsa
    simpa [ha, sub_eq_zero] using h
  refine ⟨s, ?_, hres, ?_⟩
  · simpa [Polynomial.IsRoot, f] using hs
  · apply (residue_ne_zero_iff_isUnit _).mp
    simpa [hres, add_comm, map_ofNat] using hd₀

/-- Explicit integral admissible change of variables to the one-parameter
normal form. No square root of a unit or division by 2 or 3 is used. -/
theorem variableChange_eq_equation (W : WeierstrassCurve R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (s : R)
    (hs : s ^ 2 + W.a₁ * s - W.a₂ = 0)
    (v : Rˣ) (hv : (v : R) = W.a₁ + 2 * s) :
    (WeierstrassCurve.VariableChange.mk v 0 s 0) • W =
      equation ((↑v⁻¹ : R) ^ 6 * W.a₆) := by
  have hs' : W.a₂ - s * W.a₁ - s ^ 2 = 0 := by linear_combination -hs
  ext
  · simp only [WeierstrassCurve.variableChange_a₁, equation]
    rw [← hv]
    exact v.inv_mul
  · simp only [WeierstrassCurve.variableChange_a₂, mul_zero, add_zero, hs',
      mul_zero, equation]
  · simp [WeierstrassCurve.variableChange_a₃, h3, equation]
  · simp [WeierstrassCurve.variableChange_a₄, h3, h4, equation]
  · simp [WeierstrassCurve.variableChange_a₆, equation]

/-- A split critical equation is integrally isomorphic to the actual split
one-parameter deformation, preserving that its constant lies in the maximal
ideal. All residue characteristics, including 2 and 3, are covered. -/
theorem exists_normal_form [HenselianLocalRing R] (W : WeierstrassCurve R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ ∈ maximalIdeal R)
    (s₀ : ResidueField R)
    (hs₀ : s₀ ^ 2 + residue R W.a₁ * s₀ - residue R W.a₂ = 0)
    (hd₀ : 2 * s₀ + residue R W.a₁ ≠ 0) :
    ∃ C : WeierstrassCurve.VariableChange R, ∃ t : R,
      t ∈ maximalIdeal R ∧ C • W = equation t := by
  obtain ⟨s, hs, _, v, hv⟩ := exists_tangent_lift W s₀ hs₀ hd₀
  refine ⟨⟨v, 0, s, 0⟩, (↑v⁻¹ : R) ^ 6 * W.a₆,
    (maximalIdeal R).mul_mem_left _ h6, ?_⟩
  exact variableChange_eq_equation W h3 h4 s hs v hv

/-- The discriminant separates these normal forms over any local ring on the
maximal ideal. This is the integral substitute for a quadratic-twist descent. -/
theorem equation_discriminant_injective [IsLocalRing R] {s t : R}
    (hs : s ∈ maximalIdeal R) (ht : t ∈ maximalIdeal R)
    (he : (equation s).Δ = (equation t).Δ) : s = t := by
  have hu : IsUnit (1 + 432 * (s + t)) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simp [(residue_eq_zero_iff _).mpr hs, (residue_eq_zero_iff _).mpr ht]
  have hprod : (1 + 432 * (s + t)) * (s - t) = 0 := by
    simp only [equation_discriminant] at he
    linear_combination -he
  exact sub_eq_zero.mp (hu.mul_left_cancel (by simpa using hprod))

section GenericJ
variable {F : Type*} [Field F] [IsLocalRing R] (f : R →+* F)

/-- Actual generic j separates the integral one-parameter split forms.
The only map requirement is injectivity of the original coefficient map. -/
theorem equation_j_injective (hf : Function.Injective f) {s t : R}
    (hs : s ∈ maximalIdeal R) (ht : t ∈ maximalIdeal R)
    [((equation s).map f).IsElliptic] [((equation t).map f).IsElliptic]
    (he : ((equation s).map f).j = ((equation t).map f).j) : s = t := by
  apply equation_discriminant_injective hs ht
  apply hf
  simpa only [WeierstrassCurve.j_eq, WeierstrassCurve.map_c₄,
    WeierstrassCurve.map_Δ, equation_c4, map_one, one_pow, mul_one, inv_inj] using he

/-- Equal generic j for two already constructed integral split normalizations
produces an actual integral admissible change of variables. -/
theorem variableChange_of_normalizations (hf : Function.Injective f)
    (W V : WeierstrassCurve R) [(W.map f).IsElliptic] [(V.map f).IsElliptic]
    (C D : WeierstrassCurve.VariableChange R) (s t : R)
    (hs : s ∈ maximalIdeal R) (ht : t ∈ maximalIdeal R)
    (hC : C • W = equation s) (hD : D • V = equation t)
    (hj : (W.map f).j = (V.map f).j) : (D⁻¹ * C) • W = V := by
  have : ((equation s).map f).IsElliptic := by
    rw [← hC, ← WeierstrassCurve.map_variableChange]
    infer_instance
  have : ((equation t).map f).IsElliptic := by
    rw [← hD, ← WeierstrassCurve.map_variableChange]
    infer_instance
  have hst : s = t := by
    apply equation_j_injective f hf hs ht
    simp_rw [← hC, ← hD, ← WeierstrassCurve.map_variableChange,
      WeierstrassCurve.variableChange_j]
    exact hj
  rw [mul_smul, hC, hst, ← hD, inv_smul_smul]
end GenericJ
end WeierstrassCurve.SplitNodalNormalForm


/-! ## SplitNodeRecognition; source
7c4e30203af0882a0107b37e4bf537197c6467ff4a7ecd49f8e380eb657d167f -/


open IsLocalRing
namespace WeierstrassCurve.SplitNodalNormalForm
open WeierstrassCurve.CriticalPoint
variable {R : Type u} [CommRing R]

/-- A rational tangent direction distinct from its conjugate already supplies
nonvanishing of the actual Hessian; no additional ordinary-node certificate
is needed. -/
theorem hessian_ne_zero_of_simple_tangent {k : Type*} [Field k]
    (W : WeierstrassCurve k) (x s : k)
    (hs : s ^ 2 + W.a₁ * s - (W.a₂ + 3 * x) = 0)
    (hd : 2 * s + W.a₁ ≠ 0) : criticalHessianDet W x ≠ 0 := by
  have he : W.b₂ + 12 * x = (2 * s + W.a₁) ^ 2 := by
    dsimp only [WeierstrassCurve.b₂]
    linear_combination -4 * hs
  rw [criticalHessianDet_eq, neg_ne_zero, he]
  exact pow_ne_zero 2 hd

/-- Two distinct rational slopes in the actual tangent cone give the simple
root needed by Hensel, including in characteristic two. -/
theorem simple_tangent_of_distinct_roots {k : Type*} [Field k]
    (a b s t : k) (hs : s ^ 2 + a * s - b = 0)
    (ht : t ^ 2 + a * t - b = 0) (hst : s ≠ t) : 2 * s + a ≠ 0 := by
  have hp : (s - t) * (s + t + a) = 0 := by linear_combination hs - ht
  have ha : s + t + a = 0 := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hst)
  have he : 2 * s + a = s - t := by linear_combination ha
  rw [he]
  exact sub_ne_zero.mpr hst

/-- Starting from an actual rational split ordinary node of the reduced cubic,
construct an integral admissible normalization. The source equation and both
actual gradient equalities are explicit; no isomorphism or recognition
conclusion is accepted as an input. -/
theorem exists_normal_form_of_split_node [HenselianLocalRing R]
    (W : WeierstrassCurve R) (x y s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation x y)
    (hx : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0)
    (hy : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0)
    (hs : s ^ 2 + residue R W.a₁ * s - (residue R W.a₂ + 3 * x) = 0)
    (hd : 2 * s + residue R W.a₁ ≠ 0) :
    ∃ C : WeierstrassCurve.VariableChange R, ∃ t : R,
      t ∈ maximalIdeal R ∧ C • W = equation t := by
  have hh : criticalHessianDet (W.map (residue R)) x ≠ 0 :=
    hessian_ne_zero_of_simple_tangent _ x s hs hd
  obtain ⟨r, t, hr, _, _, _, h3, h4, _, h6, _⟩ :=
    exists_critical_translation W x y he hx hy hh
  have hs' : s ^ 2 + residue R (translate W r t).a₁ * s -
      residue R (translate W r t).a₂ = 0 := by
    simpa only [translate_a1, translate_a2, map_add, map_mul, map_ofNat, hr] using hs
  have hd' : 2 * s + residue R (translate W r t).a₁ ≠ 0 := by
    simpa only [translate_a1] using hd
  obtain ⟨C, a, ha, hC⟩ := exists_normal_form (translate W r t) h3 h4 h6 s hs' hd'
  exact ⟨C * WeierstrassCurve.VariableChange.mk 1 r 0 t, a, ha,
    by simpa only [mul_smul, translate] using hC⟩
/-- Concrete split-node data for this reduced equation. This is geometric
input on the literal reduced cubic, not a recognition or isomorphism premise. -/
structure SplitNodeData [IsLocalRing R] (W : WeierstrassCurve R) where
  x : ResidueField R
  y : ResidueField R
  first : ResidueField R
  second : ResidueField R
  point : (W.map (residue R)).toAffine.Equation x y
  gradientX : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0
  gradientY : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0
  firstRoot : first ^ 2 + residue R W.a₁ * first - (residue R W.a₂ + 3 * x) = 0
  secondRoot : second ^ 2 + residue R W.a₁ * second - (residue R W.a₂ + 3 * x) = 0
  distinct : first ≠ second

theorem SplitNodeData.exists_normal_form [HenselianLocalRing R]
    {W : WeierstrassCurve R} (d : SplitNodeData W) :
    ∃ C : WeierstrassCurve.VariableChange R, ∃ t : R,
      t ∈ maximalIdeal R ∧ C • W = equation t :=
  exists_normal_form_of_split_node W d.x d.y d.first d.point d.gradientX d.gradientY
    d.firstRoot (simple_tangent_of_distinct_roots _ _ _ _ d.firstRoot d.secondRoot d.distinct)

/-- Genuine local algebraic recognition between two split nodal integral
models with the same generic j: the integral variable change is constructed. -/
theorem exists_variableChange_of_split_nodes_of_j_eq [HenselianLocalRing R]
    {F : Type*} [Field F] (f : R →+* F) (hf : Function.Injective f)
    (W V : WeierstrassCurve R) [(W.map f).IsElliptic] [(V.map f).IsElliptic]
    (dW : SplitNodeData W) (dV : SplitNodeData V)
    (hj : (W.map f).j = (V.map f).j) :
    ∃ C : WeierstrassCurve.VariableChange R, C • W = V := by
  obtain ⟨C, s, hs, hC⟩ := dW.exists_normal_form
  obtain ⟨D, t, ht, hD⟩ := dV.exists_normal_form
  exact ⟨D⁻¹ * C, variableChange_of_normalizations f hf W V C D s t hs ht hC hD hj⟩
end WeierstrassCurve.SplitNodalNormalForm
