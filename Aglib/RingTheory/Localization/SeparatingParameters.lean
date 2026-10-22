/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Localization at separating parameters recovers the actual fraction field

The parameter-field action is constructed by a localization map. The point into
the given fraction field is proved bijective, rather than assuming that the
localized source is already a field.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace SeparatingParameterLocalization

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K]
variable (D : Subalgebra k K) (y : ι → D)

/-- The actual parameter denominators in the residual source algebra. -/
def denominators : Submonoid D :=
  (nonZeroDivisors (MvPolynomial ι k)).map (aeval y).toRingHom

/-- The actual source localized at nonzero parameter polynomials. -/
abbrev Ring := Localization (denominators D y)

/-- Evaluation in the original field agrees with inclusion after source evaluation. -/
theorem coe_aeval (f : MvPolynomial ι k) :
    ((aeval y f : D) : K) = aeval (fun i => (y i : K)) f := by
  have h : D.val.comp (aeval y) = aeval (fun i => (y i : K)) := by
    ext i
    simp
  exact DFunLike.congr_fun h f

variable (hy : AlgebraicIndependent k (fun i => (y i : K)))

include hy in
/-- Algebraic independence makes every actual parameter denominator nonzero. -/
theorem denominator_ne_zero (s : denominators D y) : (s.1 : K) ≠ 0 := by
  obtain ⟨f, hf, he⟩ := s.property
  rw [← he]
  change ((aeval y f : D) : K) ≠ 0
  rw [coe_aeval]
  exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hf)
    ((algebraicIndependent_iff_injective_aeval.mp hy) (h.trans (map_zero _).symm))

/-- The canonical fraction-field action on the original fraction field. -/
def fractionMap : FractionRing (MvPolynomial ι k) →+* K :=
  IsFractionRing.lift (K := FractionRing (MvPolynomial ι k)) (L := K)
    (g := (aeval (R := k) (fun i => (y i : K))).toRingHom)
    (show Function.Injective ((aeval (R := k) (fun i => (y i : K))).toRingHom) from
      algebraicIndependent_iff_injective_aeval.mp hy)

/-- The parameter fraction field maps to the actual source localization. -/
def scalarMap : FractionRing (MvPolynomial ι k) →+* Ring D y :=
  IsLocalization.map (M := nonZeroDivisors (MvPolynomial ι k))
    (T := denominators D y) (Ring D y) (aeval y).toRingHom
    (fun f hf => show (aeval y).toRingHom f ∈ denominators D y from
      Submonoid.mem_map.mpr ⟨f, hf, rfl⟩)

/-- The original source inclusion extends across its actual parameter denominators. -/
def point : Ring D y →+* K :=
  IsLocalization.lift (M := denominators D y) (g := D.val.toRingHom)
    (fun s => isUnit_iff_ne_zero.mpr (denominator_ne_zero D y hy s))

/-- The point preserves each original source element. -/
@[simp] theorem point_algebraMap (a : D) :
    point D y hy (algebraMap D (Ring D y) a) = (a : K) :=
  IsLocalization.lift_eq _ a

/-- The two actual maps agree on the parameter fraction field. -/
theorem point_comp_scalarMap :
    (point D y hy).comp (scalarMap D y) = fractionMap D y hy := by
  apply IsFractionRing.ringHom_ext (A := MvPolynomial ι k)
  intro f
  change point D y hy (scalarMap D y (algebraMap _ _ f)) = fractionMap D y hy _
  have hs : scalarMap D y (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) f) = algebraMap D (Ring D y) (aeval y f) := by
    exact IsLocalization.map_eq (M := nonZeroDivisors (MvPolynomial ι k))
      (S := FractionRing (MvPolynomial ι k)) (T := denominators D y)
      (Q := Ring D y) (g := (aeval y).toRingHom)
      (fun f hf => show (aeval y).toRingHom f ∈ denominators D y from
        Submonoid.mem_map.mpr ⟨f, hf, rfl⟩) f
  rw [hs, point_algebraMap, fractionMap, IsFractionRing.lift_algebraMap]
  exact coe_aeval D y f

/-- The actual source localization still embeds in the original field. -/
theorem point_injective : Function.Injective (point D y hy) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (denominators D y)
    (point D y hy)).mpr
  intro a b
  simp only [point_algebraMap, Subtype.coe_inj]
  constructor
  · intro h
    have h' := congrArg (point D y hy) h
    simpa only [point_algebraMap, Subtype.coe_inj] using h'
  · exact congrArg (algebraMap D (Ring D y))

/-- Algebraicity over the actual parameter field makes the localized point surjective. -/
theorem point_surjective [IsFractionRing D K] :
    let := (fractionMap D y hy).toAlgebra
    Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K →
      Function.Surjective (point D y hy) := by
  let := (fractionMap D y hy).toAlgebra
  change Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K →
    Function.Surjective (point D y hy)
  intro halg
  let := halg
  let := (scalarMap D y).toAlgebra
  let φ : Ring D y →ₐ[FractionRing (MvPolynomial ι k)] K :=
    { point D y hy with commutes' := fun z =>
        DFunLike.congr_fun (point_comp_scalarMap D y hy) z }
  intro z
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective D z
  have ha : (a : K) ∈ φ.range := ⟨algebraMap D (Ring D y) a, point_algebraMap D y hy a⟩
  have hb : (b : K) ∈ φ.range := ⟨algebraMap D (Ring D y) b, point_algebraMap D y hy b⟩
  have hbinv : (b : K)⁻¹ ∈ φ.range :=
    φ.range.inv_mem_of_algebraic (x := ⟨(b : K), hb⟩)
      (Algebra.IsAlgebraic.isAlgebraic (b : K))
  have hzmem : z ∈ φ.range := by
    rw [← hz, div_eq_mul_inv]
    exact φ.range.mul_mem ha hbinv
  exact hzmem

/-- The parameter localization is the given fraction field, through its actual point. -/
def ringEquiv [IsFractionRing D K]
    (halg : letI := (fractionMap D y hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K) : Ring D y ≃+* K :=
  RingEquiv.ofBijective (point D y hy)
    ⟨point_injective D y hy, point_surjective D y hy halg⟩

/-- The identification preserves each original source element literally. -/
@[simp] theorem ringEquiv_algebraMap [IsFractionRing D K]
    (halg : letI := (fractionMap D y hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K) (a : D) :
    ringEquiv D y hy halg (algebraMap D (Ring D y) a) = (a : K) :=
  point_algebraMap D y hy a

end SeparatingParameterLocalization
