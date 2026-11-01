/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Hypersurface
public import Aglib.RingTheory.MvPolynomial.FractionFieldSpreading

/-! # The original generic comparison for a cleared hypersurface

Clearing the original polynomial's coefficients retains its exact scalar
multiple equation. The original tensor quotient is then identified with the
original generic hypersurface, since multiplication by that nonzero field
scalar does not change its defining ideal. The actual scheme comparison
retains the original structural map to the fraction field.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hypersurface

universe u v


/-- Construct the whole original generic scheme comparison from the original
scalar algebra equivalence, including its structural triangle, before
specializing either quotient algebra. -/
theorem exists_generic_iso_of_tensor_equiv
    (R K B T : Type u) [CommRing R] [CommRing K] [CommRing B] [CommRing T]
    [Algebra R K] [Algebra R B] [Algebra K T]
    (eA : K ⊗[R] B ≃ₐ[K] T) :
    ∃ e : pullback (Spec.algebraMap R B) (Spec.algebraMap R K) ≅ Spec (.of T),
      e.hom ≫ Spec.algebraMap K T =
        pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R K) := by
  let H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R K B)).flip
  let eS : Spec (.of (K ⊗[R] B)) ≅ Spec (.of T) :=
    Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op
  let e := H.isoPullback.symm ≪≫ eS
  have hscalar : eS.hom ≫ Spec.algebraMap K T = Spec.algebraMap K (K ⊗[R] B) := by
    change Spec.map (CommRingCat.ofHom eA.symm.toRingHom) ≫
      Spec.algebraMap K T = Spec.algebraMap K (K ⊗[R] B)
    exact Spec.map_algHom_algebraMap eA.symm.toAlgHom
  refine ⟨e, ?_⟩
  change (H.isoPullback.inv ≫ eS.hom) ≫ Spec.algebraMap K T = _
  rw [Category.assoc, hscalar]
  exact H.isoPullback_inv_snd

/-- A fraction-field hypersurface irreducible over the supplied algebraically
closed extension has a coefficient-cleared model with an actual generic
comparison. One original principal base open makes every field coefficient
image of the same cleared polynomial irreducible. Neither properness nor a
Noetherian or perfect-field condition is imposed. -/
theorem exists_cleared_generic_iso
    (R K Ω : Type (max u v)) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {σ : Type v} [Finite σ] (P : MvPolynomial σ K)
    (hP : Irreducible (MvPolynomial.map (algebraMap K Ω) P)) :
    ∃ a : R, a ≠ 0 ∧ ∃ Q : MvPolynomial σ R,
      MvPolynomial.map (algebraMap R K) Q = MvPolynomial.C (algebraMap R K a) * P ∧
      ∃ s : R, s ≠ 0 ∧ a ∣ s ∧
        (∀ (L : Type (max u v)) [Field L] (φ : R →+* L), φ s ≠ 0 →
          Irreducible (MvPolynomial.map φ Q)) ∧
        ∃ e : pullback
            (Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {Q}))
            (Spec.algebraMap R K) ≅ Spec (.of (MvPolynomial σ K ⧸ Ideal.span {P})),
          e.hom ≫ Spec.algebraMap K (MvPolynomial σ K ⧸ Ideal.span {P}) =
            pullback.snd
              (Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {Q}))
              (Spec.algebraMap R K) := by
  obtain ⟨a, ha, Q, hQ, s, hs, has, hall⟩ :=
    MvPolynomial.exists_cleared_forall_irreducible_map (R := R) P hP
  have haK : algebraMap R K a ≠ 0 := by
    intro h
    exact ha (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  have hI : Ideal.span {MvPolynomial.map (algebraMap R K) Q} = Ideal.span {P} := by
    rw [hQ]
    exact Ideal.span_singleton_mul_left_unit
      ((isUnit_iff_ne_zero.mpr haK).map MvPolynomial.C) P
  let B := MvPolynomial σ R ⧸ Ideal.span {Q}
  let T := MvPolynomial σ K ⧸ Ideal.span {P}
  let eA : K ⊗[R] B ≃ₐ[K] T :=
    (MvPolynomial.tensorQuotientSpanSingletonEquiv (S := K) Q).trans
      (Ideal.quotientEquivAlgOfEq K hI)
  obtain ⟨e, he⟩ := exists_generic_iso_of_tensor_equiv R K B T eA
  exact ⟨a, ha, Q, hQ, s, hs, has, hall, e, he⟩

end AlgebraicGeometry.Scheme.Hypersurface
