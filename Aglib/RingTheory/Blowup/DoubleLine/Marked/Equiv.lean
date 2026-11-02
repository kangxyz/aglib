/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Cotangent.Equiv
public import Aglib.RingTheory.Blowup.DoubleLine.Marked

/-!
# Full marked data on the same original rings under native equivalences

The genuine ring equivalence transports the original maximal-ideal elements,
entire canonical cotangent kernel, cubic equation and original residue map.
No transported marker, kernel, or residue identification is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

local instance IsLocalRing.ringEquiv_toRingHom_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) : IsLocalHom e.toRingHom :=
  IsLocalHom.of_surjective e.toRingHom e.surjective

namespace IsLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]

/-- Apply the original ring equivalence to an original maximal-ideal element. -/
def maximalIdealEquivMap (e : A ≃+* B) (t : maximalIdeal A) : maximalIdeal B :=
  ⟨e.toRingHom t, map_nonunit e.toRingHom t t.property⟩

@[simp] theorem maximalIdealEquivMap_val (e : A ≃+* B) (t : maximalIdeal A) :
    (maximalIdealEquivMap e t : B) = e t := rfl

/-- The entire original canonical kernel is transported through the actual
original residue-field map induced by the native ring equivalence. -/
theorem doubleLineChildCotangentKernel_ringEquiv (e : A ≃+* B)
    (g : Fin 3 → maximalIdeal A) :
    doubleLineChildCotangentKernel B (fun i => maximalIdealEquivMap e (g i)) =
      (doubleLineChildCotangentKernel A g).map
        (MvPolynomial.mapEquiv (Fin 3) (ResidueField.mapEquiv e)).toRingHom := by
  have hquot : Ideal.quotientEquiv (maximalIdeal A) (maximalIdeal B) e
      (map_ringEquiv_maximalIdeal e).symm = ResidueField.mapEquiv e := by
    ext a
    obtain ⟨a, rfl⟩ := residue_surjective (R := A) a
    rfl
  have h := Ideal.cotangentPolynomialMap_kernel_equiv_of_eq e
    (maximalIdeal A) (maximalIdeal B) (map_ringEquiv_maximalIdeal e) g
  simp only [hquot] at h
  dsimp only [doubleLineChildCotangentKernel, maximalIdealEquivMap, ResidueField,
    ResidueField.field, Ideal.associatedGradedCommRing] at h ⊢
  exact h

/-- The same actual triple generates the original target maximal ideal. -/
theorem maximalIdeal_span_triple_ringEquiv (e : A ≃+* B) (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A)) :
    maximalIdeal B = Ideal.span ({(maximalIdealEquivMap e t : B),
      (maximalIdealEquivMap e s : B), (maximalIdealEquivMap e z : B)} : Set B) := by
  have h := congrArg (fun I : Ideal A => I.map e.toRingHom) hgen
  have hm : (maximalIdeal A).map e.toRingHom = maximalIdeal B :=
    map_ringEquiv_maximalIdeal e
  rw [hm, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton] at h
  exact h

/-- A normalized full square kernel remains the same normalized full kernel. -/
theorem doubleLineChildCotangentKernel_square_ringEquiv (e : A ≃+* B) (t s z : maximalIdeal A)
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    doubleLineChildCotangentKernel B
        ![maximalIdealEquivMap e s, maximalIdealEquivMap e z, maximalIdealEquivMap e t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField B)) ^ 2} := by
  have hg : (fun i => maximalIdealEquivMap e (![s, z, t] i)) =
      ![maximalIdealEquivMap e s, maximalIdealEquivMap e z, maximalIdealEquivMap e t] := by
    funext i
    fin_cases i <;> rfl
  rw [← hg, doubleLineChildCotangentKernel_ringEquiv, hker,
    Ideal.map_span, Set.image_singleton, map_pow]
  change Ideal.span {(MvPolynomial.map (ResidueField.mapEquiv e).toRingHom
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A))) ^ 2} = _
  rw [MvPolynomial.map_X]

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The same ten original cubic coefficients through a native ring homomorphism. -/
def CubicCoefficients.map (C : CubicCoefficients A) (f : A →+* B) : CubicCoefficients B :=
  ⟨f C.a0, f C.a1, f C.a2, f C.a3, f C.b0, f C.b1, f C.b2,
    f C.c0, f C.c1, f C.d0⟩

/-- Evaluation of the same fixed cubic commutes with its original coefficient map. -/
theorem CubicCoefficients.map_value (C : CubicCoefficients A) (f : A →+* B)
    (t s z : A) : (C.map f).value (f t) (f s) (f z) = f (C.value t s z) := by
  simp only [CubicCoefficients.map, CubicCoefficients.value, map_add, map_mul, map_pow]

variable [IsLocalRing A] [IsLocalRing B]
open IsLocalRing

/-- Transport the true cubic and its genuine fourth-order remainder. -/
def CubicRelation.map {t s z : maximalIdeal A} (F : CubicRelation t s z) (e : A ≃+* B) :
    CubicRelation (maximalIdealEquivMap e t) (maximalIdealEquivMap e s)
      (maximalIdealEquivMap e z) where
  coefficients := F.coefficients.map e.toRingHom
  remainder := e.toRingHom F.remainder
  remainder_mem := by
    have h := Ideal.mem_map_of_mem e.toRingHom F.remainder_mem
    have hm : (maximalIdeal A).map e.toRingHom = maximalIdeal B :=
      map_ringEquiv_maximalIdeal e
    rwa [Ideal.map_pow, hm] at h
  equation := by
    change (F.coefficients.map e.toRingHom).value (e.toRingHom t) (e.toRingHom s)
      (e.toRingHom z) + e.toRingHom F.remainder = 0
    rw [CubicCoefficients.map_value, ← map_add, F.equation, map_zero]

@[simp] theorem CubicRelation.map_remainder {t s z : maximalIdeal A}
    (F : CubicRelation t s z) (e : A ≃+* B) : (F.map e).remainder = e F.remainder := rfl

end Localization.Away.SaturatedChart

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]

/-- Transport the full corrected marker, including its entire original
canonical kernel and its simple-root conditions through the original residue map. -/
def MarkedCubic.map {t : maximalIdeal A} (M : MarkedCubic t) (e : A ≃+* B) :
    MarkedCubic (maximalIdealEquivMap e t) where
  other := maximalIdealEquivMap e M.other
  square := maximalIdealEquivMap e M.square
  generates := maximalIdeal_span_triple_ringEquiv e t M.other M.square M.generates
  tangent := doubleLineChildCotangentKernel_square_ringEquiv e t M.other M.square M.tangent
  relation := M.relation.map e
  constant_at_infinity := by
    change residue B (e.toRingHom M.relation.coefficients.a3) = 0
    rw [← ResidueField.map_residue e.toRingHom, M.constant_at_infinity, map_zero]
  linear_at_infinity := by
    change residue B (e.toRingHom M.relation.coefficients.a2) ≠ 0
    rw [← ResidueField.map_residue e.toRingHom]
    exact (map_ne_zero_iff (ResidueField.map e.toRingHom)
      (ResidueField.mapEquiv e).injective).mpr M.linear_at_infinity

@[simp] theorem MarkedCubic.map_other {t : maximalIdeal A} (M : MarkedCubic t) (e : A ≃+* B) :
    (M.map e).other = maximalIdealEquivMap e M.other := rfl

@[simp] theorem MarkedCubic.map_square {t : maximalIdeal A} (M : MarkedCubic t) (e : A ≃+* B) :
    (M.map e).square = maximalIdealEquivMap e M.square := rfl

/-- The distinguished coefficient is still transported by the original residue map. -/
theorem MarkedCubic.map_a2_residue {t : maximalIdeal A} (M : MarkedCubic t) (e : A ≃+* B) :
    residue B (M.map e).relation.coefficients.a2 =
      ResidueField.map e.toRingHom (residue A M.relation.coefficients.a2) :=
  (ResidueField.map_residue e.toRingHom M.relation.coefficients.a2).symm

/-- Transport every field of the genuine first triple-entry identity,
including its full canonical kernel on the actual transported generators. -/
def TripleEntryData.map {t s z : maximalIdeal A} (T : TripleEntryData t s z) (e : A ≃+* B) :
    TripleEntryData (maximalIdealEquivMap e t) (maximalIdealEquivMap e s)
      (maximalIdealEquivMap e z) where
  coefficient := e.toRingHom T.coefficient
  coefficient_unit := T.coefficient_unit.map e.toRingHom
  P := e.toRingHom T.P
  Q := e.toRingHom T.Q
  P_mem := map_nonunit e.toRingHom T.P T.P_mem
  Q_mem := map_nonunit e.toRingHom T.Q T.Q_mem
  generates := maximalIdeal_span_triple_ringEquiv e t s z T.generates
  tangent := doubleLineChildCotangentKernel_square_ringEquiv e t s z T.tangent
  equation := by
    change (e.toRingHom z) ^ 2 + e.toRingHom T.coefficient * (e.toRingHom t) *
      (e.toRingHom s) ^ 3 + (e.toRingHom t) * (e.toRingHom z) * e.toRingHom T.P +
        (e.toRingHom t) ^ 2 * e.toRingHom T.Q = 0
    simpa only [map_add, map_mul, map_pow, map_zero] using congrArg e.toRingHom T.equation

@[simp] theorem TripleEntryData.map_coefficient {t s z : maximalIdeal A}
    (T : TripleEntryData t s z) (e : A ≃+* B) : (T.map e).coefficient = e T.coefficient := rfl

/-- The entry coefficient uses the same original residue-field homomorphism. -/
theorem TripleEntryData.map_coefficient_residue {t s z : maximalIdeal A}
    (T : TripleEntryData t s z) (e : A ≃+* B) :
    residue B (T.map e).coefficient = ResidueField.map e.toRingHom (residue A T.coefficient) :=
  (ResidueField.map_residue e.toRingHom T.coefficient).symm

end IsLocalRing
