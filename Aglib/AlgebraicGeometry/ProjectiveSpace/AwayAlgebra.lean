/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing

/-!
# Degree-zero localizations of the polynomial grading as `R`-algebras

Mathlib makes `HomogeneousLocalization.Away 𝒜 f` an algebra over `𝒜 0` only. For the
total-degree grading `homogeneousSubmodule ι R` of `MvPolynomial ι R`, this file gives the
`R`-algebra structure `awayAlgebra`, whose algebra map is the coefficient map `awayCoefficient`
(for `f = Xᵢ` this is `coordinateRingCoefficient R ι i`) and whose scalar action is Mathlib's
`HomogeneousLocalization.instSMul`. With it, Mathlib's `awayMap` is a map of `R`-algebras
(`awayMapAlgHom`), algebra maps out of a standard chart ring are determined by the ratios
`X_k / X_i` (`coordinateRing_algHom_ext`), and the restrictions of the charts `D₊(Xᵢ)` and
`D₊(Xₗ)` to their overlap `D₊(Xᵢ Xₗ)` are maps of `R`-algebras (`overlapLeft`, `overlapRight`)
with the ratio identities `X_p / X_l = (X_i / X_l) (X_p / X_i)` (`overlapRight_ratio`) and
`(X_i / X_l) (X_l / X_i) = 1`.

## Caveats on `awayAlgebra`

- Its scalar action agrees with Mathlib's `HomogeneousLocalization.instSMul` only at instances
  transparency, not at reducible transparency. Goals `r • z` over these rings elaborate to
  `instSMul`, and `rw`/`simp` with `zero_smul`, `Algebra.smul_def` or `add_smul` fail on them
  (also under `backward.isDefEq.respectTransparency false`), while term-mode applications of
  these lemmas work. Rewrite with `smul_eq_algebraMap_mul`, whose statement uses `instSMul`, or
  state lemmas with `algebraMap R _ r * _`.
- Over `R = ℤ` it forms the standard `ℤ`-algebra diamond with `Ring.toIntAlgebra`: the two
  instances are equal only propositionally (by subsingleton elimination), not definitionally.

There is no other `Algebra R (HomogeneousLocalization.Away …)` instance in Mathlib or Aglib at this
pin.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {ι : Type u}

/-- The coefficient map `R → (MvPolynomial ι R)_{(f)}` into a degree-zero localization. For
`f = Xᵢ` it is `coordinateRingCoefficient R ι i`. -/
def awayCoefficient (f : MvPolynomial ι R) : R →+* Away (homogeneousSubmodule ι R) f :=
  (fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers f)).comp
    (toHomogeneousSubmoduleZero R ι)

theorem val_awayCoefficient (f : MvPolynomial ι R) (r : R) :
    (awayCoefficient R f r).val =
      algebraMap (MvPolynomial ι R) (Localization.Away f) (C r) := rfl

/-- The `R`-algebra structure on a degree-zero localization of the polynomial ring: the algebra
map is the coefficient map, and the scalar action is Mathlib's action on homogeneous
localizations. See the module documentation for its two caveats (transparency of the scalar
action, and the `ℤ`-algebra diamond). -/
instance awayAlgebra (f : MvPolynomial ι R) : Algebra R (Away (homogeneousSubmodule ι R) f) where
  toSMul := inferInstance
  algebraMap := awayCoefficient R f
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, val_awayCoefficient,
      ← Algebra.smul_def, ← MvPolynomial.algebraMap_eq, algebraMap_smul]

theorem algebraMap_away (f : MvPolynomial ι R) :
    algebraMap R (Away (homogeneousSubmodule ι R) f) = awayCoefficient R f := rfl

theorem algebraMap_coordinateRing (i : ι) :
    algebraMap R (coordinateRing R ι i) = coordinateRingCoefficient R ι i := rfl

/-- The scalar action of `awayAlgebra` as multiplication by the coefficient. The statement is
elaborated with Mathlib's `HomogeneousLocalization.instSMul`, so, unlike `Algebra.smul_def`, it
rewrites goals `r • z` over degree-zero localizations; its proof is the term-mode application of
`Algebra.smul_def`. -/
theorem smul_eq_algebraMap_mul (f : MvPolynomial ι R) (r : R)
    (z : Away (homogeneousSubmodule ι R) f) :
    r • z = algebraMap R (Away (homogeneousSubmodule ι R) f) r * z :=
  Algebra.smul_def r z

variable {R} in
/-- Mathlib's `awayMap` as a map of `R`-algebras. -/
def awayMapAlgHom {f g x : MvPolynomial ι R} {d : ℕ} (hg : g ∈ homogeneousSubmodule ι R d)
    (hx : x = f * g) :
    Away (homogeneousSubmodule ι R) f →ₐ[R] Away (homogeneousSubmodule ι R) x where
  __ := awayMap (homogeneousSubmodule ι R) hg hx
  commutes' _ := awayMap_fromZeroRingHom ..

theorem awayMapAlgHom_toRingHom {f g x : MvPolynomial ι R} {d : ℕ}
    (hg : g ∈ homogeneousSubmodule ι R d) (hx : x = f * g) :
    (awayMapAlgHom hg hx).toRingHom = awayMap (homogeneousSubmodule ι R) hg hx := rfl

/-- Algebra maps out of a standard chart ring agree when they agree on the ratios `X_k / X_i`. -/
theorem coordinateRing_algHom_ext {A : Type*} [CommRing A] [Algebra R A] {i : ι}
    {f g : coordinateRing R ι i →ₐ[R] A}
    (h : ∀ k, f (coordinateRatio R ι i k) = g (coordinateRatio R ι i k)) : f = g := by
  have hp : f.toRingHom.comp (polynomialToCoordinateRing R ι i) =
      g.toRingHom.comp (polynomialToCoordinateRing R ι i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact (f.commutes r).trans (g.commutes r).symm
    · intro j
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact h j.1
  ext z
  have hz := RingHom.congr_fun hp (coordinateRingToPolynomial R ι i z)
  have hinv :=
    RingHom.congr_fun (polynomialToCoordinateRing_comp_coordinateRingToPolynomial R ι i) z
  simp only [RingHom.comp_apply, RingHom.id_apply] at hinv
  simpa only [RingHom.comp_apply, hinv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hz

section Overlap

variable (i l : ι)

/-- The restriction `(MvPolynomial ι R)_{(Xᵢ)} → (MvPolynomial ι R)_{(Xᵢ Xₗ)}`. -/
def overlapLeft :
    coordinateRing R ι i →ₐ[R] Away (homogeneousSubmodule ι R) (X i * X l) :=
  awayMapAlgHom (isHomogeneous_X R l) rfl

/-- The restriction `(MvPolynomial ι R)_{(Xₗ)} → (MvPolynomial ι R)_{(Xᵢ Xₗ)}`. -/
def overlapRight :
    coordinateRing R ι l →ₐ[R] Away (homogeneousSubmodule ι R) (X i * X l) :=
  awayMapAlgHom (isHomogeneous_X R i) (mul_comm (X i) (X l))

theorem val_overlapLeft_ratio (p : ι) :
    (overlapLeft R i l (coordinateRatio R ι i p)).val =
      Localization.mk (X p * X l) ⟨X i * X l, Submonoid.mem_powers _⟩ := by
  change (awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R l) rfl
    (coordinateRatio R ι i p)).val = _
  rw [coordinateRatio, awayMap_mk, Away.val_mk]
  congr 1 <;> simp

theorem val_overlapRight_ratio (p : ι) :
    (overlapRight R i l (coordinateRatio R ι l p)).val =
      Localization.mk (X p * X i) ⟨X i * X l, Submonoid.mem_powers _⟩ := by
  change (awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R i) (mul_comm (X i) (X l))
    (coordinateRatio R ι l p)).val = _
  rw [coordinateRatio, awayMap_mk, Away.val_mk]
  congr 1 <;> simp

/-- On the overlap, `X_p / X_l = (X_i / X_l) (X_p / X_i)`. -/
theorem overlapRight_ratio (p : ι) :
    overlapRight R i l (coordinateRatio R ι l p) =
      overlapRight R i l (coordinateRatio R ι l i) *
        overlapLeft R i l (coordinateRatio R ι i p) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_overlapRight_ratio, val_overlapRight_ratio,
    val_overlapLeft_ratio, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

/-- On the overlap, `(X_i / X_l) (X_l / X_i) = 1`. -/
theorem overlapRight_ratio_mul_overlapLeft_ratio :
    overlapRight R i l (coordinateRatio R ι l i) *
      overlapLeft R i l (coordinateRatio R ι i l) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_overlapRight_ratio, val_overlapLeft_ratio,
    HomogeneousLocalization.val_one, Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, mul_one]; ring⟩

theorem isUnit_overlapLeft_ratio : IsUnit (overlapLeft R i l (coordinateRatio R ι i l)) :=
  IsUnit.of_mul_eq_one_right _ (overlapRight_ratio_mul_overlapLeft_ratio R i l)

theorem isUnit_overlapRight_ratio : IsUnit (overlapRight R i l (coordinateRatio R ι l i)) :=
  IsUnit.of_mul_eq_one _ (overlapRight_ratio_mul_overlapLeft_ratio R i l)

/-- The element `X_l / X_i` of `B_i` at which `B_{il}` is Mathlib's localization of `B_i`. -/
abbrev overlapElem : coordinateRing R ι i :=
  Away.isLocalizationElem (𝒜 := homogeneousSubmodule ι R) (isHomogeneous_X R i)
    (isHomogeneous_X R l)

theorem overlapElem_eq : overlapElem R i l = coordinateRatio R ι i l := by
  apply HomogeneousLocalization.val_injective
  simp [coordinateRatio, Away.val_mk]

end Overlap

end AlgebraicGeometry.ProjectiveSpace
