/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Algebraic differential bases from actual dual derivations

A finite algebraically generating family with dual derivations gives a basis
of the ordinary Kähler module. Its coordinates on `d a` are those same
derivations applied to `a`.
-/

@[expose] public noncomputable section

open Module

namespace KaehlerDifferential

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The original derivations, lifted by the universal property of algebraic differentials. -/
def derivationCoordinates (δ : ι → Derivation R A A) :
    KaehlerDifferential R A →ₗ[A] (ι → A) :=
  LinearMap.pi fun i => (δ i).liftKaehlerDifferential

@[simp]
theorem derivationCoordinates_D (δ : ι → Derivation R A A) (a : A) (i : ι) :
    derivationCoordinates δ (D R A a) i = δ i a :=
  Derivation.liftKaehlerDifferential_comp_D _ _

variable [Fintype ι]

/-- The finite linear combination of the original generator differentials. -/
def differentialCombination (g : ι → A) :
    (ι → A) →ₗ[A] KaehlerDifferential R A where
  toFun v := ∑ i, v i • D R A (g i)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    change (∑ i, (a * v i) • D R A (g i)) = a • ∑ i, v i • D R A (g i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_smul a (v i) (D R A (g i))

@[simp]
theorem differentialCombination_apply (g : ι → A) (v : ι → A) :
    differentialCombination (R := R) g v = ∑ i, v i • D R A (g i) := rfl

variable [DecidableEq ι]

theorem derivationCoordinates_differentialCombination (g : ι → A)
    (δ : ι → Derivation R A A) (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
    (v : ι → A) :
    derivationCoordinates δ (differentialCombination g v) = v := by
  ext i
  change (δ i).liftKaehlerDifferential (∑ j, v j • D R A (g j)) = v i
  simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D, hδ]
  simp

theorem differentialCombination_derivationCoordinates (g : ι → A)
    (δ : ι → Derivation R A A) (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) :
    (differentialCombination (R := R) g).comp (derivationCoordinates δ) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext_of_adjoin_eq_top (Set.range g) hgen
  rintro _ ⟨i, rfl⟩
  change differentialCombination g (derivationCoordinates δ (D R A (g i))) = D R A (g i)
  have hcoord : derivationCoordinates δ (D R A (g i)) = fun j => δ j (g i) :=
    funext fun j => derivationCoordinates_D δ (g i) j
  rw [hcoord, differentialCombination_apply]
  simp only [hδ]
  simp

/-- The coordinate equivalence is built from the supplied original derivations. -/
def differentialCoordinateEquiv (g : ι → A) (δ : ι → Derivation R A A)
    (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) :
    KaehlerDifferential R A ≃ₗ[A] (ι → A) where
  __ := derivationCoordinates δ
  invFun := differentialCombination g
  left_inv ω := LinearMap.congr_fun
    (differentialCombination_derivationCoordinates g δ hgen hδ) ω
  right_inv v := derivationCoordinates_differentialCombination g δ hδ v

/-- Actual algebraic generators and dual derivations give the ordinary Kähler basis. -/
def basisOfDerivations (g : ι → A) (δ : ι → Derivation R A A)
    (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) :
    Basis ι A (KaehlerDifferential R A) :=
  Basis.ofEquivFun (differentialCoordinateEquiv g δ hgen hδ)

@[simp]
theorem basisOfDerivations_apply (g : ι → A) (δ : ι → Derivation R A A)
    (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) (i : ι) :
    basisOfDerivations g δ hgen hδ i = D R A (g i) := by
  rw [basisOfDerivations, Basis.coe_ofEquivFun]
  change differentialCombination g (Pi.single i 1) = D R A (g i)
  simp [differentialCombination_apply, Pi.single_apply]

@[simp]
theorem basisOfDerivations_repr_D (g : ι → A) (δ : ι → Derivation R A A)
    (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) (a : A) (i : ι) :
    (basisOfDerivations g δ hgen hδ).repr (D R A a) i = δ i a := by
  change derivationCoordinates δ (D R A a) i = δ i a
  exact derivationCoordinates_D δ a i

end KaehlerDifferential
