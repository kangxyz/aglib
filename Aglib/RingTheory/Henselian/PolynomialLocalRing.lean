/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Polynomial local rings at the coefficient maximal ideal and the origin

The objects are native localizations of finite-variable polynomial rings at
`(maximalIdeal R, X)`, defined by constant-coefficient preimage. The lower-variable
inclusion sends `i` to `swap 0 (Fin.last n) i.succ`, matching the actual
`MvPowerSeries.finLastEquiv`, rather than silently using `Fin.castSucc`.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The origin over the coefficient maximal ideal, as an actual polynomial ideal. -/
def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) R) :=
  (maximalIdeal R).comap MvPolynomial.constantCoeff

instance originIdeal_isMaximal (n : ℕ) : (originIdeal R n).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective
    (MvPolynomial.constantCoeff : MvPolynomial (Fin n) R →+* R)
    (fun r => ⟨MvPolynomial.C r, MvPolynomial.constantCoeff_C _ _⟩)

/-- The lower variables in the coordinate order used by `finLastEquiv`.
Explicitly, this sends `i` to `Equiv.swap 0 (Fin.last n) i.succ`. -/
def lowerVariableEmbedding (n : ℕ) : Fin n ↪ Fin (n + 1) where
  toFun i := Equiv.swap 0 (Fin.last n) i.succ
  inj' := (Equiv.swap 0 (Fin.last n)).injective.comp (Fin.succ_injective n)

@[simp] theorem lowerVariableEmbedding_apply (n : ℕ) (i : Fin n) :
    lowerVariableEmbedding n i = Equiv.swap 0 (Fin.last n) i.succ := rfl

/-- The origin prime contracts correctly along the actual variable inclusion. -/
theorem originIdeal_comap_rename (n : ℕ) :
    originIdeal R n = (originIdeal R (n + 1)).comap
      (MvPolynomial.rename (lowerVariableEmbedding n)).toRingHom := by
  ext p
  change MvPolynomial.constantCoeff p ∈ maximalIdeal R ↔
    MvPolynomial.constantCoeff (MvPolynomial.rename (lowerVariableEmbedding n) p) ∈ maximalIdeal R
  rw [MvPolynomial.constantCoeff_rename]

end PolynomialLocalRing

/-- The native polynomial localization at the origin over the maximal ideal. -/
abbrev PolynomialLocalRing (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  Localization.AtPrime (PolynomialLocalRing.originIdeal R n)

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The original coefficient map into the polynomial local ring is local. -/
instance algebraMap_isLocalHom (n : ℕ) : IsLocalHom (algebraMap R (PolynomialLocalRing R n)) := by
  constructor
  intro r hr
  apply IsLocalRing.notMem_maximalIdeal.mp
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n)
      (algebraMap R (MvPolynomial (Fin n) R) r)) := by
    simpa only [← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R)
      (PolynomialLocalRing R n)] using hr
  have hn := (IsLocalization.AtPrime.isUnit_to_map_iff
    (PolynomialLocalRing R n) (originIdeal R n) _).mp hu
  change MvPolynomial.constantCoeff (MvPolynomial.C r : MvPolynomial (Fin n) R) ∉
    maximalIdeal R at hn
  simpa only [MvPolynomial.constantCoeff_C] using hn

/-- The actual local map adding the last variable in the `finLastEquiv` ordering. -/
def variableInclusion (n : ℕ) : PolynomialLocalRing R n →ₐ[R] PolynomialLocalRing R (n + 1) :=
  Localization.localAlgHom (originIdeal R n) (originIdeal R (n + 1))
    (MvPolynomial.rename (lowerVariableEmbedding n)) (originIdeal_comap_rename R n)

instance variableInclusion_isLocalHom (n : ℕ) : IsLocalHom (variableInclusion R n).toRingHom := by
  change IsLocalHom (Localization.localRingHom (originIdeal R n) (originIdeal R (n + 1))
    (MvPolynomial.rename (lowerVariableEmbedding n)).toRingHom (originIdeal_comap_rename R n))
  infer_instance

/-- Compatibility with the original polynomial maps, not merely a chosen abstract lift. -/
theorem variableInclusion_algebraMap (n : ℕ) (p : MvPolynomial (Fin n) R) :
    variableInclusion R n (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (PolynomialLocalRing R (n + 1))
        (MvPolynomial.rename (lowerVariableEmbedding n) p) :=
  Localization.localRingHom_to_map (originIdeal R n) (originIdeal R (n + 1))
    (MvPolynomial.rename (lowerVariableEmbedding n)).toRingHom (originIdeal_comap_rename R n) p

end PolynomialLocalRing
