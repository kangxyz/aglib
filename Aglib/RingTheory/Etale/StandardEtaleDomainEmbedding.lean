/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.StandardEtaleDomainLocalization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # The original factor hypersurface embeds in its standard etale open

The denominator is nonzero because its image is a unit in the original
nontrivial receiving algebra. The embedding is the original root-evaluation
map, identified with the actual localization map, not a chosen abstract
embedding. Flat scalar extension preserves this same injection.
-/

@[expose] public noncomputable section

open Polynomial

namespace StandardEtalePresentation

variable {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]

/-- The denominator of the original factor open is nonzero in its actual
quotient ring. This does not require injectivity of the coefficient map. -/
theorem factor_denominator_ne_zero (P : StandardEtalePresentation R S)
    (p q : R[X]) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    AdjoinRoot.mk p (P.g * q) ≠ 0 := by
  have hd := P.hasMap.isUnit_derivative_f
  rw [hf, derivative_mul, map_add, map_mul, map_mul, hp, zero_mul, add_zero] at hd
  have hu : IsUnit (aeval P.x (P.g * q)) := by
    rw [map_mul]
    exact P.hasMap.2.mul (isUnit_of_mul_isUnit_right hd)
  intro hz
  apply hu.ne_zero
  have hpeval : p.eval₂ (Algebra.ofId R S) P.x = 0 := hp
  calc
    aeval P.x (P.g * q) =
        (AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hpeval)
          (AdjoinRoot.mk p (P.g * q)) := rfl
    _ = (AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hpeval) 0 := congrArg _ hz
    _ = 0 := map_zero _

omit [Nontrivial S] in
/-- The original factor evaluation equals localization followed by the
inverse of the original standard etale presentation isomorphism. -/
theorem factor_lift_eq_localization (P : StandardEtalePresentation R S)
    (p q : R[X]) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hp =
      (P.equivAwayAdjoinRootFactor p q hf hp).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom R (AdjoinRoot p)
          (Localization.Away (AdjoinRoot.mk p (P.g * q)))) := by
  apply AdjoinRoot.algHom_ext
  let e := P.equivAwayAdjoinRootFactor p q hf hp
  change (AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hp) (AdjoinRoot.root p) =
    e.symm (algebraMap (AdjoinRoot p) _ (AdjoinRoot.root p))
  calc
    _ = P.x := AdjoinRoot.liftAlgHom_root p (Algebra.ofId R S) P.x hp
    _ = e.symm (e P.x) := (e.symm_apply_apply P.x).symm
    _ = _ := congrArg e.symm (P.equivAwayAdjoinRootFactor_x p q hf hp)


/-- The original root evaluation of an irreducible factor is injective.
The UFD condition is imposed on the actual polynomial ring. -/
theorem factor_lift_injective [UniqueFactorizationMonoid R[X]]
    (P : StandardEtalePresentation R S) (p q : R[X])
    (hirr : Irreducible p) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    Function.Injective (AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hp) := by
  let : IsDomain (AdjoinRoot p) :=
    AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  have hj := IsLocalization.injective
    (Localization.Away (AdjoinRoot.mk p (P.g * q)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (P.factor_denominator_ne_zero p q hf hp))
  rw [P.factor_lift_eq_localization p q hf hp]
  exact (P.equivAwayAdjoinRootFactor p q hf hp).symm.injective.comp hj

/-- Flat extension of scalars preserves the same original factor embedding.
The smaller base ring may be a field below the original coefficient ring. -/
theorem lTensor_factor_lift_injective [UniqueFactorizationMonoid R[X]]
    {K L : Type*} [CommRing K] [Algebra K R] [Algebra K S] [IsScalarTower K R S]
    [AddCommGroup L] [Module K L] [Module.Flat K L]
    (P : StandardEtalePresentation R S) (p q : R[X])
    (hirr : Irreducible p) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    Function.Injective (LinearMap.lTensor L
      ((AdjoinRoot.liftAlgHom p (Algebra.ofId R S) P.x hp).restrictScalars K).toLinearMap) := by
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact P.factor_lift_injective p q hirr hf hp

end StandardEtalePresentation
