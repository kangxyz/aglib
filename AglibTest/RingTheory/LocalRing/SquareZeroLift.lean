/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.LocalRing.SquareZeroLift
public import Mathlib.Algebra.DualNumber

/-! Focused consumer of square-zero lifts of a rational point of a local algebra: lifts to
`L[ε]` are `k`-linear maps on the cotangent space, naturally in the module; derivations into a
module killed by the maximal ideal are the cotangent maps; and the cotangent space of a
Noetherian local algebra with residue field `k` is finite-dimensional. -/

@[expose] public section

open IsLocalRing

variable {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] (ψ : A →ₐ[k] k)
variable (L : Type*) [Field L] [Algebra k L]

example : RingHom.ker ψ = maximalIdeal A := ker_algHom_eq_maximalIdeal ψ

example :
    {φ : A →ₐ[k] DualNumber L //
      (TrivSqZeroExt.fstHom k L L).comp φ = (Algebra.ofId k L).comp ψ} ≃
      (CotangentSpace A →ₗ[k] L) :=
  trivSqZeroExtLiftEquiv ψ L L

example (θ : CotangentSpace A →ₗ[k] L) (a : A) :
    ((trivSqZeroExtLiftEquiv ψ L L).symm θ).1 a =
      ⟨algebraMap k L (ψ a), θ (cotangentDeviation ψ a)⟩ :=
  rfl

example (a b : A) :
    cotangentDeviation ψ (a * b) =
      ψ a • cotangentDeviation ψ b + ψ b • cotangentDeviation ψ a :=
  cotangentDeviation_mul ψ a b

/-- Naturality for the projection `L × L → L`. -/
example (θ : CotangentSpace A →ₗ[k] L × L) :
    ((TrivSqZeroExt.map (LinearMap.fst L L L)).restrictScalars k).comp
        (trivSqZeroExtLift ψ θ) =
      trivSqZeroExtLift ψ (((LinearMap.fst L L L).restrictScalars k).comp θ) :=
  map_comp_trivSqZeroExtLift _ θ

example [IsNoetherianRing A] : Module.Finite k (CotangentSpace A) :=
  finite_cotangentSpace_of_algHom ψ

/-- Lifts to `L[ε]` are the derivations `A → L`, with `A` acting on `L` through `ψ`. -/
example (φ : {φ : A →ₐ[k] DualNumber L //
      (TrivSqZeroExt.fstHom k L L).comp φ = (Algebra.ofId k L).comp ψ}) (a : A) :
    trivSqZeroExtLiftEquivDerivation ψ L L φ a = (φ.1 a).snd :=
  trivSqZeroExtLiftEquivDerivation_apply ψ L L φ a

/-- Derivations into a module killed by the maximal ideal are the cotangent maps. -/
example {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    (hN : ∀ x ∈ maximalIdeal A, ∀ n : N, x • n = 0) :
    Derivation k A N ≃ₗ[k] (CotangentSpace A →ₗ[k] N) :=
  derivationEquivCotangentSpace ψ N hN

/-- The identity of `𝔪/𝔪²` corresponds to the derivation `a ↦ [a - ψ a]`. -/
example :
    (derivationEquivCotangentSpace ψ (CotangentSpace A)
      fun _ hx z => Ideal.Cotangent.smul_eq_zero_of_mem hx z).symm LinearMap.id =
      cotangentDerivation ψ :=
  Derivation.ext fun _ => rfl

/--
info: 'IsLocalRing.trivSqZeroExtLiftEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trivSqZeroExtLiftEquiv

/--
info: 'IsLocalRing.map_comp_trivSqZeroExtLift' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms map_comp_trivSqZeroExtLift

/--
info: 'IsLocalRing.finite_cotangentSpace_of_algHom' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_cotangentSpace_of_algHom

/--
info: 'IsLocalRing.derivationEquivCotangentSpace' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derivationEquivCotangentSpace
