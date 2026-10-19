/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Spectrum.Prime.Bijectivity

/-! Focused consumer of bijectivity from bijectivity on every residue-field fibre (the Nakayama
step of Nitsure, arXiv:math/0504590v1, Thm 4.3 (ii), pp. 22–23), with axiom guards. -/

@[expose] public section

open scoped TensorProduct

/-- A fibrewise isomorphism of finite modules onto a finite projective module is an
isomorphism; no Noetherian hypothesis. -/
example {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R, Function.Bijective (f.baseChange p.asIdeal.ResidueField)) :
    Function.Bijective f :=
  LinearMap.bijective_of_residueField_baseChange_bijective f h

/-- Nakayama at every prime. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M)) :
    Subsingleton M :=
  Module.subsingleton_of_subsingleton_residueField_tensorProduct h

/--
info: 'Module.subsingleton_of_subsingleton_residueField_tensorProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.subsingleton_of_subsingleton_residueField_tensorProduct

/--
info: 'LinearMap.surjective_of_residueField_baseChange_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.surjective_of_residueField_baseChange_surjective

/--
info: 'LinearMap.injective_of_surjective_of_residueField_baseChange_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.injective_of_surjective_of_residueField_baseChange_injective

/--
info: 'LinearMap.bijective_of_residueField_baseChange_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.bijective_of_residueField_baseChange_bijective
