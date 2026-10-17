/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Grassmannian

/-!
# The component formula for the base change of Grassmannian points

Mathlib's `Module.Grassmannian.map` is defined through `Module.Grassmannian.baseChangeMkQ`,
whose body `N.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap` is not exposed:
outside `Mathlib.RingTheory.Grassmannian` even `baseChangeMkQ.eq_1` is unknown, and the public
API (`baseChangeMkQ_surjective`, `map_toSubmodule`, `map_id`, `map_comp`) does not determine the
values of `map`. The component formula on pure tensors is therefore recorded as the named
premise `BaseChangeMkQFormula`. It is the statement of the upstream lemma that an exposure of
`baseChangeMkQ` (or an upstream `baseChangeMkQ_tmul`) would prove; no instance is provided here.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

/-- The component formula of Mathlib's `baseChangeMkQ` for algebras in universe `w`:
`baseChangeMkQ B N (b ⊗ m) = b ⊗ [1 ⊗ m]`. Mathlib's definition satisfies it, but its body is not
exposed, so it is a named premise until an upstream exposure supplies it. -/
class BaseChangeMkQFormula (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] : Prop where
  baseChangeMkQ_tmul {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M)) (b : B) (m : M) :
    baseChangeMkQ B N (b ⊗ₜ[R] m) = b ⊗ₜ[A] N.mkQ ((1 : A) ⊗ₜ[R] m)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]
variable [Algebra A B] [IsScalarTower R A B]

/-- `baseChangeMkQ` sends `b ⊗ m` to `b ⊗ [1 ⊗ m]`, under the premise `BaseChangeMkQFormula`. -/
@[simp]
theorem baseChangeMkQ_tmul [BaseChangeMkQFormula.{u, v, w} R M] (N : Submodule A (A ⊗[R] M))
    (b : B) (m : M) :
    baseChangeMkQ B N (b ⊗ₜ[R] m) = b ⊗ₜ[A] N.mkQ ((1 : A) ⊗ₜ[R] m) :=
  BaseChangeMkQFormula.baseChangeMkQ_tmul N b m

/-- The isomorphism `(B ⊗[R] M) ⧸ ker (baseChangeMkQ B N) ≃ B ⊗[A] ((A ⊗[R] M) ⧸ N)` induced
by `baseChangeMkQ`, built from Mathlib's public `quotKerEquivOfSurjective`. -/
noncomputable abbrev baseChangeMkQQuotEquiv (N : Submodule A (A ⊗[R] M)) :
    ((B ⊗[R] M) ⧸ LinearMap.ker (baseChangeMkQ B N)) ≃ₗ[B] B ⊗[A] ((A ⊗[R] M) ⧸ N) :=
  (baseChangeMkQ B N).quotKerEquivOfSurjective (baseChangeMkQ_surjective N)

@[simp]
theorem baseChangeMkQQuotEquiv_mk (N : Submodule A (A ⊗[R] M)) (v : B ⊗[R] M) :
    baseChangeMkQQuotEquiv N (Submodule.Quotient.mk v) = baseChangeMkQ B N v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ v

end Module.Grassmannian
