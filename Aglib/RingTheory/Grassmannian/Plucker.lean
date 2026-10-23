/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.BaseChange
public import Aglib.RingTheory.Grassmannian.MapCriterion

/-!
# The Plücker map on points of the Grassmannian functor

Let `M` be an `R`-module, `A` an `R`-algebra and `N ∈ G(k, A ⊗[R] M; A)`, so that the quotient
`Q = (A ⊗[R] M) ⧸ N` is finite projective of constant rank `k`.

* `Module.Grassmannian.pluckerMap k N : A ⊗[R] ⋀[R]^k M →ₗ[A] ⋀[A]^k ((A ⊗[R] M) ⧸ N)`,
  `a ⊗ (m₁ ∧ ⋯ ∧ m_k) ↦ a • [1 ⊗ m₁] ∧ ⋯ ∧ [1 ⊗ m_k]` (`pluckerMap_tmul`): the base-change map
  `A ⊗[R] ⋀[R]^k M → ⋀[A]^k (A ⊗[R] M)` followed by `⋀^k` of the quotient map. It is surjective
  (`pluckerMap_surjective`).
* `Module.Grassmannian.plucker N : G(1, A ⊗[R] ⋀[R]^k M; A)` is its kernel: `⋀[A]^k Q` is finite
  projective of rank `k.choose k = 1` at every prime (`exteriorPower.rankAtStalk_exteriorPower`).
* `Module.Grassmannian.map_plucker`: Mathlib's base change `map f` of points commutes with
  `plucker`. Hence `Module.Grassmannian.pluckerNatTrans R M k` is a natural transformation from
  `Module.Grassmannian.functor k` (for `M`) to `Module.Grassmannian.functor 1` (for `⋀[R]^k M`) of
  functors on `R`-algebras.

This is the Plücker morphism of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §1, p. 5 (item (2): the closed embedding `Grass(r, d) ↪ P(π_* det U)`) and
p. 9 ("Projective embedding": the Plücker coordinates `σ_I`), on points of Mathlib's Grassmannian
functor: the rank-one quotient of a point is the top exterior power `det Q = ⋀^k Q` of its quotient.
Stacks, Section 27.22 (Tag 089R) has no Plücker embedding. The naturality uses `map_eq_of_forall`,
whose module imports the instance of the named premise `BaseChangeMkQFormula`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

universe u v w

namespace Module.Grassmannian

section PluckerMap

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (k : ℕ)
  {A : Type w} [CommRing A] [Algebra R A]

/-- The **Plücker map** of a submodule `N` of `A ⊗[R] M`:
`A ⊗[R] ⋀[R]^k M → ⋀[A]^k (A ⊗[R] M) → ⋀[A]^k ((A ⊗[R] M) ⧸ N)`. -/
def pluckerMap (N : Submodule A (A ⊗[R] M)) :
    A ⊗[R] ⋀[R]^k M →ₗ[A] ⋀[A]^k ((A ⊗[R] M) ⧸ N) :=
  exteriorPower.map k N.mkQ ∘ₗ (exteriorPower.toBaseChange R A k M).liftBaseChange A

theorem pluckerMap_tmul (N : Submodule A (A ⊗[R] M)) (a : A) (v : Fin k → M) :
    pluckerMap k N (a ⊗ₜ exteriorPower.ιMulti R k v) =
      a • exteriorPower.ιMulti A k (fun i => N.mkQ ((1 : A) ⊗ₜ[R] v i)) := by
  rw [pluckerMap, LinearMap.comp_apply, exteriorPower.liftBaseChange_toBaseChange_tmul,
    LinearMap.map_smul, exteriorPower.map_apply_ιMulti]
  rfl

theorem pluckerMap_surjective (N : Submodule A (A ⊗[R] M)) :
    Function.Surjective (pluckerMap k N) :=
  (exteriorPower.map_surjective N.mkQ_surjective).comp
    (exteriorPower.liftBaseChange_toBaseChange_surjective R A k M)

end PluckerMap

section Point

/- The module `M` lies in the universe of `R`, so that `A ⊗[R] ⋀[R]^k M` and the exterior power of
the quotient lie in the same universe, as `ofSurjective` requires. -/
variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A]

/-- The top exterior power of the quotient of a point of `G(k, A ⊗[R] M; A)` has rank one at
every prime. -/
theorem rankAtStalk_exteriorPower_quotient (N : G(k, A ⊗[R] M; A)) (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (⋀[A]^k ((A ⊗[R] M) ⧸ N.toSubmodule)) p = 1 := by
  rw [exteriorPower.rankAtStalk_exteriorPower k N.rankAtStalk_eq p, Nat.choose_self]

/-- **The Plücker point** of `N ∈ G(k, A ⊗[R] M; A)`: the kernel of the Plücker map, a point of
`G(1, A ⊗[R] ⋀[R]^k M; A)` since the top exterior power `⋀[A]^k ((A ⊗[R] M) ⧸ N)` of the quotient
is finite projective of rank `k.choose k = 1`. -/
def plucker (N : G(k, A ⊗[R] M; A)) : G(1, A ⊗[R] ⋀[R]^k M; A) :=
  ofSurjective (pluckerMap k N.toSubmodule) (pluckerMap_surjective k N.toSubmodule)
    (rankAtStalk_exteriorPower_quotient N)

theorem plucker_toSubmodule (N : G(k, A ⊗[R] M; A)) :
    (plucker N).toSubmodule = LinearMap.ker (pluckerMap k N.toSubmodule) :=
  rfl

end Point

section Naturality

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **Naturality of the Plücker point**: Mathlib's base change of points along an `R`-algebra map
`f : A → B` commutes with `plucker`. The `A`-linear map `Q → Q_B`, `[a ⊗ m] ↦ [f a ⊗ m]`, of
quotients induces `⋀[A]^k Q → ⋀[B]^k Q_B`, which intertwines the two Plücker maps along `f ⊗ id`;
so `f ⊗ id` maps the Plücker point of `N` into that of `map f N` (`map_eq_of_forall`). -/
theorem map_plucker (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    map f (plucker N) = plucker (map f N) := by
  apply map_eq_of_forall
  intro x hx
  rw [plucker_toSubmodule, LinearMap.mem_ker] at hx ⊢
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  let φ : A ⊗[R] M →ₗ[A] B ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)
  have hφ : ∀ y, φ y = f.toLinearMap.rTensor M y := fun y => by
    induction y using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add y z hy hz => rw [map_add, map_add, hy, hz]
  let q : (A ⊗[R] M) ⧸ N.toSubmodule →ₗ[A] (B ⊗[R] M) ⧸ (map f N).toSubmodule :=
    N.toSubmodule.liftQ (((map f N).toSubmodule.mkQ.restrictScalars A) ∘ₗ φ) fun y hy => by
      simpa [hφ y, Submodule.Quotient.mk_eq_zero] using rTensor_mem_map f N hy
  have hq : ∀ m : M, q (N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) =
      (map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] m) := fun m => by
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, hφ, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      map_one]
  let Θ := exteriorPower.mapOfIsScalarTower B k q
  have key : ∀ y : A ⊗[R] ⋀[R]^k M,
      pluckerMap k (map f N).toSubmodule (f.toLinearMap.rTensor _ y) =
        Θ (pluckerMap k N.toSubmodule y) := by
    intro y
    induction y using exteriorPower.tmul_ιMulti_induction with
    | tmul a v =>
      rw [LinearMap.rTensor_tmul, pluckerMap_tmul, pluckerMap_tmul, LinearMap.map_smul,
        exteriorPower.mapOfIsScalarTower_ιMulti, ← algebraMap_smul B a]
      have hv : (q ∘ fun i => N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] v i)) =
          fun i => (map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] v i) := by
        funext i
        exact hq (v i)
      rw [hv]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
    | zero => simp only [map_zero]
  rw [key, hx, map_zero]

variable (R M k) in
/-- **The Plücker transformation** `N ↦ plucker N` from Mathlib's Grassmannian functor of `M` to
the Grassmannian functor of rank-one quotients of `⋀[R]^k M`, on `R`-algebras. -/
def pluckerNatTrans :
    functor.{u, u, u} (R := R) (M := M) k ⟶ functor.{u, u, u} (R := R) (M := ⋀[R]^k M) 1 where
  app _ := TypeCat.ofHom fun N => plucker N
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun N => (map_plucker f.hom N).symm

theorem pluckerNatTrans_app (A : CommAlgCat.{u} R)
    (N : (functor.{u, u, u} (R := R) (M := M) k).obj A) :
    (pluckerNatTrans R M k).app A N = plucker N :=
  rfl

end Naturality

end Module.Grassmannian
