/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.MapCriterion

/-!
# Transport of Grassmannian points along linear equivalences

* `Module.Grassmannian.ofLinearEquiv e`: a point of `G(k, M; R)` goes to its image under
  `e : M ≃ₗ[R] M'`, a point of `G(k, M'; R)`; it is injective (`ofLinearEquiv_injective`) and
  inverse to transport along `e.symm` (`ofLinearEquiv_symm_ofLinearEquiv`, `ofLinearEquivEquiv`).
* `Module.Grassmannian.map_ofLinearEquiv_baseChange`: transport along `A ⊗ e` and `B ⊗ e`
  commutes with Mathlib's base change along `f : A → B` (`rTensor_mem_map`).
* `Module.Grassmannian.functorIsoOfLinearEquiv`: Mathlib's Grassmannian functor
  `B ↦ G(k, B ⊗[R] M; B)` is functorial in `M` along linear equivalences.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Module.Grassmannian

/-- **Transport of a Grassmannian point along a linear equivalence** of the ambient modules: the
image of the submodule, with the induced isomorphism of quotients. -/
def ofLinearEquiv {R : Type u} [CommRing R] {M : Type v} {M' : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] {k : ℕ} (e : M ≃ₗ[R] M')
    (N : Module.Grassmannian R M k) :
    Module.Grassmannian R M' k :=
  let E := Submodule.Quotient.equiv N.toSubmodule (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl
  { toSubmodule := N.toSubmodule.map (e : M →ₗ[R] M')
    finite_quotient := Module.Finite.equiv E
    projective_quotient := Module.Projective.of_equiv E
    rankAtStalk_eq := fun p => (congrFun (Module.rankAtStalk_eq_of_equiv E) p).symm.trans
      (N.rankAtStalk_eq p) }

theorem ofLinearEquiv_injective {R : Type u} [CommRing R] {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] {k : ℕ} (e : M ≃ₗ[R] M') :
    Function.Injective (ofLinearEquiv (k := k) e) := by
  intro N N' h
  apply Module.Grassmannian.ext
  have h' := congrArg Module.Grassmannian.toSubmodule h
  exact Submodule.map_injective_of_injective e.injective h'

variable {R : Type u} [CommRing R] {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {k : ℕ}

/-- Transport along `e` and then along `e.symm` is the identity. -/
theorem ofLinearEquiv_symm_ofLinearEquiv (e : M ≃ₗ[R] M') (N : Module.Grassmannian R M k) :
    ofLinearEquiv e.symm (ofLinearEquiv e N) = N := by
  apply Module.Grassmannian.ext
  change Submodule.map (e.symm : M' →ₗ[R] M) (Submodule.map (e : M →ₗ[R] M') N.toSubmodule) = _
  rw [← Submodule.map_comp]
  simp

/-- Points of Grassmannians correspond along a linear equivalence of the ambient modules. -/
def ofLinearEquivEquiv (e : M ≃ₗ[R] M') :
    Module.Grassmannian R M k ≃ Module.Grassmannian R M' k where
  toFun := ofLinearEquiv e
  invFun := ofLinearEquiv e.symm
  left_inv := ofLinearEquiv_symm_ofLinearEquiv e
  right_inv N := by simpa using ofLinearEquiv_symm_ofLinearEquiv e.symm N

/-- **Transport along a linear equivalence commutes with base change**: for `e : M ≃ₗ[R] M'` and an
`R`-algebra map `f : A → B`, base change along `f` commutes with transport along `A ⊗ e` and
`B ⊗ e`. -/
theorem map_ofLinearEquiv_baseChange (e : M ≃ₗ[R] M') {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (N : Module.Grassmannian A (A ⊗[R] M) k) :
    map f (ofLinearEquiv (e.baseChange R A M M') N) =
      ofLinearEquiv (e.baseChange R B M M') (map f N) := by
  have key : ∀ z : A ⊗[R] M, e.baseChange R B M M' (f.toLinearMap.rTensor M z) =
      f.toLinearMap.rTensor M' (e.baseChange R A M M' z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  apply map_eq_of_forall
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨f.toLinearMap.rTensor M y, rTensor_mem_map f N hy, key y⟩

variable (k) in
/-- **Mathlib's Grassmannian functor is functorial in the module along linear equivalences**:
`e : M ≃ₗ[R] M'` induces `G(k, B ⊗ M; B) ≅ G(k, B ⊗ M'; B)`, naturally in `B`. -/
def functorIsoOfLinearEquiv (e : M ≃ₗ[R] M') :
    functor.{u, u, u} (R := R) (M := M) k ≅ functor.{u, u, u} (R := R) (M := M') k :=
  NatIso.ofComponents
    (fun B => (ofLinearEquivEquiv (k := k) (e.baseChange R B M M')).toIso)
    fun {_ _} f => ConcreteCategory.hom_ext _ _ fun N =>
      (map_ofLinearEquiv_baseChange e f.hom N).symm

end Module.Grassmannian
