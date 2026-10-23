/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.Semilinear
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Base change of exterior powers

Let `B` be an `A`-algebra and `P` an `A`-module.

* `exteriorPower.mapOfIsScalarTower B k g`: an `A`-linear map `g : P → N` into a `B`-module `N`
  induces the `A`-linear map `⋀[A]^k P → ⋀[B]^k N`, `p₁ ∧ ⋯ ∧ p_k ↦ g p₁ ∧ ⋯ ∧ g p_k`. It is the
  `A`-linear form of `exteriorPower.mapSemilinear k` applied to `g` as a semilinear map along
  `algebraMap A B` (`semilinearOfIsScalarTower`).
* `exteriorPower.toBaseChange A B k P := mapOfIsScalarTower B k (1 ⊗ ·)`, the map
  `⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)`. Its `B`-linear extension `B ⊗[A] ⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)` is
  surjective for every `P` (`liftBaseChange_toBaseChange_surjective`) and bijective for projective
  `P` (`bijective_liftBaseChange_toBaseChange`): a basis goes to a basis when `P` is free, and a
  projective module is a retract of a free one, compatibly with the maps
  (`liftBaseChange_toBaseChange_naturality`). Hence `toBaseChange` is a base change
  (`isBaseChange_toBaseChange`, Mathlib's `IsBaseChange`).
* For a finite projective `A`-module `Q` of constant rank `r` at every prime, `⋀[A]^k Q` is finite
  projective (`projective_exteriorPower`) of constant rank `r.choose k`
  (`rankAtStalk_exteriorPower`); for `k = r` it has rank one.

This is the base-change compatibility of exterior powers used for the Plücker embedding of the
Grassmannian. Only the projective case is proved; the bijectivity holds for every module but is
not needed here. Compare Stacks, Tag 0C6F (exterior powers commute with localization), Tag 00DN
(exterior powers of free modules are free) and Tag 01CI (exterior powers of sheaves of modules
commute with pullback).
-/

@[expose] public section

noncomputable section

open TensorProduct Function

universe u v w w'

namespace exteriorPower

section MapOfIsScalarTower

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] (k : ℕ)
  {P : Type w} [AddCommGroup P] [Module A P]
  {N : Type w'} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- An `A`-linear map into a `B`-module, as a semilinear map along `algebraMap A B`. -/
def semilinearOfIsScalarTower (g : P →ₗ[A] N) : P →ₛₗ[algebraMap A B] N where
  toFun := g
  map_add' := g.map_add
  map_smul' a x := by rw [map_smul, algebraMap_smul]

/-- An `A`-linear map `g : P → N` into a `B`-module induces the `A`-linear map
`⋀[A]^k P → ⋀[B]^k N`, `p₁ ∧ ⋯ ∧ p_k ↦ g p₁ ∧ ⋯ ∧ g p_k`. It is the `A`-linear form, needed for
`liftBaseChange` and `IsBaseChange`, of `mapSemilinear k` applied to `g` as a semilinear map along
`algebraMap A B` (`semilinearOfIsScalarTower`). -/
def mapOfIsScalarTower (g : P →ₗ[A] N) : ⋀[A]^k P →ₗ[A] ⋀[B]^k N where
  toFun := mapSemilinear k (semilinearOfIsScalarTower B g)
  map_add' := map_add _
  map_smul' a x := by
    rw [LinearMap.map_smulₛₗ, RingHom.id_apply, algebraMap_smul]

@[simp]
theorem mapOfIsScalarTower_ιMulti (g : P →ₗ[A] N) (v : Fin k → P) :
    mapOfIsScalarTower B k g (ιMulti A k v) = ιMulti B k (g ∘ v) :=
  mapSemilinear_apply_ιMulti k (semilinearOfIsScalarTower B g) v

end MapOfIsScalarTower

/-- An additive statement on `A ⊗[R] ⋀[R]^k M` holds once it holds on the elements
`a ⊗ (m₁ ∧ ⋯ ∧ m_k)`. -/
theorem tmul_ιMulti_induction {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {k : ℕ} {A : Type*} [CommRing A] [Algebra R A] {motive : A ⊗[R] ⋀[R]^k M → Prop}
    (x : A ⊗[R] ⋀[R]^k M)
    (tmul : ∀ (a : A) (v : Fin k → M), motive (a ⊗ₜ ιMulti R k v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) (zero : motive 0) : motive x := by
  induction x using TensorProduct.inductionOn with
  | tmul a ω =>
    have hω : ω ∈ Submodule.span R (Set.range (ιMulti R k (M := M))) := by
      rw [ιMulti_span]; trivial
    induction hω using Submodule.span_induction generalizing a with
    | mem ω hω => obtain ⟨v, rfl⟩ := hω; exact tmul a v
    | zero => rw [TensorProduct.tmul_zero]; exact zero
    | add ω₁ ω₂ _ _ h₁ h₂ => rw [TensorProduct.tmul_add]; exact add _ _ (h₁ a) (h₂ a)
    | smul r ω _ h => rw [← TensorProduct.smul_tmul]; exact h (r • a)
  | add x y hx hy => exact add x y hx hy

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B] (k : ℕ)
  (P : Type w) [AddCommGroup P] [Module A P]

/-- The base-change map `⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)`,
`p₁ ∧ ⋯ ∧ p_k ↦ (1 ⊗ p₁) ∧ ⋯ ∧ (1 ⊗ p_k)`. -/
abbrev toBaseChange : ⋀[A]^k P →ₗ[A] ⋀[B]^k (B ⊗[A] P) :=
  mapOfIsScalarTower B k (TensorProduct.mk A B P 1)

variable {A B k P}

theorem toBaseChange_ιMulti (v : Fin k → P) :
    toBaseChange A B k P (ιMulti A k v) = ιMulti B k (fun i => (1 : B) ⊗ₜ[A] v i) :=
  mapOfIsScalarTower_ιMulti B k _ v

theorem liftBaseChange_toBaseChange_tmul (b : B) (v : Fin k → P) :
    (toBaseChange A B k P).liftBaseChange B (b ⊗ₜ ιMulti A k v) =
      b • ιMulti B k (fun i => (1 : B) ⊗ₜ[A] v i) := by
  rw [LinearMap.liftBaseChange_tmul, toBaseChange_ιMulti]

variable (A B k P) in
/-- The `B`-linear extension `B ⊗[A] ⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)` of `toBaseChange` is surjective:
its range contains the wedges of the generators `1 ⊗ p`. -/
theorem liftBaseChange_toBaseChange_surjective :
    Surjective ((toBaseChange A B k P).liftBaseChange B) := by
  rw [← LinearMap.range_eq_top]
  have hspan : Submodule.span B (Set.range (TensorProduct.mk A B P 1)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | tmul b p =>
      have h : b ⊗ₜ[A] p = b • (TensorProduct.mk A B P 1 p) := by
        rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  rw [eq_top_iff, ← ιMulti_span_of_span B k (B ⊗[A] P) hspan, Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have h : ∀ i, ∃ p : P, TensorProduct.mk A B P 1 p = a i := fun i => ha ⟨i, rfl⟩
  choose v hv using h
  rw [SetLike.mem_coe, LinearMap.mem_range]
  refine ⟨(1 : B) ⊗ₜ ιMulti A k v, ?_⟩
  rw [liftBaseChange_toBaseChange_tmul, one_smul]
  congr 1
  funext i
  exact hv i

/-- Naturality of `toBaseChange` in the module, on the `B`-linear extensions. -/
theorem liftBaseChange_toBaseChange_naturality {P' : Type w'} [AddCommGroup P'] [Module A P']
    (g : P →ₗ[A] P') (x : B ⊗[A] ⋀[A]^k P) :
    (toBaseChange A B k P').liftBaseChange B ((map k g).baseChange B x) =
      map k (g.baseChange B) ((toBaseChange A B k P).liftBaseChange B x) := by
  have key : ∀ y : ⋀[A]^k P,
      toBaseChange A B k P' (map k g y) = map k (g.baseChange B) (toBaseChange A B k P y) := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (ιMulti A k (M := P))) := by
      rw [ιMulti_span]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [map_apply_ιMulti, toBaseChange_ιMulti, toBaseChange_ιMulti, map_apply_ιMulti]
      congr 1
    | zero => simp only [map_zero]
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul a y _ hy =>
      rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
        LinearMap.map_smul_of_tower, hy]
  induction x using TensorProduct.inductionOn with
  | tmul b y =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      LinearMap.map_smul, key]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- For a free module, `toBaseChange` sends the exterior-power basis built from a basis of `P` to
the exterior-power basis built from the base-changed basis, so its `B`-linear extension is
bijective. -/
theorem bijective_liftBaseChange_toBaseChange_of_free [Module.Free A P] :
    Bijective ((toBaseChange A B k P).liftBaseChange B) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex A P) := linearOrderOfSTO WellOrderingRel
  have h : (toBaseChange A B k P).liftBaseChange B =
      ((Algebra.TensorProduct.basis B ((Module.Free.chooseBasis A P).exteriorPower k)).equiv
        ((Algebra.TensorProduct.basis B (Module.Free.chooseBasis A P)).exteriorPower k)
        (Equiv.refl _)).toLinearMap := by
    refine (Algebra.TensorProduct.basis B
      ((Module.Free.chooseBasis A P).exteriorPower k)).ext fun s => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
      Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul, basis_apply,
      basis_apply, ιMulti_family, ιMulti_family, toBaseChange_ιMulti]
    congr 1
    funext i
    simp only [Function.comp_apply, Algebra.TensorProduct.basis_apply]
  rw [h]
  exact LinearEquiv.bijective _

/-- For a projective module `P`, the `B`-linear extension
`B ⊗[A] ⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)` of `toBaseChange` is bijective: `P` is a retract of the free
module `P →₀ A`, the map is natural in the module, and a retract of a bijection is a bijection. -/
theorem bijective_liftBaseChange_toBaseChange [Module.Projective A P] :
    Bijective ((toBaseChange A B k P).liftBaseChange B) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A P)
  set r : (P →₀ A) →ₗ[A] P := Finsupp.linearCombination A id
  have hF := bijective_liftBaseChange_toBaseChange_of_free (A := A) (B := B) (k := k)
    (P := P →₀ A)
  have hrs₁ : ∀ x : B ⊗[A] ⋀[A]^k P, (map k r).baseChange B ((map k s).baseChange B x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← map_comp, hs, map_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hrs₂ : ∀ y : ⋀[B]^k (B ⊗[A] P),
      map k (r.baseChange B) (map k (s.baseChange B) y) = y := by
    intro y
    rw [← LinearMap.comp_apply, ← map_comp, ← LinearMap.baseChange_comp, hs,
      LinearMap.baseChange_id, map_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    have h := congrArg (map k (s.baseChange B)) hxy
    rw [← liftBaseChange_toBaseChange_naturality, ← liftBaseChange_toBaseChange_naturality] at h
    have h' := congrArg ((map k r).baseChange B) (hF.1 h)
    rwa [hrs₁, hrs₁] at h'
  · intro z
    obtain ⟨y, hy⟩ := hF.2 (map k (s.baseChange B) z)
    refine ⟨(map k r).baseChange B y, ?_⟩
    rw [liftBaseChange_toBaseChange_naturality, hy, hrs₂]

variable (A B k P) in
/-- **Exterior powers of a projective module commute with base change**: `toBaseChange` exhibits
`⋀[B]^k (B ⊗[A] P)` as the base change of `⋀[A]^k P` along `A → B`. -/
theorem isBaseChange_toBaseChange [Module.Projective A P] :
    IsBaseChange B (toBaseChange A B k P) :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ bijective_liftBaseChange_toBaseChange)
    fun x => by
      rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]

variable (k P) in
/-- The exterior powers of a projective module are projective: `⋀[A]^k P` is a retract of the free
module `⋀[A]^k (P →₀ A)`. -/
instance projective_exteriorPower [Module.Projective A P] :
    Module.Projective A (⋀[A]^k P) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A P)
  exact Module.Projective.of_split (map k s) (map k (Finsupp.linearCombination A id))
    (by rw [← map_comp, hs, map_id])

variable (k) in
/-- **The rank of an exterior power**: if `Q` is finite projective of rank `r` at every prime, then
`⋀[A]^k Q` has rank `r.choose k` at every prime. At a prime `p`, base change to the local ring
`A_p` (`isBaseChange_toBaseChange`) reduces this to `exteriorPower.finrank_eq` for the free
module `A_p ⊗[A] Q` of rank `r`. -/
theorem rankAtStalk_exteriorPower {Q : Type w} [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    [Module.Projective A Q] {r : ℕ} (hr : ∀ p, Module.rankAtStalk (R := A) Q p = r)
    (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (⋀[A]^k Q) p = r.choose k := by
  have hb := isBaseChange_toBaseChange A (Localization.AtPrime p.asIdeal) k Q
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[A] Q) := Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_tensorProduct, hb.equiv.finrank_eq, exteriorPower.finrank_eq,
    ← Module.rankAtStalk_eq_finrank_tensorProduct, hr]

end exteriorPower
