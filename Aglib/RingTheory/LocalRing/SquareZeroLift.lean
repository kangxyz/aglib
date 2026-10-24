/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Square-zero lifts of a rational point of a local algebra

Let `k` be a field and `A` a local `k`-algebra with a `k`-algebra map `ψ : A →ₐ[k] k`, so that
the residue field of `A` is `k`. Then `ker ψ` is the maximal ideal `𝔪`
(`IsLocalRing.ker_algHom_eq_maximalIdeal`), every `a ∈ A` is `ψ a + (a - ψ a)` with
`a - ψ a ∈ 𝔪`, and `ψ` is a local homomorphism (`IsLocalRing.isLocalHom_algHom`).

**Derivations.** `a ↦ [a - ψ a]` is a `k`-derivation `A → 𝔪/𝔪²`
(`IsLocalRing.cotangentDerivation`). For an `A`-module `N` killed by `𝔪`, composition with it
identifies the `k`-linear maps `𝔪/𝔪² → N` with the `k`-derivations `A → N`; the inverse
restricts a derivation to `𝔪` (`IsLocalRing.derivationEquivCotangentSpace`). This is the first
paragraph of Kleiman's proof of Thm 5.11 (p. 42): a derivation `δ` kills `𝔪²`, so induces a
linear map on `𝔪/𝔪²`; every such map arises, uniquely since `δ(1) = 0`.

Let `L` be a commutative `k`-algebra and `M` an `L`-module (with its central right action and a
compatible `k`-structure), and let `L ⊕ M = TrivSqZeroExt L M`, so `L[ε] = L ⊕ L`. A lift of
`ψ` is a `k`-algebra map `φ : A →ₐ[k] L ⊕ M` with `fst ∘ φ = (k → L) ∘ ψ`. Lifts correspond to
`k`-linear maps `𝔪/𝔪² → M` (`IsLocalRing.trivSqZeroExtLiftEquiv`):

* a lift `φ` vanishes on `𝔪²` in the second coordinate and gives `[x] ↦ (φ x).snd`;
* conversely `θ : 𝔪/𝔪² →ₗ[k] M` gives the lift `a ↦ (ψ a, θ [a - ψ a])`
  (`IsLocalRing.trivSqZeroExtLift`), whose second coordinate is `θ` composed with the
  derivation `a ↦ [a - ψ a]` (`IsLocalRing.cotangentDeviation`).

With `A` acting on `M` through `ψ` (`IsLocalRing.moduleViaAlgHom`), lifts are therefore the
`k`-derivations `a ↦ (φ a).snd` (`IsLocalRing.trivSqZeroExtLiftEquivDerivation`). The
correspondence is natural in `M`: for an `L`-linear `g : M → M'`, composing a lift with
`TrivSqZeroExt.map g` corresponds to composing with `g` (`IsLocalRing.map_comp_trivSqZeroExtLift`).
For Noetherian `A`, the cotangent space `𝔪/𝔪²` is finite-dimensional over `k`
(`IsLocalRing.finite_cotangentSpace_of_algHom`).

This is the algebra of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 5.11,
before (5.11.1), p. 42, for `L = M = k`: the local `k`-algebra maps `u : A → k[ε]` are
`u(a) = ā + δ(a) ε` for the derivations `δ`. Here the second coordinate of a lift is the
derivation `θ ∘ [· - ψ ·]`. Mathlib's `derivationToSquareZeroEquivLift` is the same
correspondence for a square-zero ideal with a given reference lift; it is not used, since the
lift `a ↦ (ψ a, θ [a - ψ a])` is explicit once the residue field is `k`.
-/

@[expose] public section

namespace IsLocalRing

variable {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] (ψ : A →ₐ[k] k)

/-- The kernel of a `k`-rational point of a local `k`-algebra is the maximal ideal. -/
theorem ker_algHom_eq_maximalIdeal : RingHom.ker ψ = maximalIdeal A := by
  have hsurj : Function.Surjective ψ := fun c => ⟨algebraMap k A c, ψ.commutes c⟩
  have := RingHom.ker_isMaximal_of_surjective ψ hsurj
  exact IsLocalRing.eq_maximalIdeal this

theorem mem_maximalIdeal_iff_algHom_eq_zero {a : A} : a ∈ maximalIdeal A ↔ ψ a = 0 := by
  rw [← ker_algHom_eq_maximalIdeal ψ, RingHom.mem_ker]

/-- `a - ψ a` lies in the maximal ideal. -/
theorem sub_algebraMap_algHom_mem_maximalIdeal (a : A) :
    a - algebraMap k A (ψ a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal_iff_algHom_eq_zero ψ, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

/-- A `k`-rational point of a local `k`-algebra is a local homomorphism. -/
theorem isLocalHom_algHom : IsLocalHom ψ := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := h
  rw [mem_maximalIdeal_iff_algHom_eq_zero ψ] at hm
  rw [hm] at ha
  exact not_isUnit_zero ha

/-- The class `[a - ψ a] ∈ 𝔪/𝔪²`. As a function of `a` it is a `k`-derivation
(`cotangentDeviation_mul`), the identity on `𝔪` (`cotangentDeviation_of_mem`). -/
def cotangentDeviation (a : A) : CotangentSpace A :=
  (maximalIdeal A).toCotangent
    ⟨a - algebraMap k A (ψ a), sub_algebraMap_algHom_mem_maximalIdeal ψ a⟩

theorem cotangentDeviation_of_mem {x : A} (hx : x ∈ maximalIdeal A) :
    cotangentDeviation ψ x = (maximalIdeal A).toCotangent ⟨x, hx⟩ := by
  have h0 : ψ x = 0 := (mem_maximalIdeal_iff_algHom_eq_zero ψ).mp hx
  have hx' : (⟨x - algebraMap k A (ψ x), sub_algebraMap_algHom_mem_maximalIdeal ψ x⟩ :
      maximalIdeal A) = ⟨x, hx⟩ := by
    ext
    simp only [h0, map_zero, sub_zero]
  exact congrArg (maximalIdeal A).toCotangent hx'

theorem cotangentDeviation_algebraMap (c : k) : cotangentDeviation ψ (algebraMap k A c) = 0 := by
  have hc : (⟨algebraMap k A c - algebraMap k A (ψ (algebraMap k A c)),
      sub_algebraMap_algHom_mem_maximalIdeal ψ _⟩ : maximalIdeal A) = 0 := by
    ext
    simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
      ZeroMemClass.coe_zero]
  exact (congrArg (maximalIdeal A).toCotangent hc).trans (map_zero _)

theorem cotangentDeviation_add (a b : A) :
    cotangentDeviation ψ (a + b) = cotangentDeviation ψ a + cotangentDeviation ψ b := by
  have hab : (⟨a + b - algebraMap k A (ψ (a + b)),
      sub_algebraMap_algHom_mem_maximalIdeal ψ _⟩ : maximalIdeal A) =
      ⟨a - algebraMap k A (ψ a), sub_algebraMap_algHom_mem_maximalIdeal ψ a⟩ +
        ⟨b - algebraMap k A (ψ b), sub_algebraMap_algHom_mem_maximalIdeal ψ b⟩ := by
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  exact (congrArg (maximalIdeal A).toCotangent hab).trans (map_add _ _ _)

theorem cotangentDeviation_smul (c : k) (a : A) :
    cotangentDeviation ψ (c • a) = c • cotangentDeviation ψ a := by
  have hca : (⟨c • a - algebraMap k A (ψ (c • a)),
      sub_algebraMap_algHom_mem_maximalIdeal ψ _⟩ : maximalIdeal A) =
      c • ⟨a - algebraMap k A (ψ a), sub_algebraMap_algHom_mem_maximalIdeal ψ a⟩ := by
    ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  exact (congrArg (maximalIdeal A).toCotangent hca).trans (LinearMap.map_smul_of_tower _ _ _)

/-- The Leibniz rule for `a ↦ [a - ψ a]`, with `A` acting on `𝔪/𝔪²` through `ψ`. -/
theorem cotangentDeviation_mul (a b : A) :
    cotangentDeviation ψ (a * b) =
      ψ a • cotangentDeviation ψ b + ψ b • cotangentDeviation ψ a := by
  let x : maximalIdeal A :=
    ⟨a - algebraMap k A (ψ a), sub_algebraMap_algHom_mem_maximalIdeal ψ a⟩
  let y : maximalIdeal A :=
    ⟨b - algebraMap k A (ψ b), sub_algebraMap_algHom_mem_maximalIdeal ψ b⟩
  have hab : (⟨a * b - algebraMap k A (ψ (a * b)),
      sub_algebraMap_algHom_mem_maximalIdeal ψ _⟩ : maximalIdeal A) =
      ψ a • y + ψ b • x + x * y := by
    ext
    simp only [x, y, map_mul, Submodule.coe_add, Submodule.coe_smul_of_tower,
      MulMemClass.coe_mul, Algebra.smul_def]
    ring
  have hxy : (maximalIdeal A).toCotangent (x * y) = 0 := by
    rw [Ideal.toCotangent_eq_zero, MulMemClass.coe_mul, pow_two]
    exact Ideal.mul_mem_mul x.2 y.2
  calc cotangentDeviation ψ (a * b)
      = (maximalIdeal A).toCotangent (ψ a • y + ψ b • x + x * y) :=
        congrArg (maximalIdeal A).toCotangent hab
    _ = ψ a • (maximalIdeal A).toCotangent y + ψ b • (maximalIdeal A).toCotangent x := by
        rw [map_add, hxy, add_zero, map_add, LinearMap.map_smul_of_tower,
          LinearMap.map_smul_of_tower]
    _ = ψ a • cotangentDeviation ψ b + ψ b • cotangentDeviation ψ a := rfl

/-- `A` acts on `𝔪/𝔪²` through `ψ`. -/
theorem smul_cotangentSpace_eq (a : A) (z : CotangentSpace A) : a • z = ψ a • z := by
  conv_lhs => rw [← sub_add_cancel a (algebraMap k A (ψ a))]
  rw [add_smul,
    Ideal.Cotangent.smul_eq_zero_of_mem (sub_algebraMap_algHom_mem_maximalIdeal ψ a) z,
    zero_add, algebraMap_smul A]

/-- The derivation `a ↦ [a - ψ a]` of `A` into its cotangent space `𝔪/𝔪²`. -/
def cotangentDerivation : Derivation k A (CotangentSpace A) where
  toFun := cotangentDeviation ψ
  map_add' := cotangentDeviation_add ψ
  map_smul' := cotangentDeviation_smul ψ
  map_one_eq_zero' := by
    have h := cotangentDeviation_algebraMap ψ 1
    rw [map_one] at h
    exact h
  leibniz' a b := by
    change cotangentDeviation ψ (a * b) = a • cotangentDeviation ψ b + b • cotangentDeviation ψ a
    rw [cotangentDeviation_mul, smul_cotangentSpace_eq ψ a, smul_cotangentSpace_eq ψ b]

@[simp]
theorem cotangentDerivation_apply (a : A) : cotangentDerivation ψ a = cotangentDeviation ψ a :=
  rfl

section Derivation

variable {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- A derivation, restricted to the maximal ideal. -/
def derivationRestrict (D : Derivation k A N) : maximalIdeal A →ₗ[k] N where
  toFun x := D x
  map_add' x y := by rw [Submodule.coe_add, map_add]
  map_smul' c x := by rw [Submodule.coe_smul_of_tower, D.map_smul, RingHom.id_apply]

theorem smul_eq_algHom_smul (hN : ∀ x ∈ maximalIdeal A, ∀ n : N, x • n = 0) (a : A) (n : N) :
    a • n = ψ a • n := by
  conv_lhs => rw [← sub_add_cancel a (algebraMap k A (ψ a))]
  rw [add_smul, hN _ (sub_algebraMap_algHom_mem_maximalIdeal ψ a) n, zero_add,
    algebraMap_smul A]

variable (N) in
/-- **Derivations and the cotangent space** (Kleiman, proof of Thm 5.11, p. 42). If the maximal
ideal kills the `A`-module `N`, a `k`-derivation `A → N` vanishes on `𝔪²`, and restriction to `𝔪`
identifies the `k`-derivations `A → N` with the `k`-linear maps `𝔪/𝔪² → N`; the inverse composes
with `cotangentDerivation`. -/
def derivationEquivCotangentSpace (hN : ∀ x ∈ maximalIdeal A, ∀ n : N, x • n = 0) :
    Derivation k A N ≃ₗ[k] (CotangentSpace A →ₗ[k] N) where
  toFun D := Ideal.Cotangent.lift (derivationRestrict D) fun x y => by
    change D ((x : A) * (y : A)) = 0
    rw [D.leibniz, hN _ x.2, hN _ y.2, add_zero]
  map_add' D D' := LinearMap.ext fun z => by
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    rfl
  map_smul' c D := LinearMap.ext fun z => by
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    rfl
  invFun θ :=
    { toFun a := θ (cotangentDeviation ψ a)
      map_add' a b := by rw [cotangentDeviation_add, map_add]
      map_smul' c a := by rw [cotangentDeviation_smul, map_smul, RingHom.id_apply]
      map_one_eq_zero' := by
        have h := cotangentDeviation_algebraMap ψ 1
        rw [map_one] at h
        change θ (cotangentDeviation ψ 1) = 0
        rw [h, map_zero]
      leibniz' a b := by
        change θ (cotangentDeviation ψ (a * b)) =
          a • θ (cotangentDeviation ψ b) + b • θ (cotangentDeviation ψ a)
        rw [cotangentDeviation_mul, map_add, map_smul, map_smul, smul_eq_algHom_smul ψ hN a,
          smul_eq_algHom_smul ψ hN b] }
  left_inv D := by
    ext a
    change D (a - algebraMap k A (ψ a)) = D a
    rw [map_sub, D.map_algebraMap, sub_zero]
  right_inv θ := LinearMap.ext fun z => by
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    change θ (cotangentDeviation ψ x) = θ ((maximalIdeal A).toCotangent x)
    rw [cotangentDeviation_of_mem ψ x.2]

theorem derivationEquivCotangentSpace_apply_toCotangent
    (hN : ∀ x ∈ maximalIdeal A, ∀ n : N, x • n = 0) (D : Derivation k A N)
    (x : maximalIdeal A) :
    derivationEquivCotangentSpace ψ N hN D ((maximalIdeal A).toCotangent x) = D x :=
  rfl

theorem derivationEquivCotangentSpace_symm_apply (hN : ∀ x ∈ maximalIdeal A, ∀ n : N, x • n = 0)
    (θ : CotangentSpace A →ₗ[k] N) (a : A) :
    (derivationEquivCotangentSpace ψ N hN).symm θ a = θ (cotangentDeviation ψ a) :=
  rfl

end Derivation

section Lift

variable {L M M' : Type*} [CommRing L] [Algebra k L]
  [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M] [IsCentralScalar L M] [Module k M]
  [IsScalarTower k L M]
  [AddCommGroup M'] [Module L M'] [Module Lᵐᵒᵖ M'] [IsCentralScalar L M'] [Module k M']
  [IsScalarTower k L M']

/-- The lift `a ↦ (ψ a, θ [a - ψ a])` of `ψ` to `L ⊕ M` defined by `θ : 𝔪/𝔪² →ₗ[k] M`. -/
def trivSqZeroExtLift (θ : CotangentSpace A →ₗ[k] M) : A →ₐ[k] TrivSqZeroExt L M where
  toFun a := ⟨algebraMap k L (ψ a), θ (cotangentDeviation ψ a)⟩
  map_one' := by
    have h := cotangentDeviation_algebraMap ψ 1
    rw [map_one] at h
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (algebraMap k L) (map_one ψ)).trans (map_one _)
    · exact (congrArg θ h).trans (map_zero θ)
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (algebraMap k L) (map_mul ψ a b)).trans (map_mul _ _ _)
    · change θ (cotangentDeviation ψ (a * b)) =
        algebraMap k L (ψ a) • θ (cotangentDeviation ψ b) +
          MulOpposite.op (algebraMap k L (ψ b)) • θ (cotangentDeviation ψ a)
      rw [cotangentDeviation_mul, map_add, map_smul, map_smul, op_smul_eq_smul,
        algebraMap_smul L, algebraMap_smul L]
  map_zero' := by
    have h := cotangentDeviation_algebraMap ψ 0
    rw [map_zero] at h
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (algebraMap k L) (map_zero ψ)).trans (map_zero _)
    · exact (congrArg θ h).trans (map_zero θ)
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (algebraMap k L) (map_add ψ a b)).trans (map_add _ _ _)
    · exact (congrArg θ (cotangentDeviation_add ψ a b)).trans (map_add θ _ _)
  commutes' c := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact congrArg (algebraMap k L) (AlgHom.commutes ψ c)
    · exact (congrArg θ (cotangentDeviation_algebraMap ψ c)).trans (map_zero θ)

@[simp]
theorem fst_trivSqZeroExtLift (θ : CotangentSpace A →ₗ[k] M) (a : A) :
    (trivSqZeroExtLift ψ θ a).fst = algebraMap k L (ψ a) :=
  rfl

@[simp]
theorem snd_trivSqZeroExtLift (θ : CotangentSpace A →ₗ[k] M) (a : A) :
    (trivSqZeroExtLift (L := L) ψ θ a).snd = θ (cotangentDeviation ψ a) :=
  rfl

theorem fstHom_comp_trivSqZeroExtLift (θ : CotangentSpace A →ₗ[k] M) :
    (TrivSqZeroExt.fstHom k L M).comp (trivSqZeroExtLift ψ θ) = (Algebra.ofId k L).comp ψ :=
  AlgHom.ext fun _ => rfl

variable {ψ}

theorem fst_eq_zero_of_mem_maximalIdeal {φ : A →ₐ[k] TrivSqZeroExt L M}
    (hφ : (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ) {x : A}
    (hx : x ∈ maximalIdeal A) : (φ x).fst = 0 := by
  have h := AlgHom.congr_fun hφ x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, Algebra.ofId_apply,
    (mem_maximalIdeal_iff_algHom_eq_zero ψ).mp hx, map_zero] at h
  exact h

/-- A lift of `ψ` to `L ⊕ M`, for a nontrivial `L`, is a local homomorphism. -/
theorem isLocalHom_of_fstHom_comp_eq [Nontrivial L] {φ : A →ₐ[k] TrivSqZeroExt L M}
    (hφ : (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ) : IsLocalHom φ := by
  have := isLocalHom_algHom ψ
  refine ⟨fun a ha => ?_⟩
  have h1 : IsUnit (φ a).fst := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
  have h2 : (φ a).fst = algebraMap k L (ψ a) := AlgHom.congr_fun hφ a
  rw [h2] at h1
  exact IsUnit.of_map ψ a (IsUnit.of_map (algebraMap k L) _ h1)

/-- The second coordinate of a lift, on the maximal ideal. -/
def liftSnd (φ : A →ₐ[k] TrivSqZeroExt L M) : maximalIdeal A →ₗ[k] M where
  toFun x := (φ x).snd
  map_add' x y := by
    rw [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add]
  map_smul' c x := by
    rw [Submodule.coe_smul_of_tower, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]

theorem liftSnd_mul {φ : A →ₐ[k] TrivSqZeroExt L M}
    (hφ : (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ)
    (x y : maximalIdeal A) : liftSnd φ (x * y) = 0 := by
  change (φ ((x : A) * (y : A))).snd = 0
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_eq_zero_of_mem_maximalIdeal hφ x.2,
    fst_eq_zero_of_mem_maximalIdeal hφ y.2, zero_smul, MulOpposite.op_zero, zero_smul, add_zero]

variable (ψ L M)

/-- **Square-zero lifts and the cotangent space.** Lifts `φ : A →ₐ[k] L ⊕ M` of `ψ` correspond
to `k`-linear maps `𝔪/𝔪² → M`, by `φ ↦ ([x] ↦ (φ x).snd)`, with inverse
`θ ↦ (a ↦ (ψ a, θ [a - ψ a]))`. -/
def trivSqZeroExtLiftEquiv :
    {φ : A →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ} ≃
      (CotangentSpace A →ₗ[k] M) where
  toFun φ := Ideal.Cotangent.lift (liftSnd φ.1) (liftSnd_mul φ.2)
  invFun θ := ⟨trivSqZeroExtLift ψ θ, fstHom_comp_trivSqZeroExtLift ψ θ⟩
  left_inv φ := by
    obtain ⟨φ, hφ⟩ := φ
    refine Subtype.ext (AlgHom.ext fun a => TrivSqZeroExt.ext ?_ ?_)
    · exact (AlgHom.congr_fun hφ a).symm
    · change liftSnd φ ⟨a - algebraMap k A (ψ a), sub_algebraMap_algHom_mem_maximalIdeal ψ a⟩ =
        (φ a).snd
      change (φ (a - algebraMap k A (ψ a))).snd = (φ a).snd
      rw [map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.snd_inl, sub_zero]
  right_inv θ := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    change θ (cotangentDeviation ψ x) = θ ((maximalIdeal A).toCotangent x)
    rw [cotangentDeviation_of_mem ψ x.2]

@[simp]
theorem trivSqZeroExtLiftEquiv_apply_toCotangent
    (φ : {φ : A →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ})
    (x : maximalIdeal A) :
    trivSqZeroExtLiftEquiv ψ L M φ ((maximalIdeal A).toCotangent x) = (φ.1 x).snd :=
  rfl

@[simp]
theorem trivSqZeroExtLiftEquiv_symm_apply_coe (θ : CotangentSpace A →ₗ[k] M) :
    ((trivSqZeroExtLiftEquiv ψ L M).symm θ).1 = trivSqZeroExtLift ψ θ :=
  rfl

variable {ψ L M}

/-- Naturality in `M`: composing the lift of `θ` with `TrivSqZeroExt.map g` gives the lift of
`g ∘ θ`. -/
theorem map_comp_trivSqZeroExtLift (g : M →ₗ[L] M') (θ : CotangentSpace A →ₗ[k] M) :
    ((TrivSqZeroExt.map g).restrictScalars k).comp (trivSqZeroExtLift ψ θ) =
      trivSqZeroExtLift ψ ((g.restrictScalars k).comp θ) := by
  refine AlgHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · exact TrivSqZeroExt.fst_map g _
  · exact TrivSqZeroExt.snd_map g _

variable (ψ L M)

omit [IsLocalRing A] [Module Lᵐᵒᵖ M] [IsCentralScalar L M] in
/-- `M` as an `A`-module through `ψ : A → k` and `k → L`; the maximal ideal kills it. -/
abbrev moduleViaAlgHom : Module A M :=
  Module.compHom M ((algebraMap k L).comp ψ.toRingHom)

omit [IsLocalRing A] [Module Lᵐᵒᵖ M] [IsCentralScalar L M] in
theorem isScalarTower_moduleViaAlgHom :
    letI := moduleViaAlgHom ψ L M
    IsScalarTower k A M := by
  let := moduleViaAlgHom ψ L M
  refine ⟨fun c a m => ?_⟩
  change algebraMap k L (ψ (c • a)) • m = c • (algebraMap k L (ψ a) • m)
  rw [map_smul, smul_eq_mul, map_mul, mul_smul, algebraMap_smul L]

/-- **Lifts and derivations** (Kleiman, proof of Thm 5.11, p. 42: `u(a) = ā + δ(a) ε`). With `A`
acting on `M` through `ψ`, a lift `φ` of `ψ` to `L ⊕ M` corresponds to the `k`-derivation
`a ↦ (φ a).snd` (`trivSqZeroExtLiftEquivDerivation_apply`). -/
def trivSqZeroExtLiftEquivDerivation :
    letI := moduleViaAlgHom ψ L M
    letI := isScalarTower_moduleViaAlgHom ψ L M
    {φ : A →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ} ≃ Derivation k A M :=
  letI := moduleViaAlgHom ψ L M
  letI := isScalarTower_moduleViaAlgHom ψ L M
  (trivSqZeroExtLiftEquiv ψ L M).trans
    (derivationEquivCotangentSpace ψ M fun x hx m => by
      change algebraMap k L (ψ x) • m = 0
      rw [(mem_maximalIdeal_iff_algHom_eq_zero ψ).mp hx, map_zero, zero_smul]).symm.toEquiv

theorem trivSqZeroExtLiftEquivDerivation_apply
    (φ : {φ : A →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp ψ}) (a : A) :
    trivSqZeroExtLiftEquivDerivation ψ L M φ a = (φ.1 a).snd := by
  change (φ.1 (a - algebraMap k A (ψ a))).snd = (φ.1 a).snd
  rw [map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub, TrivSqZeroExt.algebraMap_eq_inl',
    TrivSqZeroExt.snd_inl, sub_zero]

end Lift

include ψ in
/-- For Noetherian `A`, the cotangent space of a local `k`-algebra with residue field `k` is
finite-dimensional over `k`. -/
theorem finite_cotangentSpace_of_algHom [IsNoetherianRing A] :
    Module.Finite k (CotangentSpace A) := by
  have hsurj : Function.Surjective (algebraMap k (ResidueField A)) := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    refine ⟨ψ a, ?_⟩
    rw [IsScalarTower.algebraMap_apply k A (ResidueField A), ResidueField.algebraMap_eq, eq_comm,
      ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact sub_algebraMap_algHom_mem_maximalIdeal ψ a
  have : Module.Finite k (ResidueField A) :=
    Module.Finite.of_surjective (Algebra.linearMap k (ResidueField A)) hsurj
  have : IsScalarTower k (ResidueField A) (CotangentSpace A) :=
    IsScalarTower.of_algebraMap_smul fun c z => by
      rw [IsScalarTower.algebraMap_apply k A (ResidueField A), algebraMap_smul (ResidueField A),
        algebraMap_smul A]
  exact Module.Finite.trans (ResidueField A) (CotangentSpace A)

end IsLocalRing
