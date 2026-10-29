/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.ArtinReesInfMulSup
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Smooth.Local

/-!
# Formal smoothness from lifting along Artinian square-zero extensions

Let `R` be a commutative ring and `S` a local `R`-algebra presented as a quotient `P → S` of a
Noetherian local `R`-algebra `P` that is formally smooth with finite free differentials (for
instance, over a Noetherian `R`, the localization at a prime of a polynomial ring in finitely
many variables). If every surjective
`R`-algebra map from `S` to an Artinian local `R`-algebra `A` lifts along every surjection
`A' → A` of Artinian local `R`-algebras with square-zero kernel, then `S` is formally smooth
over `R` (`Algebra.FormallySmooth.of_lift_artinianLocal_squareZero`). Over a Noetherian ring `R`,
the localization `S` of a finite type `R`-algebra at a prime has such a presentation (the
localization of a polynomial ring at the inverse image of the prime, as in Mathlib's
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`), so the lifting condition alone
gives formal smoothness
(`Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization`).

This is the infinitesimal criterion with Artin local test rings used in Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, proof of Prop. 5.19, p. 47 (there quoted from SGA 1). The proof
here uses a single test extension. With `I = ker (P → S)`, `𝔪` the maximal ideal of `P` and
`m ≥ 1` given by the Artin–Rees lemma (`Ideal.exists_inf_mul_sup_pow_eq_mul`), put
`J = I + 𝔪 ^ m`. A lift of `S → P / J` to `P / 𝔪 J` differs from the quotient map
`P → P / 𝔪 J` by a derivation (`lift_eq_mk_of_D_mem_smul`), and this derivation shows that
`κ ⊗ I → κ ⊗ Ω[P⁄R]` is injective, `κ` the residue field of `S`. Mathlib's Jacobian criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField` concludes. No
condition on `R` or on the residue field of `S` is imposed.
-/

@[expose] public section

noncomputable section

open TensorProduct IsLocalRing KaehlerDifferential

universe u v

namespace Ideal.Quotient

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

/-- In `P ⧸ 𝔪 * J`, the ideal `𝔪` kills the kernel of the map to `P ⧸ J`. -/
theorem mk_mul_eq_zero_of_mem_ker_factorₐ {𝔪 J : Ideal P} {a : P} (ha : a ∈ 𝔪)
    {y : P ⧸ 𝔪 * J}
    (hy : y ∈ RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.mul_le_right : 𝔪 * J ≤ J))) :
    Ideal.Quotient.mk (𝔪 * J) a * y = 0 := by
  obtain ⟨j, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hj : j ∈ J := by
    rw [RingHom.mem_ker, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mp hy
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_mul ha hj)

/-- The kernel of `P ⧸ 𝔪 * J → P ⧸ J` has square zero when `J ≤ 𝔪`. -/
theorem ker_factorₐ_mul_sq_eq_bot {𝔪 J : Ideal P} (hJ : J ≤ 𝔪) :
    RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.mul_le_right : 𝔪 * J ≤ J)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro y hy z hz
  obtain ⟨j, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hj : j ∈ J := by
    rw [RingHom.mem_ker, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mp hy
  exact Ideal.mem_bot.mpr (mk_mul_eq_zero_of_mem_ker_factorₐ (hJ hj) hz)

end Ideal.Quotient

namespace IsLocalRing

variable {P : Type v} [CommRing P] [IsLocalRing P]

/-- The test ring `P ⧸ 𝔪 * J` of a local ring `P` is local. -/
theorem isLocalRing_quotient_maximalIdeal_mul (J : Ideal P) :
    IsLocalRing (P ⧸ maximalIdeal P * J) := by
  have hne : maximalIdeal P * J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal P).ne_top Ideal.mul_le_left
  have : Nontrivial (P ⧸ maximalIdeal P * J) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The test ring `P ⧸ 𝔪 * J` of a Noetherian local ring is Artinian when `𝔪 ^ m ≤ J`. -/
theorem isArtinianRing_quotient_maximalIdeal_mul [IsNoetherianRing P] {J : Ideal P} {m : ℕ}
    (hJ : maximalIdeal P ^ m ≤ J) : IsArtinianRing (P ⧸ maximalIdeal P * J) := by
  have := isLocalRing_quotient_maximalIdeal_mul J
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨m + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (maximalIdeal P * J))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.zero_eq_bot]
  apply Ideal.map_mk_eq_bot_of_le
  rw [pow_succ']
  exact Ideal.mul_mono_right hJ

end IsLocalRing

namespace Algebra.FormallySmooth

/-- **The derivation of a test lift.** Let `J ≤ 𝔪` be ideals of `P` and let
`ψ : P →ₐ[R] P ⧸ 𝔪 * J` lift the quotient map `P → P ⧸ J`. Then `ψ` minus the quotient map is
an `R`-derivation into the square-zero kernel of `P ⧸ 𝔪 * J → P ⧸ J`, and it vanishes at every
`x` whose differential lies in `𝔪 • Ω[P⁄R]`, since `𝔪` kills that kernel. -/
theorem lift_eq_mk_of_D_mem_smul {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
    {𝔪 J : Ideal P} (hJ : J ≤ 𝔪) (ψ : P →ₐ[R] P ⧸ 𝔪 * J)
    (hψ : (Ideal.Quotient.factorₐ R (Ideal.mul_le_right : 𝔪 * J ≤ J)).comp ψ =
      Ideal.Quotient.mkₐ R J)
    {x : P} (hx : D R P x ∈ 𝔪 • (⊤ : Submodule P Ω[P⁄R])) :
    ψ x = Ideal.Quotient.mk (𝔪 * J) x := by
  let g : P ⧸ 𝔪 * J →ₐ[R] P ⧸ J := Ideal.Quotient.factorₐ R Ideal.mul_le_right
  have hK : RingHom.ker g ^ 2 = ⊥ := Ideal.Quotient.ker_factorₐ_mul_sq_eq_bot hJ
  have he : (Ideal.Quotient.mkₐ R (RingHom.ker g)).comp ψ =
      IsScalarTower.toAlgHom R P ((P ⧸ 𝔪 * J) ⧸ RingHom.ker g) := by
    apply AlgHom.ext
    intro y
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
      IsScalarTower.algebraMap_apply P (P ⧸ 𝔪 * J) ((P ⧸ 𝔪 * J) ⧸ RingHom.ker g),
      Ideal.Quotient.algebraMap_eq (RingHom.ker g)]
    refine Ideal.Quotient.eq.mpr ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← AlgHom.comp_apply, hψ,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
      Ideal.Quotient.mkₐ_eq_mk]
  let δ := derivationToSquareZeroOfLift (RingHom.ker g) hK ψ he
  have hδ : δ.liftKaehlerDifferential (D R P x) = 0 := by
    refine Submodule.smul_induction_on (p := fun ω => δ.liftKaehlerDifferential ω = 0) hx ?_ ?_
    · intro a ha ω _
      have h : ((a • δ.liftKaehlerDifferential ω : RingHom.ker g) : P ⧸ 𝔪 * J) = 0 := by
        rw [Submodule.coe_smul_of_tower, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.mk_mul_eq_zero_of_mem_ker_factorₐ ha (δ.liftKaehlerDifferential ω).2
      rw [map_smul]
      exact Subtype.ext h
    · intro ω₁ ω₂ h₁ h₂
      rw [map_add, h₁, h₂, add_zero]
  rw [Derivation.liftKaehlerDifferential_comp_D] at hδ
  have h := congrArg Subtype.val hδ
  rw [derivationToSquareZeroOfLift_apply, ZeroMemClass.coe_zero, sub_eq_zero,
    Ideal.Quotient.algebraMap_eq] at h
  exact h

/-- **The Artinian-test criterion for formal smoothness.** Let `S` be a local `R`-algebra and
`P → S` a surjection of `R`-algebras from a Noetherian local `R`-algebra `P` that is formally
smooth over `R` with finite free `Ω[P⁄R]`. Suppose that for every surjection `g : A' → A` of
`R`-algebras with `A'` Artinian local and `(ker g) ^ 2 = 0`, every surjective `R`-algebra map
`S → A` lifts through `g`. Then `S` is formally smooth over `R`. Only one test extension is used,
`P ⧸ 𝔪 J → P ⧸ J` with `J = ker (P → S) + 𝔪 ^ m` for the Artin–Rees exponent `m`. -/
theorem of_lift_artinianLocal_squareZero {R S : Type*} {P : Type v} [CommRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S] [Algebra.FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (hsurj : Function.Surjective (algebraMap P S))
    (H : ∀ (A' A : Type v) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra R A'] [Algebra R A] (g : A' →ₐ[R] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : S →ₐ[R] A, Function.Surjective φ →
        ∃ ψ : S →ₐ[R] A', g.comp ψ = φ) :
    Algebra.FormallySmooth R S := by
  have : IsLocalHom (algebraMap P S) := .of_surjective _ hsurj
  have hPκ : Function.Surjective (algebraMap P (ResidueField S)) := by
    rw [IsScalarTower.algebraMap_eq P S (ResidueField S)]
    exact residue_surjective.comp hsurj
  have hker : RingHom.ker (Algebra.ofId P (ResidueField S)) = maximalIdeal P := by
    ext x
    change residue S (algebraMap P S x) = 0 ↔ x ∈ maximalIdeal P
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap]
  have hI : RingHom.ker (algebraMap P S) ≤ maximalIdeal P := by
    intro x hx
    rw [← hker, RingHom.mem_ker, Algebra.ofId_apply,
      IsScalarTower.algebraMap_apply P S (ResidueField S), RingHom.mem_ker.mp hx, map_zero]
  obtain ⟨m, hm0, hm⟩ :=
    Ideal.exists_inf_mul_sup_pow_eq_mul (RingHom.ker (algebraMap P S)) (maximalIdeal P)
  obtain ⟨J, hJdef⟩ : ∃ J, J = RingHom.ker (algebraMap P S) ⊔ maximalIdeal P ^ m := ⟨_, rfl⟩
  rw [← hJdef] at hm
  have hIJ : RingHom.ker (algebraMap P S) ≤ J := hJdef ▸ le_sup_left
  have hJm : maximalIdeal P ^ m ≤ J := hJdef ▸ le_sup_right
  have hJ : J ≤ maximalIdeal P := hJdef ▸ sup_le hI (Ideal.pow_le_self hm0.ne')
  -- The single test extension `g : P ⧸ 𝔪 * J → P ⧸ J`.
  have := isLocalRing_quotient_maximalIdeal_mul J
  have := isArtinianRing_quotient_maximalIdeal_mul hJm
  let g : P ⧸ maximalIdeal P * J →ₐ[R] P ⧸ J := Ideal.Quotient.factorₐ R Ideal.mul_le_right
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective Ideal.mul_le_right
  have hK : RingHom.ker g ^ 2 = ⊥ := Ideal.Quotient.ker_factorₐ_mul_sq_eq_bot hJ
  -- The map `φ : S → P ⧸ J` induced by `P → P ⧸ J`, and its lift `ψ`.
  let f : P →ₐ[R] S := IsScalarTower.toAlgHom R P S
  have hfJ : RingHom.ker f.toRingHom ≤ RingHom.ker (Ideal.Quotient.mkₐ R J).toRingHom := by
    intro x hx
    have hx' : x ∈ RingHom.ker (algebraMap P S) := hx
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx')
  let φ : S →ₐ[R] P ⧸ J := AlgHom.liftOfSurjective f hsurj (Ideal.Quotient.mkₐ R J) hfJ
  have hφ : Function.Surjective φ :=
    AlgHom.liftOfSurjective_surjective f hsurj _ hfJ (Ideal.Quotient.mkₐ_surjective R J)
  obtain ⟨ψ, hψ⟩ := H (P ⧸ maximalIdeal P * J) (P ⧸ J) g hg hK φ hφ
  have hψP : g.comp (ψ.comp f) = Ideal.Quotient.mkₐ R J := by
    rw [← AlgHom.comp_assoc, hψ]
    exact AlgHom.liftOfSurjective_comp f hsurj _ hfJ
  -- The Jacobian criterion.
  rw [iff_injective_cotangentComplexBaseChange_residueField P hsurj (IsNoetherian.noetherian _),
    injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective (R := P) (S := ResidueField S)
    (M := RingHom.ker (algebraMap P S)) hPκ z
  simp only [TensorProduct.mk_apply] at hz ⊢
  change (1 : ResidueField S) • ((1 : ResidueField S) ⊗ₜ[P] D R P (x : P)) = 0 at hz
  rw [one_smul] at hz
  -- `1 ⊗ dx = 0` in `κ ⊗ Ω[P⁄R]` gives `dx ∈ 𝔪 • Ω[P⁄R]`.
  have hD : D R P (x : P) ∈ maximalIdeal P • (⊤ : Submodule P Ω[P⁄R]) := by
    let eκ := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P (ResidueField S)) hPκ
    have h1 : (eκ.symm.toLinearMap.rTensor Ω[P⁄R])
        ((1 : ResidueField S) ⊗ₜ[P] D R P (x : P)) = 0 := by
      rw [hz, map_zero]
    rw [LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply, map_one] at h1
    have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[P⁄R]
      (RingHom.ker (Algebra.ofId P (ResidueField S)))) h1
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero] at h2
    rwa [← hker]
  -- Hence `x ∈ 𝔪 * J`, so `x ∈ I ⊓ 𝔪 * J = 𝔪 * I` by Artin–Rees.
  have hx0 := lift_eq_mk_of_D_mem_smul hJ (ψ.comp f) hψP hD
  have hψx : (ψ.comp f) (x : P) = 0 := by
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', RingHom.mem_ker.mp x.2, map_zero]
  rw [hψx] at hx0
  have hxmem : (x : P) ∈ maximalIdeal P * RingHom.ker (algebraMap P S) := by
    rw [← hm]
    exact Ideal.mem_inf.mpr ⟨x.2, Ideal.Quotient.eq_zero_iff_mem.mp hx0.symm⟩
  -- Hence `1 ⊗ x = 0` in `κ ⊗ I`.
  have hmI : (maximalIdeal P • (⊤ : Submodule P (RingHom.ker (algebraMap P S)))).map
      (RingHom.ker (algebraMap P S)).subtype =
        maximalIdeal P * RingHom.ker (algebraMap P S) := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul]
  rw [← hmI] at hxmem
  obtain ⟨y, hy, hxy⟩ := hxmem
  have hyx : y = x := Subtype.ext hxy
  subst hyx
  refine Submodule.smul_induction_on
    (p := fun y => (1 : ResidueField S) ⊗ₜ[P] y = 0) hy ?_ ?_
  · intro a ha y _
    have ha' : algebraMap P (ResidueField S) a = 0 := by
      rw [← hker] at ha
      exact RingHom.mem_ker.mp ha
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, ha',
      zero_tmul]
  · intro y₁ y₂ h₁ h₂
    rw [tmul_add, h₁, h₂, add_zero]

/-- **The Artinian-test criterion for local algebras essentially of finite type.** Let `R` be a
Noetherian ring, `B` a finite type `R`-algebra and `S` the localization of `B` at a prime `q`.
Suppose that for every surjection `g : A' → A` of `R`-algebras with `A'` Artinian local and
`(ker g) ^ 2 = 0`, every surjective `R`-algebra map `S → A` lifts through `g`. Then `S` is
formally smooth over `R`. The presentation used is the localization of a polynomial ring over `R`
at the inverse image of `q`, as in Mathlib's
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`. -/
theorem of_lift_artinianLocal_squareZero_of_isLocalization {R : Type u} {B S : Type*}
    [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [CommRing S] [Algebra R S] [Algebra B S] [IsScalarTower R B S] (q : Ideal B) [q.IsPrime]
    [IsLocalization.AtPrime S q]
    (H : ∀ (A' A : Type u) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra R A'] [Algebra R A] (g : A' →ₐ[R] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : S →ₐ[R] A, Function.Surjective φ →
        ∃ ψ : S →ₐ[R] A', g.comp ψ = φ) :
    Algebra.FormallySmooth R S := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  let q' : Ideal (MvPolynomial (Fin n) R) := q.comap f₀
  let P' := Localization.AtPrime q'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := q'.primeCompl)
      (f := (IsScalarTower.toAlgHom R B S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := q.primeCompl) S ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := q'.primeCompl) _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  algebraize [fP.toRingHom]
  have : FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization q'.primeCompl
  have : FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  have : IsNoetherianRing P' := IsLocalization.isNoetherianRing q'.primeCompl P' inferInstance
  exact of_lift_artinianLocal_squareZero (P := P') hf₁ H

end Algebra.FormallySmooth
