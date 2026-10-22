/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.ResidueTensor
public import Aglib.RingTheory.Flat.LocalCriterion.Tensor
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Finite freeness from all positive adic reductions

A finite module over a Noetherian local ring is free if its reductions modulo
all positive powers of a proper ideal are flat. The ideal need not be maximal,
and neither the ring nor the module is assumed complete. A lifted residue
basis gives one original surjection. Its actual scalar extensions are
injective by the flat-quotient residue criterion; Krull intersection then
annihilates the kernel of the original surjection. The basis index may be empty.
-/

@[expose] public section

noncomputable section

open Module TensorProduct IsLocalRing

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The original base change of a surjection to a local algebra is injective
if its target is flat, its kernel is finite, and the original residue map is
injective. The residue comparison is the native cancellation of base change. -/
theorem baseChange_injective_of_surjective_of_flat_of_residue_injective
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (f : M →ₗ[R] N)
    [Module.Finite S (LinearMap.ker (f.baseChange S))]
    [Module.Flat S (S ⊗[R] N)]
    (hs : Function.Surjective f)
    (hi : Function.Injective (f.lTensor (ResidueField R))) :
    Function.Injective (f.baseChange S) := by
  have hfield : Function.Injective (f.lTensor (ResidueField S)) :=
    Module.Flat.lTensor_injective_of_baseChange_injective
      (ResidueField R) (ResidueField S) f hi
  have : IsLocalHom (algebraMap S S) := by
    change IsLocalHom (RingHom.id S)
    infer_instance
  apply injective_of_surjective_of_flat_quotient_of_residue_injective
    (R := S) (S := S) (f.baseChange S) (f.lTensor_surjective S hs)
  change Function.Injective ((f.baseChange S).baseChange (ResidueField S))
  rw [LinearMap.baseChange_baseChange]
  exact (AlgebraTensorModule.cancelBaseChange R S (ResidueField S)
    (ResidueField S) N).symm.injective.comp (hfield.comp
      (AlgebraTensorModule.cancelBaseChange R S (ResidueField S)
        (ResidueField S) M).injective)

/-- If every positive adic reduction of a map is injective, its original map
is injective when the source is finite over a Noetherian local ring. -/
theorem injective_of_baseChange_quotient_pow_injective
    [IsNoetherianRing R] [Module.Finite R M]
    (J : Ideal R) (hJ : J ≠ ⊤) (f : M →ₗ[R] N)
    (hf : ∀ n : ℕ, 0 < n → Function.Injective (f.baseChange (R ⧸ J ^ n))) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hfx : f x = 0 := hx
  have hmem : x ∈ (⨅ n : ℕ, J ^ n • ⊤ : Submodule R M) := by
    apply (Submodule.mem_iInf _).mpr
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have ht : (1 : R ⧸ J ^ n) ⊗ₜ[R] x = 0 :=
        hf n (Nat.pos_of_ne_zero hn) (by simp [hfx])
      have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul M (J ^ n)) ht
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
        map_zero, Submodule.Quotient.mk_eq_zero] using hq
  exact (J.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) hJ).le hmem

end LinearMap

namespace Module

variable {R M : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

/-- A finite module over a Noetherian local ring is free if all its positive
reductions modulo powers of a proper ideal are flat over the quotient rings.
No completeness or positive-rank assumption is imposed. -/
theorem free_of_flat_quotient_pow [IsNoetherianRing R] [Module.Finite R M]
    (J : Ideal R) (hJ : J ≠ ⊤)
    (hflat : ∀ n : ℕ, 0 < n → Module.Flat (R ⧸ J ^ n) ((R ⧸ J ^ n) ⊗[R] M)) :
    Module.Free R M := by
  classical
  let k := ResidueField R
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  let b : Basis ι k (k ⊗[R] M) := Module.Free.chooseBasis k (k ⊗[R] M)
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ : ∃ v : ι → M, ∀ i, (1 : k) ⊗ₜ[R] v i = b i := by
    choose v hv using fun i ↦
      TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective (b i)
    exact ⟨v, hv⟩
  let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  have hs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  have hk : Function.Injective (f.lTensor k) := by
    have hs' : Function.Surjective (f.baseChange k) := f.lTensor_surjective k hs
    change Function.Injective (f.baseChange k)
    rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (ι →₀ R)) (f := f.baseChange k),
      ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (ι →₀ R)),
      ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range (f.baseChange k))),
      LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (ι →₀ R)),
      LinearMap.range_eq_top.mpr hs', finrank_top]
    simp only [Module.finrank_tensorProduct, Module.finrank_self,
      Module.finrank_finsupp_self, one_mul, add_zero]
    exact (Module.finrank_eq_card_basis b).symm
  have hi : Function.Injective f := by
    apply LinearMap.injective_of_baseChange_quotient_pow_injective J hJ f
    intro n hn
    have hnJ : J ^ n ≠ ⊤ := ne_top_of_le_ne_top hJ (Ideal.pow_le_self hn.ne')
    let S := R ⧸ J ^ n
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hnJ
    have : IsLocalRing S := .of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap R S) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : Module.Flat S (S ⊗[R] M) := hflat n hn
    exact LinearMap.baseChange_injective_of_surjective_of_flat_of_residue_injective S f hs hk
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hi, hs⟩)

end Module
