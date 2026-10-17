/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GenericFreeness.Noetherian
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Generic flatness at localizations of the algebra

Let `B` be an `A`-algebra and `M` a `B`-module. If `M[1/a]` is flat over `A[1/a]`, then every
localization of `M` at a submonoid of `B` containing the image of `a` is flat over `A`. With
generic freeness (`Module.Finite.exists_ne_zero_free_localizedModule_away`) this gives the
local form of generic flatness: for a Noetherian domain `A`, a finitely generated
`A`-algebra `B` and a finite `B`-module `M`, there is `a ≠ 0` such that `M_P` is flat over
`A` for every prime `P` of `B` not containing `a` (Stacks Project, Tag 051R, Lemma 10.118.1,
combined with flatness of localization).

* `Module.Flat.of_isLocalizedModule_of_isScalarTower`: flatness over `R` passes to a
  localization at a submonoid of an `R`-algebra.
* `Module.flat_of_isLocalizedModule_of_flat_localizedModule_away`: the statement above.
* `Module.Finite.exists_ne_zero_flat_localizedModule_primeCompl`: the local form of generic
  flatness.
-/

@[expose] public section

open TensorProduct

namespace Module

/-- Flatness over `R` passes to the localization of an `A`-module at a submonoid of the
`R`-algebra `A`: tensor products over `R` commute with the localization. -/
theorem Flat.of_isLocalizedModule_of_isScalarTower {R A M M' : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    (S : Submonoid A) (g : M →ₗ[A] M') [IsLocalizedModule S g] [hM : Module.Flat R M] :
    Module.Flat R M' := by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N => ?_
  have H := Module.Flat.iff_lTensor_injectiveₛ.mp hM N
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := A)] at H ⊢
  rw [← IsLocalizedModule.map_lTensor A S N.subtype g]
  exact IsLocalizedModule.map_injective S _ _ _ H

/-- If `M[1/a]` is flat over `A[1/a]`, every localization of the `B`-module `M` at a
submonoid of `B` containing the image of `a` is flat over `A`. -/
theorem flat_of_isLocalizedModule_of_flat_localizedModule_away {A B M : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (a : A) [Module.Flat (Localization.Away a) (LocalizedModule.Away a M)]
    (T : Submonoid B) (haT : algebraMap A B a ∈ T) {M' : Type*} [AddCommGroup M']
    [Module A M'] [Module B M'] [IsScalarTower A B M'] (g : M →ₗ[B] M')
    [IsLocalizedModule T g] :
    Module.Flat A M' := by
  have : Module.Flat A (Localization.Away a) := IsLocalization.flat _ (Submonoid.powers a)
  have : Module.Flat A (LocalizedModule.Away a M) := Module.Flat.trans A (Localization.Away a) _
  let f'' := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B a)) M
  have : IsLocalizedModule (Submonoid.powers a) (f''.restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers a f''
  have : Module.Flat A (LocalizedModule (Submonoid.powers (algebraMap A B a)) M) :=
    Module.Flat.of_linearEquiv (IsLocalizedModule.linearEquiv (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M) (f''.restrictScalars A)).symm
  have hle : Submonoid.powers (algebraMap A B a) ≤ T := Submonoid.powers_le.mpr haT
  exact Flat.of_isLocalizedModule_of_isScalarTower T
    (IsLocalizedModule.liftOfLE _ T hle f'' g)

/-- **Generic flatness at primes**: for a Noetherian domain `A`, a finitely generated
`A`-algebra `B` and a finite `B`-module `M`, there is `a ≠ 0` such that for every prime `P` of
`B` not containing the image of `a`, the localization `M_P` is flat over `A`. -/
theorem Finite.exists_ne_zero_flat_localizedModule_primeCompl {A B : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal B) [P.IsPrime], algebraMap A B a ∉ P →
      Module.Flat A (LocalizedModule P.primeCompl M) := by
  obtain ⟨a, ha, hflat⟩ := Finite.exists_ne_zero_flat_localizedModule_away (A := A) (B := B) M
  refine ⟨a, ha, fun P _ haP => ?_⟩
  exact flat_of_isLocalizedModule_of_flat_localizedModule_away a P.primeCompl haP
    (LocalizedModule.mkLinearMap P.primeCompl M)

end Module
