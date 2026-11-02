/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Mathlib.Data.Nat.Prime.Basic

/-! # Prime reduction for original constructible cohomology

A positive annihilator is reduced by strong induction through the actual
kernel of scalar multiplication and its native cokernel. These coefficients
remain constructible by the proved kernel and cokernel closure for genuine
finite-ring module sheaves. Exact scalar forgetting gives a short exact
sequence of the original abelian coefficients, so same-degree original
cohomology vanishing passes through that sequence.

On a qcqs scheme every constructible abelian coefficient has a positive
annihilator. Its vanishing therefore reduces to genuine constructible
`ZMod p` coefficients for primes `p`, retaining the original Ext universe.
No uniform annihilator on arbitrary internally torsion coefficients is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

open Constructible.Modules

variable {X : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- Vanishing for constructible prime-killed coefficients implies vanishing
for every constructible coefficient with a displayed positive annihilator.
The induction uses actual constructible kernel and cokernel coefficients,
not closure under arbitrary ambient subobjects or quotients. -/
theorem subsingleton_H_of_constructible_killed_of_prime
    (q : ℕ)
    (hprime : ∀ (G : AbelianSheaf.{u, u + 1} X) (p : ℕ), p.Prime →
      Constructible.IsConstructible G → p • 𝟙 G = 0 →
        Subsingleton (Sheaf.H.{e} G q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F)
    (n : ℕ) (hn : 0 < n) (hkill : n • 𝟙 F = 0) :
    Subsingleton (Sheaf.H.{e} F q) := by
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases h1 : n = 1
    · apply Sheaf.subsingleton_H_of_isZero
      apply (IsZero.iff_id_eq_zero F).mpr
      simpa only [h1, one_nsmul] using hkill
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact (Nat.ne_of_gt hn) (by simpa only [hzero, Nat.mul_zero] using hm)
    have hmlt : m < n := by
      rw [hm]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hp.one_lt hmpos
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let M : ModuleSheaf (ZMod n) X := TorsionZMod.sheaf X.smallEtaleTopology n F hkill
    let U := moduleUnderlying (ZMod n) X
    let a : U.obj M ≅ F := TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hkill
    have hM : IsConstructible M :=
      (isConstructible_canonicalZModSheaf_iff n hn F hkill).mpr hF
    have hkillM : n • 𝟙 M = 0 := by
      apply U.map_injective
      simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
      apply (cancel_mono a.hom).1
      simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id, zero_comp, comp_zero] using
          congrArg (fun f => a.hom ≫ f) hkill
    let φ : M ⟶ M := p • 𝟙 M
    let K := kernel φ
    let Q := cokernel (kernel.ι φ)
    have hK : IsConstructible K := isConstructible_kernel φ hM hM
    have hQ : IsConstructible Q := isConstructible_cokernel (kernel.ι φ) hK hM
    have hkillK : p • 𝟙 K = 0 := by
      apply (cancel_mono (kernel.ι φ)).1
      rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
      simpa only [φ, Preadditive.comp_nsmul, Category.comp_id] using kernel.condition φ
    have hcomp : (m • 𝟙 M) ≫ φ = 0 := by
      simpa only [φ, Preadditive.nsmul_comp, Category.id_comp,
        ← mul_smul, Nat.mul_comm m p, ← hm] using hkillM
    let t : M ⟶ K := kernel.lift φ (m • 𝟙 M) hcomp
    have ht : t ≫ kernel.ι φ = m • 𝟙 M := kernel.lift_ι _ _ _
    have hkillQ : m • 𝟙 Q = 0 := by
      apply (cancel_epi (cokernel.π (kernel.ι φ))).1
      rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
      calc
        m • cokernel.π (kernel.ι φ) =
            (m • 𝟙 M) ≫ cokernel.π (kernel.ι φ) := by
          rw [Preadditive.nsmul_comp, Category.id_comp]
        _ = (t ≫ kernel.ι φ) ≫ cokernel.π (kernel.ι φ) := by rw [ht]
        _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
    let S := ShortComplex.cokernelSequence (kernel.ι φ)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact _) (by
        change Mono (kernel.ι φ)
        infer_instance) (by
        change Epi (cokernel.π (kernel.ι φ))
        infer_instance)
    let : Subsingleton (Sheaf.H.{e} (S.map U).X₁ q) :=
      hprime (U.obj K) p hp (isConstructible_underlying hK) (by
        simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
          congrArg U.map hkillK)
    let : Subsingleton (Sheaf.H.{e} (S.map U).X₃ q) :=
      ih m hmlt (U.obj Q) (isConstructible_underlying hQ) hmpos (by
        simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
          congrArg U.map hkillQ)
    let : Subsingleton (Sheaf.H.{e} (U.obj M) q) :=
      Sheaf.H.subsingleton_middle_of_shortExact (hS.map_of_exact U) q
    exact (cohomologyMapIso_bijective a q).surjective.subsingleton

/-- On a qcqs scheme, vanishing for genuinely constructible prime-field module
coefficients implies vanishing for every original constructible abelian
coefficient. Only the constructible input receives a global annihilator. -/
theorem subsingleton_H_of_constructible_of_prime_zmod
    [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ)
    (hprime : ∀ (p : ℕ), ∀ [Fact p.Prime],
      ∀ (M : ModuleSheaf (ZMod p) X), IsConstructible M →
        Subsingleton (Sheaf.H.{e} ((moduleUnderlying (ZMod p) X).obj M) q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Subsingleton (Sheaf.H.{e} F q) := by
  obtain ⟨n, hn, hkill⟩ := Constructible.exists_positive_annihilator_of_isConstructible F hF
  apply subsingleton_H_of_constructible_killed_of_prime q ?_ F hF n hn hkill
  intro G p hp hG hkillG
  let : Fact p.Prime := ⟨hp⟩
  let M : ModuleSheaf (ZMod p) X := TorsionZMod.sheaf X.smallEtaleTopology p G hkillG
  let : Subsingleton (Sheaf.H.{e} ((moduleUnderlying (ZMod p) X).obj M) q) :=
    hprime p M ((isConstructible_canonicalZModSheaf_iff p hp.pos G hkillG).mpr hG)
  exact (cohomologyMapIso_bijective
    (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology p G hkillG) q).surjective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
