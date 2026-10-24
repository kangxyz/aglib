/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantModules
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantFiniteExact
public import Mathlib.Algebra.Module.ZMod

/-!
# Proper constant modules killed by a positive power of the characteristic

Induction on the exponent uses the actual kernel of scalar multiplication and
its actual quotient. The original same-degree cohomology coefficient maps form
an exact pair of modules for the original coefficient-ring action. No finite
underlying abelian group or finite prime-field dimension is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e l

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsSepClosed k] (Y : FScheme k) [IsProper Y.hom]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (Λ : Type l) [CommRing Λ]

/-- Prime-killed constant modules obtain the native `ZMod p` action, commuting
with the original coefficient action, and hence have finite original cohomology. -/
theorem constantModule_cohomology_finite_of_prime_nsmul
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj M) := by
  have h : ∀ (V : ModuleCat.{u + 1} (ZMod p)), ∀ [Module Λ V],
      ∀ [SMulCommClass Λ (ZMod p) V], ∀ [Module.Finite Λ V],
      Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology
        Y.left.smallEtaleTopology Λ q).obj (ModuleCat.of Λ V)) := by
    intro V _ _ _
    let I : Type (u + 1) := Finset (Discrete (Module.Free.ChooseBasisIndex (ZMod p) V))
    let : HasColimitsOfShape I AddCommGrpCat.{e} :=
      @HasColimitsOfSize.has_colimits_of_shape AddCommGrpCat.{e} inferInstance
        (inferInstance : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}) I
        (inferInstance : SmallCategory I)
    exact constantModule_cohomology_finite_of_proper.{u, e, l} Y p q V Λ
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : SMulCommClass Λ (ZMod p) M :=
    ⟨fun a r x => ZMod.map_smul (DistribSMul.toAddMonoidHom M a) r x⟩
  exact h (ModuleCat.of (ZMod p) M)

/-- Induction for coefficients killed by `p^(n+1)`, preserving the actual module
and original coefficient-ring action in every cohomological degree. -/
theorem constantModule_cohomology_finite_of_succ_prime_power [IsNoetherianRing Λ]
    (q n : ℕ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, (p ^ (n + 1)) • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj M) := by
  induction n generalizing M with
  | zero =>
      exact constantModule_cohomology_finite_of_prime_nsmul Y p Λ q M
        (by simpa using hM)
  | succ n ih =>
      let N : Submodule Λ M := LinearMap.ker ((p ^ (n + 1)) • (LinearMap.id : M →ₗ[Λ] M))
      have hN : ∀ x : N, (p ^ (n + 1)) • x = 0 := by
        intro x
        apply Subtype.ext
        exact x.property
      have hQ : ∀ x : M ⧸ N, p • x = 0 := by
        intro x
        obtain ⟨m, rfl⟩ := N.mkQ_surjective x
        rw [← map_nsmul]
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        change (p ^ (n + 1)) • (p • m) = 0
        rw [← mul_nsmul, ← pow_succ']
        exact hM m
      let S := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
      let : Module.Finite Λ
          ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj S.X₁) :=
        ih (ModuleCat.of Λ N) hN
      let : Module.Finite Λ
          ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj S.X₃) :=
        constantModule_cohomology_finite_of_prime_nsmul Y p Λ q (ModuleCat.of Λ (M ⧸ N)) hQ
      exact ModuleCat.Sheaf.finite_constantCohomology_of_shortExact
        Y.left.smallEtaleTopology Λ S hS q

/-- Every positive characteristic-primary exponent gives finite original constant
cohomology over the original Noetherian coefficient ring. -/
theorem constantModule_cohomology_finite_of_prime_power [IsNoetherianRing Λ]
    (q n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, (p ^ n) • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj M) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n => exact constantModule_cohomology_finite_of_succ_prime_power Y p Λ q n M hM

end AlgebraicGeometry.Scheme.EtaleCohomology
