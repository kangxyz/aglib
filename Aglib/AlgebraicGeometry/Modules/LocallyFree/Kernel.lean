/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ProjectiveKernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.ShortExact

/-!
# Kernels of epimorphisms between finite locally free sheaves

Let `0 → K → M → N → 0` be a short exact sequence of module sheaves on a scheme `X` with `M` and
`N` finite locally free. Then `K` is finite locally free
(`finiteLocallyFree_X₁_of_shortExact`).

The proof is affine-local. On `Spec R` the kernel is quasi-coherent
(`isQuasicoherent_X₁_of_shortExact`), global sections are exact on the sequence
(`shortExact_globalSections_of_quasicoherent_kernel`), and the global sections of `N` form a
projective module, so `Γ(K)` is a direct summand of the finite projective module `Γ(M)`
(`ModuleCat.finite_projective_X₁_of_shortExact`); hence `K ≅ Γ(K)~` is finite locally free
(`finiteLocallyFree_tilde_of_finite_projective`). Over a general scheme the sequence pulls back to
every affine chart of `X.affineOpenCover` (`shortExact_pullback`, no flatness needed) and finite
local freeness is local (`finiteLocallyFree_of_affineCharts`). The ranks of the terms are compared
in `Aglib.AlgebraicGeometry.Modules.LocallyFree.RankAdditivity`.

Sources: Stacks has no lemma for the kernel statement (checked 2026-10-19); the nearest is Tag 0BCI
(a direct summand of a finite locally free module is finite locally free when all stalks of `O_X`
are local). The text of Stacks, Tag 0B37 (section "Rank and determinant") states, without proof,
that admissible monomorphisms of finite locally free modules are kernels of surjections. Encoded
subset: module sheaves on an arbitrary scheme; the middle and last terms finite locally free.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme, the first term of a short exact sequence whose middle and last terms are
finite locally free is finite locally free. -/
theorem finiteLocallyFree_X₁_of_shortExact_Spec (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree (Spec R) S.X₂] [IsFiniteLocallyFree (Spec R) S.X₃] :
    IsFiniteLocallyFree (Spec R) S.X₁ := by
  have : S.X₁.IsQuasicoherent := isQuasicoherent_X₁_of_shortExact hS
  have hΓ := AffineCech.shortExact_globalSections_of_quasicoherent_kernel hS
  have : Module.Projective R (S.map moduleSpecΓFunctor).X₃ :=
    projective_globalSections_of_finiteLocallyFree R S.X₃
  have : Module.Projective R (S.map moduleSpecΓFunctor).X₂ :=
    projective_globalSections_of_finiteLocallyFree R S.X₂
  have : Module.Finite R (S.map moduleSpecΓFunctor).X₂ :=
    finite_globalSections_of_finiteLocallyFree R S.X₂
  obtain ⟨_, _⟩ := ModuleCat.finite_projective_X₁_of_shortExact hΓ
  have h₁ : IsFiniteLocallyFree (Spec R) (tilde (S.map moduleSpecΓFunctor).X₁) :=
    finiteLocallyFree_tilde_of_finite_projective R _
  exact @finiteLocallyFree_of_iso _ _ _ (asIso S.X₁.fromTildeΓ) h₁

/-- **Kernels of epimorphisms between finite locally free sheaves.** In a short exact sequence
`0 → K → M → N → 0` of module sheaves on a scheme with `M` and `N` finite locally free, `K` is
finite locally free. -/
theorem finiteLocallyFree_X₁_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree X S.X₂] [IsFiniteLocallyFree X S.X₃] :
    IsFiniteLocallyFree X S.X₁ := by
  let 𝒰 := X.affineOpenCover
  refine finiteLocallyFree_of_affineCharts S.X₁ 𝒰.X 𝒰.f (fun x ↦ ⟨𝒰.idx x, 𝒰.covers x⟩)
    (fun i ↦ ?_)
  have : IsFiniteLocallyFree (Spec (𝒰.X i)) (S.map (pullback (𝒰.f i))).X₂ :=
    finiteLocallyFree_pullback (𝒰.f i) S.X₂
  have : IsFiniteLocallyFree (Spec (𝒰.X i)) (S.map (pullback (𝒰.f i))).X₃ :=
    finiteLocallyFree_pullback (𝒰.f i) S.X₃
  have h := finiteLocallyFree_X₁_of_shortExact_Spec (𝒰.X i) (shortExact_pullback (𝒰.f i) hS)
  exact @finiteLocallyFree_of_iso _ _ _ ((restrictFunctorIsoPullback (𝒰.f i)).app S.X₁).symm h

end AlgebraicGeometry.Scheme.Modules
