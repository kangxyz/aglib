/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The kernel of a composite with an epimorphism

Let `i : P ⟶ Q` be a kernel of `q : Q ⟶ R` and `μ : F ⟶ Q` an epimorphism in an abelian category.
A kernel `ιK : K ⟶ F` of `μ ≫ q` is the pullback of `i` along `μ`: a map to `F` whose composite
with `μ` factors through `i` is killed by `μ ≫ q`. Hence every `k : K ⟶ P` with
`k ≫ i = ιK ≫ μ` is an epimorphism (`epi_of_isKernel_comp`), since pullbacks of epimorphisms are
epimorphisms (`Abelian.epi_snd_of_isLimit`).

For the direct image of a Hilbert family this compares the kernel of
`𝒪_T^{monomials} ↠ π_* 𝒪(r) ⟶ π_* 𝒪_Z(r)` with `π_* I_Z(r)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The kernel of a composite with an epimorphism maps onto the kernel**: for a kernel
`i : P ⟶ Q` of `q : Q ⟶ R`, an epimorphism `μ : F ⟶ Q` and a kernel `ιK : K ⟶ F` of `μ ≫ q`,
every `k : K ⟶ P` with `k ≫ i = ιK ≫ μ` is an epimorphism. -/
theorem epi_of_isKernel_comp {F Q R P K : C} {q : Q ⟶ R} {i : P ⟶ Q} {wi : i ≫ q = 0}
    (hi : IsLimit (KernelFork.ofι i wi)) (μ : F ⟶ Q) [Epi μ] {ιK : K ⟶ F}
    {wK : ιK ≫ μ ≫ q = 0} (hK : IsLimit (KernelFork.ofι ιK wK)) (k : K ⟶ P)
    (hk : k ≫ i = ιK ≫ μ) : Epi k := by
  have : Mono i := mono_of_isLimit_fork hi
  have hw (s : PullbackCone μ i) : s.fst ≫ μ ≫ q = 0 := by
    rw [← Category.assoc, s.condition, Category.assoc, wi, comp_zero]
  let l (s : PullbackCone μ i) : s.pt ⟶ K := (KernelFork.IsLimit.lift' hK s.fst (hw s)).1
  have hl (s : PullbackCone μ i) : l s ≫ ιK = s.fst :=
    (KernelFork.IsLimit.lift' hK s.fst (hw s)).2
  have hs : IsLimit (PullbackCone.mk ιK k hk.symm) := by
    refine PullbackCone.IsLimit.mk hk.symm l hl (fun s => ?_) (fun s m hm _ => ?_)
    · rw [← cancel_mono i, Category.assoc, hk, ← Category.assoc, hl s, s.condition]
    · exact Fork.IsLimit.hom_ext hK (hm.trans (hl s).symm)
  exact epi_snd_of_isLimit μ i hs

end CategoryTheory.Abelian
