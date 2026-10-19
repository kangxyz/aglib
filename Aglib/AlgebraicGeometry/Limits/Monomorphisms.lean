/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Monomorphisms of schemes: local factorization and disjoint unions

* `exists_lift_of_mono_of_forall_exists`: for a monomorphism `m : Z ⟶ S`, a morphism
  `g : T ⟶ S` factors through `m` as soon as it does on an open neighbourhood of every point of
  `T`; the local factorizations agree on overlaps because `m` is a monomorphism, and glue.
* `exists_sigmaι_eq`: every point of a disjoint union `∐ X` lies in one component.
* `mono_sigmaDesc_of_pairwise_disjoint`: the morphism `∐ X ⟶ S` induced by monomorphisms
  `X i ⟶ S` with pairwise disjoint images is a monomorphism.

These are the formal parts of the universal properties of flattening stratifications, where the
strata are monomorphisms with disjoint images (Stacks Project, Tag 05P9; Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 4.3 (ii)).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- **Factorization through a monomorphism is local on the source.** If `m : Z ⟶ S` is a
monomorphism and every point of `T` has an open neighbourhood `U` such that `U ⟶ T ⟶ S` factors
through `m`, then `g : T ⟶ S` factors through `m`. -/
theorem exists_lift_of_mono_of_forall_exists {Z S T : Scheme.{u}} (m : Z ⟶ S) [Mono m]
    (g : T ⟶ S) (H : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ l : U.toScheme ⟶ Z, l ≫ m = U.ι ≫ g) :
    ∃ h : T ⟶ Z, h ≫ m = g := by
  choose U hU l hl using H
  have hcover : TopologicalSpace.IsOpenCover U :=
    eq_top_iff.mpr fun t _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hU t⟩
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U hcover
  let k : ∀ t, 𝒰.X t ⟶ Z := fun t => l t
  have hk : ∀ t, k t ≫ m = 𝒰.f t ≫ g := fun t => by
    change l t ≫ m = (U t).ι ≫ g
    exact hl t
  have hcompat :
      ∀ t s, pullback.fst (𝒰.f t) (𝒰.f s) ≫ k t = pullback.snd (𝒰.f t) (𝒰.f s) ≫ k s := by
    intro t s
    rw [← cancel_mono m, Category.assoc, Category.assoc, hk, hk, pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms k hcompat, 𝒰.hom_ext _ _ fun t => ?_⟩
  rw [Cover.ι_glueMorphisms_assoc]
  exact hk t

variable {σ : Type v} [Small.{u} σ] {X : σ → Scheme.{u}}

/-- Every point of a disjoint union of schemes lies in the image of one of the components. -/
theorem exists_sigmaι_eq (x : (∐ X : Scheme.{u})) : ∃ (i : σ) (y : X i), Sigma.ι X i y = x := by
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover X).exists_eq x
  exact ⟨i, y, hy⟩

/-- **A disjoint union of monomorphisms with pairwise disjoint images is a monomorphism.** -/
theorem mono_sigmaDesc_of_pairwise_disjoint {S : Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, Mono (f i)] (hf : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) :
    Mono (Sigma.desc f) := by
  constructor
  intro T a b hab
  apply hom_ext_of_forall
  intro t
  obtain ⟨i, y, hy⟩ := exists_sigmaι_eq (a t)
  have key : ∀ z : (∐ X : Scheme.{u}), Sigma.desc f z ∈ Set.range (f i) →
      z ∈ Set.range (Sigma.ι X i) := by
    intro z hz
    obtain ⟨i', y', rfl⟩ := exists_sigmaι_eq z
    rcases eq_or_ne i' i with rfl | hne
    · exact ⟨y', rfl⟩
    · rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] at hz
      exact absurd hz (Set.disjoint_left.mp (hf hne) ⟨y', rfl⟩)
  let U : T.Opens := a ⁻¹ᵁ (Sigma.ι X i).opensRange
  have hUa : ∀ t' ∈ U, a t' ∈ Set.range (Sigma.ι X i) := fun _ ht' => ht'
  have hUb : ∀ t' ∈ U, b t' ∈ Set.range (Sigma.ι X i) := fun t' ht' => by
    apply key
    obtain ⟨y', hy'⟩ := hUa t' ht'
    rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply, ← hy', ← Scheme.Hom.comp_apply,
      Sigma.ι_comp_desc]
    exact ⟨y', rfl⟩
  have hsub : ∀ c : T ⟶ ∐ X, (∀ t' ∈ U, c t' ∈ Set.range (Sigma.ι X i)) →
      Set.range (U.ι ≫ c) ⊆ Set.range (Sigma.ι X i) := by
    rintro c hc _ ⟨u, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hc _ u.2
  refine ⟨U, show a t ∈ Set.range (Sigma.ι X i) from ⟨y, hy⟩, ?_⟩
  have hla := IsOpenImmersion.lift_fac (Sigma.ι X i) (U.ι ≫ a) (hsub a hUa)
  have hlb := IsOpenImmersion.lift_fac (Sigma.ι X i) (U.ι ≫ b) (hsub b hUb)
  have hl : IsOpenImmersion.lift (Sigma.ι X i) (U.ι ≫ a) (hsub a hUa) =
      IsOpenImmersion.lift (Sigma.ι X i) (U.ι ≫ b) (hsub b hUb) := by
    rw [← cancel_mono (f i), ← Sigma.ι_comp_desc f i, ← Category.assoc, ← Category.assoc, hla,
      hlb, Category.assoc, Category.assoc, hab]
  rw [← hla, ← hlb, hl]

end AlgebraicGeometry.Scheme
