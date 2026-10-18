/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Universal
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The disjoint union of the rank strata

Let `F` be a quasi-coherent `𝒪_S`-module of finite presentation, with rank strata
`S_r = rankStratum F hF r`. This file packages the strata as one morphism
`rankStrataι F hF : ∐ r, S_r ⟶ S` (through `Sigma.desc (rankStratumι F hF)`) and proves the
universal property of the flattening stratification in the case `n = 0`, in its locally free
form (Stacks Project, Tag 05P9 (Lemma 31.9.7); Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, Theorem 4.3 (ii), case `n = 0`, pp. 19–20). Stacks 05P9
represents the functor of morphisms along which `F` becomes flat; for finitely presented `F` this
is local freeness by Stacks Project, Tag 05P2 (Lemma 28.21.2), which is not formalized here:

* `mem_range_sigmaι_rankStratum_iff`: a point of `T` is sent by `h : T ⟶ ∐ r, S_r` into the
  component `S_r` exactly when the fibre of `F` at its image in `S` has dimension `r`;
* `rankStrataι_mono`: `rankStrataι F hF` is a monomorphism;
* `exists_lift_rankStrataι_iff`: a morphism `g : T ⟶ S` factors through `rankStrataι F hF` if and
  only if `g^* F` is finite locally free.

`rankStrataι F hF` is in general not an immersion: its source carries the disjoint union topology.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (F : S.Modules) (hF : QuasiCoherent.affineLocallyFiniteType S F)

/-- The disjoint union `∐ r, S_r` of the rank strata of `F`. -/
abbrev rankStrata : Scheme.{u} :=
  ∐ fun r : ℕ => rankStratum F hF r

/-- The morphism `∐ r, S_r ⟶ S` induced by the immersions of the rank strata. -/
def rankStrataι : rankStrata F hF ⟶ S :=
  Sigma.desc (rankStratumι F hF)

@[reassoc (attr := simp)]
theorem sigmaι_rankStrataι (r : ℕ) :
    Sigma.ι (fun r : ℕ => rankStratum F hF r) r ≫ rankStrataι F hF = rankStratumι F hF r :=
  Sigma.ι_comp_desc _ _

/-- Every point of `∐ r, S_r` lies in the image of one of the components. -/
private theorem exists_sigmaι_rankStratum_eq (x : rankStrata F hF) :
    ∃ (r : ℕ) (y : rankStratum F hF r), Sigma.ι (fun r : ℕ => rankStratum F hF r) r y = x := by
  obtain ⟨r, y, hy⟩ := (sigmaOpenCover (fun r : ℕ => rankStratum F hF r)).exists_eq x
  exact ⟨r, y, hy⟩

/-- A point of `T` is sent by `h : T ⟶ ∐ r, S_r` into the component `S_r` exactly when the fibre
of `F` at its image in `S` has dimension `r`. -/
theorem mem_range_sigmaι_rankStratum_iff [F.IsFinitePresentation] (h : T ⟶ rankStrata F hF)
    (t : T) (r : ℕ) :
    h t ∈ Set.range (Sigma.ι (fun r : ℕ => rankStratum F hF r) r) ↔
      sheafRank F ((h ≫ rankStrataι F hF) t) = r := by
  have key : ∀ (s : ℕ) (y : rankStratum F hF s),
      Sigma.ι (fun r : ℕ => rankStratum F hF r) s y = h t →
        sheafRank F ((h ≫ rankStrataι F hF) t) = s := by
    intro s y hy
    rw [Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, sigmaι_rankStrataι]
    exact (mem_range_rankStratumι_iff F hF _ s).mp ⟨y, rfl⟩
  constructor
  · rintro ⟨y, hy⟩
    exact key r y hy
  · intro hr
    obtain ⟨s, y, hy⟩ := exists_sigmaι_rankStratum_eq F hF (h t)
    obtain rfl : s = r := (key s y hy).symm.trans hr
    exact ⟨y, hy⟩

/-- Restricted to an open subset of `T` that `h : T ⟶ ∐ r, S_r` sends into the component `S_r`,
the morphism `h` factors through `S_r`. -/
private theorem range_comp_subset_range_sigmaι (h : T ⟶ rankStrata F hF) (r : ℕ) {U : T.Opens}
    (hU : ∀ t ∈ U, h t ∈ Set.range (Sigma.ι (fun r : ℕ => rankStratum F hF r) r)) :
    Set.range (U.ι ≫ h) ⊆ Set.range (Sigma.ι (fun r : ℕ => rankStratum F hF r) r) := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact hU _ u.2

/-- **The disjoint union of the rank strata is a monomorphism** into `S` (Stacks Project,
Tag 05P9). -/
instance rankStrataι_mono [F.IsFinitePresentation] : Mono (rankStrataι F hF) := by
  constructor
  intro T a b hab
  apply hom_ext_of_forall
  intro t
  obtain ⟨r, y, hy⟩ := exists_sigmaι_rankStratum_eq F hF (a t)
  let ιr := Sigma.ι (fun r : ℕ => rankStratum F hF r) r
  let U : T.Opens := a ⁻¹ᵁ ιr.opensRange
  have hUa : ∀ t' ∈ U, a t' ∈ Set.range ιr := fun _ ht' => ht'
  have hUb : ∀ t' ∈ U, b t' ∈ Set.range ιr := fun t' ht' => by
    rw [mem_range_sigmaι_rankStratum_iff F hF b t' r, ← hab,
      ← mem_range_sigmaι_rankStratum_iff F hF a t' r]
    exact ht'
  have htU : t ∈ U := show a t ∈ Set.range ιr from ⟨y, hy⟩
  refine ⟨U, htU, ?_⟩
  let la := IsOpenImmersion.lift ιr (U.ι ≫ a) (range_comp_subset_range_sigmaι F hF a r hUa)
  let lb := IsOpenImmersion.lift ιr (U.ι ≫ b) (range_comp_subset_range_sigmaι F hF b r hUb)
  have hla : la ≫ ιr = U.ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hlb : lb ≫ ιr = U.ι ≫ b := IsOpenImmersion.lift_fac _ _ _
  have hl : la = lb := by
    rw [← cancel_mono (rankStratumι F hF r), ← sigmaι_rankStrataι F hF r]
    simp only [← Category.assoc]
    rw [hla, hlb, Category.assoc, Category.assoc, hab]
  rw [← hla, ← hlb, hl]

/-- **Universal property of the disjoint union of the rank strata** (Stacks Project, Tag 05P9
(Lemma 31.9.7); Nitsure, arXiv:math/0504590v1, Theorem 4.3 (ii), case `n = 0`, in the locally free
form): for `F` of finite presentation, a morphism `g : T ⟶ S` factors through
`rankStrataι F hF : ∐ r, S_r ⟶ S` if and only if `g^* F` is finite locally free. The factorization
is unique by `rankStrataι_mono`. Stacks states flatness of `g^* F`, which is equivalent by
Stacks Project, Tag 05P2; that equivalence is not formalized here. -/
theorem exists_lift_rankStrataι_iff [F.IsFinitePresentation] (g : T ⟶ S) :
    (∃ h : T ⟶ rankStrata F hF, h ≫ rankStrataι F hF = g) ↔
      IsFiniteLocallyFree T ((pullback g).obj F) := by
  have hmono := rankStrataι_mono F hF
  constructor
  · rintro ⟨h, rfl⟩
    refine (isFiniteLocallyFree_pullback_iff F hF _).mpr fun t => ?_
    obtain ⟨r, y, hy⟩ := exists_sigmaι_rankStratum_eq F hF (h t)
    let ιr := Sigma.ι (fun r : ℕ => rankStratum F hF r) r
    let U : T.Opens := h ⁻¹ᵁ ιr.opensRange
    have hU : ∀ t' ∈ U, h t' ∈ Set.range ιr := fun _ ht' => ht'
    have htU : t ∈ U := show h t ∈ Set.range ιr from ⟨y, hy⟩
    refine ⟨U, htU, r, IsOpenImmersion.lift ιr (U.ι ≫ h)
      (range_comp_subset_range_sigmaι F hF h r hU), ?_⟩
    rw [← sigmaι_rankStrataι F hF r, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
  · intro hfree
    choose U hU r g' hg' using (isFiniteLocallyFree_pullback_iff F hF g).mp hfree
    have hcover : IsOpenCover U :=
      eq_top_iff.mpr fun t _ => Opens.mem_iSup.mpr ⟨t, hU t⟩
    let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U hcover
    let k : ∀ t, 𝒰.X t ⟶ rankStrata F hF := fun t =>
      g' t ≫ Sigma.ι (fun r : ℕ => rankStratum F hF r) (r t)
    have hk : ∀ t, k t ≫ rankStrataι F hF = 𝒰.f t ≫ g := fun t => by
      change (g' t ≫ Sigma.ι (fun r : ℕ => rankStratum F hF r) (r t)) ≫ rankStrataι F hF =
        (U t).ι ≫ g
      rw [Category.assoc, sigmaι_rankStrataι]
      exact hg' t
    have hcompat :
        ∀ t s, pullback.fst (𝒰.f t) (𝒰.f s) ≫ k t = pullback.snd (𝒰.f t) (𝒰.f s) ≫ k s := by
      intro t s
      rw [← cancel_mono (rankStrataι F hF), Category.assoc, Category.assoc, hk, hk,
        pullback.condition_assoc]
    refine ⟨𝒰.glueMorphisms k hcompat, 𝒰.hom_ext _ _ fun t => ?_⟩
    rw [Cover.ι_glueMorphisms_assoc]
    exact hk t

end AlgebraicGeometry.Scheme.Modules
