/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.Generators
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sets.OpenCover

/-!
# Finite affine atlases and closed immersions from generators

A compact source has a finite affine atlas subordinate to affine target opens.
For a locally finite-type map the chart rings have finite generating sets.
If a map between affine schemes captures the relative algebra generators,
it is a closed immersion. These are finite-atlas inputs to immersion into a
finite-presentation scheme, not an assumption that such a hull already exists.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- A finite affine source atlas subordinate to affine target opens. -/
theorem exists_finite_affine_cover_subordinate (f : X ⟶ S) [CompactSpace X] :
    ∃ (t : Finset X) (V : t → X.Opens) (U : t → S.Opens),
      IsOpenCover V ∧ ∀ a, IsAffineOpen (V a) ∧ IsAffineOpen (U a) ∧
        V a ≤ f ⁻¹ᵁ U a := by
  classical
  have hlocal (x : X) : ∃ (V : X.Opens) (U : S.Opens),
      IsAffineOpen V ∧ IsAffineOpen U ∧ x ∈ V ∧ V ≤ f ⁻¹ᵁ U := by
    obtain ⟨U, hU, hxU, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ U from hxU)
    exact ⟨V, U, hV, hU, hxV, hVU⟩
  choose V U hV hU hxV hVU using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t, fun a => V a, fun a => U a, ?_, fun a => ⟨hV a, hU a, hVU a⟩⟩
  apply top_unique
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

/-- The actual chart ring of a locally finite-type map has finite algebra generators. -/
theorem exists_finset_generators_appLE (f : X ⟶ S) [LocallyOfFiniteType f]
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) :
    let := (f.appLE U V e).hom.toAlgebra
    ∃ s : Finset Γ(X, V), Algebra.adjoin Γ(S, U) (s : Set Γ(X, V)) = ⊤ := by
  let := (f.appLE U V e).hom.toAlgebra
  exact (f.finiteType_appLE hU hV e).out

/-- Capturing relative algebra generators makes an affine map a closed immersion. -/
theorem isClosedImmersion_of_generators_in_range (h : X ⟶ Y) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] (s : Set Γ(X, ⊤))
    (hs : letI := (h ≫ g).appTop.hom.toAlgebra
      Algebra.adjoin Γ(S, ⊤) s = ⊤)
    (hh : s ⊆ Set.range h.appTop) : IsClosedImmersion h := by
  let := (h ≫ g).appTop.hom.toAlgebra
  apply IsClosedImmersion.of_surjective_of_isAffine
  exact RingHom.surjective_of_adjoin_eq_top h.appTop.hom g.appTop.hom rfl s hs hh

/-- The literal map into an affine product is closed when the other projection
captures a set of generators relative to the first factor. -/
theorem isClosedImmersion_pullback_lift_of_generators
    {W T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine W] [IsAffine T]
    (a : Y ⟶ T) (b : W ⟶ T) (p : X ⟶ Y) (q : X ⟶ W)
    (hpq : p ≫ a = q ≫ b) (s : Set Γ(X, ⊤))
    (hs : letI := q.appTop.hom.toAlgebra
      Algebra.adjoin Γ(W, ⊤) s = ⊤)
    (hp : s ⊆ Set.range p.appTop) :
    IsClosedImmersion (pullback.lift p q hpq) := by
  apply isClosedImmersion_of_generators_in_range (pullback.lift p q hpq)
    (pullback.snd a b) s
  · exact (congrArg (fun r : X ⟶ W =>
        letI := r.appTop.hom.toAlgebra
        Algebra.adjoin Γ(W, ⊤) s = ⊤) (pullback.lift_snd p q hpq)).mpr hs
  · intro x hx
    obtain ⟨y, hy⟩ := hp hx
    refine ⟨(pullback.fst a b).appTop y, ?_⟩
    change ((pullback.lift p q hpq ≫ pullback.fst a b).appTop) y = x
    simpa only [pullback.lift_fst] using hy

end AlgebraicGeometry.Scheme.Hom
