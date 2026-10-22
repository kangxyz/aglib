/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.CommonDomain

/-!
# The initial simultaneous boundary is empty

On the common product image, closed partial graphs identify their actual
pullback domains and their maps to the original scheme. A point over all
boundaries would therefore give one point outside every member of the
original open cover. Schematic density is required only on the common image.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Compactification

/-- Initial boundary preimages have empty intersection. The index need only
be nonempty; finiteness is needed later for the boundary modification, not
for this cover contradiction. -/
theorem iInter_preimage_boundary_eq_empty
    {M X S T : Scheme.{u}} [IsNoetherian M] {ι : Type v} [Nonempty ι]
    {Y : ι → Scheme.{u}} (pY : ∀ i, Y i ⟶ S)
    (pM : M ⟶ S) (pX : X ⟶ S)
    (π : ∀ i, M ⟶ Y i) (hπ : ∀ i, π i ≫ pY i = pM)
    (V : ∀ i, (Y i).Opens) (q : ∀ i, (V i).toScheme ⟶ X)
    (hq : ∀ i, (V i).ι ≫ pY i = q i ≫ pX)
    [∀ i, IsClosedImmersion (pullback.lift (V i).ι (q i) (hq i))]
    (j : T ⟶ M) [IsSchemeTheoreticallyDominant j] (g : T ⟶ X)
    (a : ∀ i, T ⟶ (V i).toScheme)
    (ha : ∀ i, a i ≫ (V i).ι = j ≫ π i)
    (hag : ∀ i, a i ≫ q i = g)
    (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    (⋂ i, π i ⁻¹' ((V i).ι '' (q i ⁻¹' (U i : Set X)ᶜ))) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hpoint (i : ι) :
      ∃ z : ↥(pullback (V i).ι (π i) : Scheme.{u}),
        pullback.snd (V i).ι (π i) z = x ∧
        q i (pullback.fst (V i).ι (π i) z) ∉ U i := by
    obtain ⟨y, hy, he⟩ := Set.mem_iInter.mp hx i
    have hrange : x ∈ Set.range (pullback.snd (V i).ι (π i)) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨y, he⟩
    obtain ⟨z, hz⟩ := hrange
    have hf : pullback.fst (V i).ι (π i) z = y := by
      apply (V i).ι.isOpenEmbedding.injective
      calc
        (V i).ι (pullback.fst (V i).ι (π i) z) =
            π i (pullback.snd (V i).ι (π i) z) :=
          congrArg (fun f : pullback (V i).ι (π i) ⟶ Y i ↦ f z)
            (pullback.condition (f := (V i).ι) (g := π i))
        _ = π i x := congrArg (π i) hz
        _ = (V i).ι y := he.symm
    refine ⟨z, hz, ?_⟩
    rw [hf]
    exact hy
  let i := Classical.arbitrary ι
  obtain ⟨zi, hzi, _⟩ := hpoint i
  obtain ⟨k, hk⟩ := hcover (q i (pullback.fst (V i).ι (π i) zi))
  obtain ⟨zk, hzk, hnot⟩ := hpoint k
  obtain ⟨e, heM, heX, _⟩ :=
    exists_pullback_domainIso_of_common_closedGraphs pY pM pX π hπ V q hq
      j g a ha hag i k
  have hez : e.hom zi = zk := by
    apply (pullback.snd (V k).ι (π k)).isOpenEmbedding.injective
    calc
      pullback.snd (V k).ι (π k) (e.hom zi) =
          pullback.snd (V i).ι (π i) zi :=
        congrArg (fun f : pullback (V i).ι (π i) ⟶ M ↦ f zi) heM
      _ = x := hzi
      _ = pullback.snd (V k).ι (π k) zk := hzk.symm
  have heval := congrArg (fun f : pullback (V i).ι (π i) ⟶ X ↦ f zi) heX
  change q k (pullback.fst (V k).ι (π k) (e.hom zi)) =
    q i (pullback.fst (V i).ι (π i) zi) at heval
  rw [hez] at heval
  apply hnot
  rw [heval]
  exact hk

end AlgebraicGeometry.Scheme.Compactification
