/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Dimension of an original irreducible closed subspace

The original subtype map identifies irreducible closed subsets of a closed
subspace Z with the irreducible closed subsets of the ambient space contained
in Z. For irreducible Z this is the principal lower order interval at Z, so
its dimension is the native order height of Z. A finite dimension witness
therefore has an irreducible closed witness of at least the same dimension.

No separation, sobriety, Noetherianity or catenarity hypothesis is used.
-/

@[expose] public noncomputable section

open Set Order Topology

universe u

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- An irreducible closed subset contained in Z remains irreducible in
the original subspace topology of Z. -/
theorem irreducible_preimage_subtype
    (Z A : IrreducibleCloseds X) (hA : A ≤ Z) :
    IsIrreducible ((Subtype.val : Z → X) ⁻¹' (A : Set X)) := by
  let : IrreducibleSpace A := Subtype.irreducibleSpace A.isIrreducible
  let g : A → Z := fun x => ⟨x.1, hA x.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk (fun x => hA x.2)
  have he : g '' Set.univ = (Subtype.val : Z → X) ⁻¹' (A : Set X) := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, trivial, rfl⟩
  exact he ▸ (IrreducibleSpace.isIrreducible_univ A).image g hg.continuousOn

/-- The original subtype image and preimage give the actual order
isomorphism between closed irreducibles in Z and those contained in Z. -/
def IrreducibleCloseds.orderIsoOfClosedSubspace (Z : IrreducibleCloseds X) :
    IrreducibleCloseds Z ≃o Set.Iic Z where
  toFun A := ⟨IrreducibleCloseds.map Subtype.val continuous_subtype_val A,
    Z.isClosed.closure_subset_iff.mpr (by
      rintro x ⟨y, _, rfl⟩
      exact y.2)⟩
  invFun A :=
    { carrier := (Subtype.val : Z → X) ⁻¹' (A.1 : Set X)
      isIrreducible' := irreducible_preimage_subtype Z A.1 A.2
      isClosed' := A.1.isClosed.preimage continuous_subtype_val }
  left_inv A := by
    apply SetLike.coe_injective
    change (Subtype.val : Z → X) ⁻¹' closure (Subtype.val '' (A : Set Z)) = (A : Set Z)
    have hi : IsInducing (Subtype.val : Z → X) := IsInducing.subtypeVal
    have h := hi.closure_eq_preimage_closure_image (A : Set Z)
    exact h.symm.trans A.isClosed.closure_eq
  right_inv A := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change closure (Subtype.val '' ((Subtype.val : Z → X) ⁻¹' (A.1 : Set X))) = (A.1 : Set X)
    have hsub : (A.1 : Set X) ⊆ Set.range (Subtype.val : Z → X) := by
      intro x hx
      exact ⟨⟨x, A.2 hx⟩, rfl⟩
    rw [Set.image_preimage_eq_of_subset hsub, A.1.isClosed.closure_eq]
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have hpre := Set.preimage_mono (f := (Subtype.val : Z → X)) h
      change (Subtype.val : Z → X) ⁻¹' closure (Subtype.val '' (A : Set Z)) ⊆
        (Subtype.val : Z → X) ⁻¹' closure (Subtype.val '' (B : Set Z)) at hpre
      have hi : IsInducing (Subtype.val : Z → X) := IsInducing.subtypeVal
      have hA := hi.closure_eq_preimage_closure_image (A : Set Z)
      have hB := hi.closure_eq_preimage_closure_image (B : Set Z)
      rwa [← hA, ← hB,
        A.isClosed.closure_eq, B.isClosed.closure_eq] at hpre
    · intro h
      exact IrreducibleCloseds.map_mono (f := (Subtype.val : Z → X)) continuous_subtype_val h

/-- The dimension of the original irreducible closed subspace is the
height of that same closed subset in the ambient irreducible-closed order. -/
theorem topologicalKrullDim_irreducibleClosed_eq_height (Z : IrreducibleCloseds X) :
    topologicalKrullDim Z = (Order.height Z : WithBot ℕ∞) := by
  exact (Order.krullDim_eq_of_orderIso (Z.orderIsoOfClosedSubspace)).trans
    (Order.height_eq_krullDim_Iic Z).symm

/-- A native finite chain witnessing ambient dimension supplies an
actual irreducible closed subspace with at least that dimension. -/
theorem exists_irreducibleClosed_topologicalKrullDim_ge (d : ℕ)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ Z : IrreducibleCloseds X, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp hd
  refine ⟨p.last, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed_eq_height]
  have h := Order.length_le_height_last (p := p)
  rw [hp] at h
  exact_mod_cast h

/-- A finite dimension witness in an actual closed subspace has an
irreducible closed witness in the ambient space, still contained in it. -/
theorem exists_irreducibleClosed_subset_topologicalKrullDim_ge
    (S : Set X) (hS : IsClosed S) (d : ℕ)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim S) :
    ∃ Z : IrreducibleCloseds X, (Z : Set X) ⊆ S ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  obtain ⟨A, hA⟩ := exists_irreducibleClosed_topologicalKrullDim_ge d hd
  let Z := IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val A
  have hclosed : IsClosed ((Subtype.val : S → X) '' (A : Set S)) :=
    hS.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
  have hZ : (Z : Set X) = (Subtype.val : S → X) '' (A : Set S) := hclosed.closure_eq
  let e := hS.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphImage (A : Set S)
  let eZ := Homeomorph.setCongr hZ
  have hdim : topologicalKrullDim Z = topologicalKrullDim A :=
    (IsHomeomorph.topologicalKrullDim_eq eZ eZ.isHomeomorph).trans
      (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
  refine ⟨Z, ?_, hA.trans_eq hdim.symm⟩
  rw [hZ]
  rintro x ⟨y, _, rfl⟩
  exact y.2

end TopologicalSpace
