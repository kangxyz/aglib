/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Limits

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeFiniteCoverInduction.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256: `fa0bd7ed0040404c3e091735082619a2a3bc7273caec266734ff959b53b854e0`.
Selected declaration ranges: [[1, 113]].
Actual maps and premises are preserved; the generic truncation lift is recorded explicitly.
-/

/-! # Affine induction for scheme properties

An isomorphism-invariant scheme property with its affine case and compact
binary-open-union closure follows on qcqs schemes. The overlap property is an
explicit input to union closure; the induction does not establish that input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.AffineInduction

variable (P : Scheme.{u} → Prop)
  (hIso : ∀ {X Y : Scheme.{u}} (_e : X ≅ Y), P X → P Y)
  (hAffine : ∀ (X : Scheme.{u}) [IsAffine X], P X)
  (hUnion : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (U V : X.Opens),
    IsCompact (U : Set X) → IsCompact (V : Set X) →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P (U ⊔ V).toScheme)

private lemma compact_finiteAffineUnion {X : Scheme.{u}} (s : Finset X.affineOpens) :
    IsCompact ((s.sup (fun V => V.val) : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert V s hV ih =>
    rw [Finset.sup_insert]
    exact V.property.isCompact.union ih

include hAffine hUnion in
/-- Intersections with one affine chart do not increase the finite cover size
when the ambient scheme is separated. -/
lemma of_finiteAffineUnion_of_separated {X : Scheme.{u}} [X.IsSeparated]
    (s : Finset X.affineOpens) : P (s.sup (fun V => V.val)).toScheme := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hz : s = ∅
    · subst s
      simp only [Finset.sup_empty]
      exact @hAffine _ (isAffineOpen_bot X)
    obtain ⟨V, hV⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    let t := s.erase V
    have hcard : t.card < n := by
      have hc : t.card + 1 = s.card := Finset.card_erase_add_one hV
      omega
    let W := t.sup (fun A => A.val)
    have hW : P W.toScheme := ih t.card hcard t rfl
    let t' : Finset X.affineOpens :=
      t.image (fun A => ⟨A.val ⊓ V.val, A.property.inf V.property⟩)
    have ht' : t'.sup (fun A => A.val) = W ⊓ V.val := by
      rw [Finset.sup_image]
      exact (Finset.sup_inf_distrib_right t (fun A => A.val) V.val).symm
    have hi : P (W ⊓ V.val).toScheme := by
      rw [← ht']
      exact ih t'.card (lt_of_le_of_lt Finset.card_image_le hcard) t' rfl
    have h := hUnion W V.val (compact_finiteAffineUnion t) V.property.isCompact
      hW (hAffine V.val.toScheme) hi
    have hs : insert V t = s := Finset.insert_erase hV
    have he : W ⊔ V.val = s.sup (fun A => A.val) := by
      rw [← hs, Finset.sup_insert, sup_comm]
    rwa [he] at h

include hAffine hUnion in
/-- Every compact open of a separated scheme satisfies the property. -/
lemma of_compactOpen_of_separated {X : Scheme.{u}} [X.IsSeparated]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : P U.toScheme := by
  classical
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have he : hs.toFinset.sup (fun V => V.val) = U := by
    simpa only [Finset.sup_eq_iSup, Set.Finite.mem_toFinset] using hcover.symm
  rw [← he]
  exact of_finiteAffineUnion_of_separated P hAffine hUnion hs.toFinset

include hIso hAffine hUnion in
/-- Qcqs induction uses the assumed property on each compact overlap,
which is a compact open inside an affine scheme. -/
lemma of_compactOpen {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : P U.toScheme := by
  refine compact_open_induction_on U hU ?_ ?_
  · exact @hAffine _ (isAffineOpen_bot X)
  · intro S hS V ih
    let : IsAffine V.val.toScheme := V.property
    let : CompactSpace V.val.toScheme := isCompact_iff_compactSpace.mp V.property.isCompact
    have hi : P (V.val.ι ⁻¹ᵁ S).toScheme :=
      of_compactOpen_of_separated P hAffine hUnion _ (V.val.ι.isCompact_preimage hS)
    let e : (V.val.ι ⁻¹ᵁ S).toScheme ≅ (S ⊓ V.val).toScheme :=
      V.val.ι.isoImage _ ≪≫ X.isoOfEq (by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm])
    exact hUnion S V.val hS V.property.isCompact ih (hAffine _) (hIso e hi)

include hIso hAffine hUnion in
/-- The affine case and actual compact binary-union closure imply the full
qcqs conclusion. -/
lemma of_qcqs (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : P X :=
  hIso X.topIso (of_compactOpen P hIso hAffine hUnion ⊤ isCompact_univ)

end AlgebraicGeometry.Scheme.AffineInduction
