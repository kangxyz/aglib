/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualClosedOverlap
public import Aglib.AlgebraicGeometry.Descent.FiniteType.OverlapLocality

/-!
# Eventual separatedness over a fixed affine target

A finite affine cover of one compact source stage gives finitely many
chart pairs. Their eventual closed overlap arrows are synchronized in
the actual over category. The inverse-image cover at that common stage
and the native diagonal-product cover give separatedness by locality.
This is varying-source descent, not the base-change-family theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Separatedness over a fixed base persists along an affine transition
by composition, independently of any diagonal transition square. -/
lemma isSeparated_app_of_affine_transition
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
    {j k : I} (q : j ⟶ k) [IsAffineHom (D.map q)] [IsSeparated (t.app k)] :
    IsSeparated (t.app j) := by
  have heq : D.map q ≫ t.app k = t.app j := by
    exact (t.naturality q).trans (Category.comp_id _)
  rw [← heq]
  infer_instance

/-- A separated limit over an affine fixed target descends to an actual
stage of the varying source system. Compactness is required only at the
specified initial stage; source stages need not be affine. -/
lemma exists_isSeparated_app_of_isLimit_of_isAffine_target
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (h : c.pt ⟶ S)
    (hcompat : ∀ j, c.π.app j ≫ t.app j = h)
    (i : I) [CompactSpace (D.obj i)] [IsSeparated h] :
    ∃ j : Over i, IsSeparated (t.app j.left) := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let U (a : 𝒰.I₀) := (𝒰.f a).opensRange
  have hU (a : 𝒰.I₀) : IsAffineOpen (U a) := isAffineOpen_opensRange (𝒰.f a)
  choose j hj using fun ab : 𝒰.I₀ × 𝒰.I₀ ↦
    RelativeOverlap.exists_eventually_isClosedImmersion_overlapMap
      D t c hc h hcompat i (U ab.1) (U ab.2) (hU ab.1) (hU ab.2)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (ab : 𝒰.I₀ × 𝒰.I₀) : l ⟶ j ab :=
    (hl (Finset.mem_image.mpr ⟨ab, Finset.mem_univ _, rfl⟩)).some
  refine ⟨l, RelativeOverlap.isSeparated_of_overlap_cover (t.app l.left)
    (fun a ↦ D.map l.hom ⁻¹ᵁ U a) ?_ ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange]
    simp
  · intro a b
    exact hj (a, b) l (q (a, b))

end AlgebraicGeometry.Scheme
