/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.TargetOpenSeparated

/-!
# Eventual separatedness over a quasi-separated fixed target

Finitely many affine target opens are selected to cover the image of one
compact source stage. They need not cover the target. Their actual
restricted systems descend separatedness and are synchronized at one
source stage. Locality on the range of that structural morphism gives
separatedness globally. This is the varying-source assertion of Stacks
01ZH, distinct from base-change-family descent 01ZQ.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Separatedness of a limit morphism to a fixed quasi-separated scheme
is attained at a stage of a qcqs affine-transition source system.
The fixed target is not assumed compact. -/
lemma exists_isSeparated_app_of_isLimit_of_quasiSeparatedSpace
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (h : c.pt ⟶ S)
    (hcompat : ∀ j, c.π.app j ≫ t.app j = h)
    (i : I) [IsSeparated h] : ∃ j : Over i, IsSeparated (t.app j.left) := by
  classical
  let V (a : S.affineCover.I₀) := (S.affineCover.f a).opensRange
  have hcover : (Set.univ : Set (D.obj i)) ⊆ ⋃ a, (t.app i ⁻¹ᵁ V a : Set (D.obj i)) := by
    intro x _
    have hx : t.app i x ∈ ⨆ a, V a := by
      rw [S.affineCover.iSup_opensRange]
      trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set (D.obj i))).elim_finite_subcover
    (fun a ↦ (t.app i ⁻¹ᵁ V a : Set (D.obj i))) (fun a ↦ (t.app i ⁻¹ᵁ V a).isOpen) hcover
  have hselected (x : D.obj i) : ∃ a : s, t.app i x ∈ V a.1 := by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  choose j hj using fun a : s ↦ TargetOpenSystem.exists_isSeparated_stageMap
    D t i (V a.1) (isAffineOpen_opensRange (S.affineCover.f a.1)) c hc h hcompat
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (a : s) : l ⟶ j a :=
    (hl (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).some
  have hrestricted (a : s) : IsSeparated (t.app l.left ∣_ V a.1) := by
    have : IsSeparated ((TargetOpenSystem.structureMap D t i (V a.1)).app (j a)) := hj a
    have : IsSeparated (TargetOpenSystem.stageMap D t i (V a.1) l) :=
      isSeparated_app_of_affine_transition (opensDiagram D i (t.app i ⁻¹ᵁ V a.1))
        (TargetOpenSystem.structureMap D t i (V a.1)) (q a)
    exact TargetOpenSystem.isSeparated_restriction_of_stageMap D t i (V a.1) l
  let : MorphismProperty.RespectsRight (@IsSeparated) (@IsOpenImmersion) := {
    postcomp := fun g hg f hf ↦ by
      have := hg
      have := hf
      infer_instance }
  refine ⟨l, IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsSeparated)
    (fun a : s ↦ V a.1) ?_ hrestricted⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hselected (D.map l.hom x)
  apply Opens.mem_iSup.mpr
  refine ⟨a, ?_⟩
  have hnat : D.map l.hom ≫ t.app i = t.app l.left :=
    (t.naturality l.hom).trans (Category.comp_id _)
  change (D.map l.hom ≫ t.app i) x ∈ V a.1 at ha
  rwa [hnat] at ha

end AlgebraicGeometry.Scheme
