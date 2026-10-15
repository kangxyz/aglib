/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Filtered colimits of sheaves on Noetherian spaces

Pointwise filtered colimits are sheaves on Noetherian spaces. The forgetful functor
preserves these colimits, and sectionwise epimorphisms pass to filtered colimits.
The indexing categories are small in universe u; the coefficient groups are in
universe u. No cohomology/colimit comparison is assumed.

Source: `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Filtered-colimit and sectionwise-epimorphism
  declarations only.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite TopCat
namespace TopCat.Sheaf
universe u

/-- Every open family on a Noetherian space has a finite subfamily with the same union. -/
lemma exists_finite_opens_subcover {X : TopCat.{u}} [NoetherianSpace X]
    {ι : Type u} (U : ι → Opens X) :
    ∃ t : Finset ι, (iSup fun i : t => U i) = iSup U := by
  classical
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (↑(iSup U) : Set X)).elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) (by simp)
  refine ⟨t, le_antisymm (iSup_le fun i => le_iSup U i) ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

variable {X : TopCat.{u}} (F : X.Presheaf (Type u))

/-- Finite compatible gluing suffices for the full sheaf condition on a Noetherian space. -/
lemma isSheaf_of_finite_gluing [NoetherianSpace X]
    (hfin : ∀ {ι : Type u} [Finite ι] (U : ι → Opens X)
      (V : Opens X) (iUV : ∀ i, U i ⟶ V) (_hcover : V ≤ iSup U)
      (sf : ∀ i, F.obj (op (U i))), F.IsCompatible U sf →
      ∃! s : F.obj (op V), ∀ i, F.map (iUV i).op s = sf i) : F.IsSheaf := by
  classical
  have hext : ∀ {ι : Type u} [Finite ι] (U : ι → Opens X)
      (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
      (s t : F.obj (op V)),
      (∀ i, F.map (iUV i).op s = F.map (iUV i).op t) → s = t := by
    intro ι _ U V iUV hcover s t hst
    let sf := fun i => F.map (iUV i).op s
    have hcpt : F.IsCompatible U sf := by
      intro i j
      dsimp [sf]
      simp only [← Functor.map_comp_apply]
      congr 1
    obtain ⟨z, hz, huniq⟩ := hfin U V iUV hcover sf hcpt
    exact (huniq s (fun _ => rfl)).trans (huniq t (fun i => (hst i).symm)).symm
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro ι U sf hcpt
  obtain ⟨t, ht⟩ := exists_finite_opens_subcover U
  let Ut : t → Opens X := fun i => U i
  have hcov : iSup U ≤ iSup Ut := ht.ge
  obtain ⟨s, hs, huniq⟩ := hfin Ut (iSup U) (fun i => Opens.leSupr U i)
    hcov (fun i => sf i) (fun i j => hcpt i j)
  refine ⟨s, ?_, ?_⟩
  · intro i
    let W : t → Opens X := fun j => U j ⊓ U i
    have hW : U i ≤ iSup W := by
      intro x hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov (Opens.mem_iSup.mpr ⟨i, hx⟩))
      exact Opens.mem_iSup.mpr ⟨j, hj, hx⟩
    apply hext W (U i) (fun j => homOfLE inf_le_right) hW
    intro j
    change F.map (homOfLE inf_le_right).op (F.map (Opens.leSupr U i).op s) = _
    rw [← Functor.map_comp_apply]
    have hh := congrArg (F.map (homOfLE (inf_le_left : W j ≤ U j)).op) (hs j)
    rw [← Functor.map_comp_apply] at hh
    exact hh.trans (hcpt j i)
  · intro s' hs'
    exact huniq s' (fun j => hs' j)

/-- Finite pairwise-cover limits detect the sheaf condition on a Noetherian space. -/
lemma isSheaf_of_preserves_finite_pairwise [NoetherianSpace X]
    (hfin : ∀ {ι : Type u} [Finite ι] (U : ι → Opens X),
      PreservesLimit (Pairwise.diagram U).op F) : F.IsSheaf := by
  apply isSheaf_of_finite_gluing F
  intro ι _ U V iUV hcover sf hcpt
  let := hfin U
  have hg : ∃! s : F.obj (op (iSup U)), F.IsGluing U sf s := by
    simp_rw [TopCat.Presheaf.isGluing_iff_pairwise]
    exact (Types.isLimit_iff _).mp
      ⟨isLimitOfPreserves F (Pairwise.coconeIsColimit U).op⟩
      _ hcpt.sectionPairwise.prop
  have hV : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨s, hs, huniq⟩ := hg
  refine ⟨F.map (eqToHom hV).op s, ?_, ?_⟩
  · intro i
    rw [← Functor.map_comp_apply]
    exact hs i
  · intro s' hs'
    have heq : F.map (eqToHom hV.symm).op s' = s := by
      apply huniq
      intro i
      rw [← Functor.map_comp_apply]
      exact hs' i
    have h := congrArg (F.map (eqToHom hV).op) heq
    simpa only [← Functor.map_comp_apply, eqToHom_op, eqToHom_trans,
      eqToHom_refl, F.map_id, types_id_apply] using h

/-- The pointwise filtered colimit of sheaves of types is a sheaf on a Noetherian space. -/
lemma filtered_pointwiseColimit_isSheaf [NoetherianSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ (Opens X)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, TopCat.Presheaf.IsSheaf (X := X) (D.obj i)) :
    TopCat.Presheaf.IsSheaf (X := X) (D.flip ⋙ colim) := by
  apply isSheaf_of_preserves_finite_pairwise
  intro ι _ U
  classical
  let := Fintype.ofFinite ι
  let : PreservesLimit (Pairwise.diagram U).op D.flip :=
    preservesLimit_of_evaluation _ _ fun i =>
      (hD i).isSheafPreservesLimitPairwiseIntersections U
  infer_instance

/-- The pointwise filtered colimit of abelian sheaves is a sheaf on a Noetherian space. -/
lemma filtered_additive_pointwiseColimit_isSheaf [NoetherianSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hD : ∀ i, TopCat.Presheaf.IsSheaf (X := X) (D.obj i)) :
    TopCat.Presheaf.IsSheaf (X := X) (D.flip ⋙ colim) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (CategoryTheory.forget AddCommGrpCat.{u}) _).mpr
  apply isSheaf_of_preserves_finite_pairwise
  intro ι _ U
  classical
  let := Fintype.ofFinite ι
  let : PreservesLimit (Pairwise.diagram U).op D.flip :=
    preservesLimit_of_evaluation _ _ fun i =>
      (hD i).isSheafPreservesLimitPairwiseIntersections U
  infer_instance

/-- Actual abelian-sheaf filtered colimits on a Noetherian space are computed on opens. -/
instance noetherian_sheafToPresheaf_preservesColimitsOfShape [NoetherianSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) where
  preservesColimit {D} := by
    suffices CreatesColimit D (sheafToPresheaf _ _) from inferInstance
    refine CategoryTheory.Sheaf.createsColimitOfIsSheaf _ (fun c hc => ?_)
    let e : c.pt ≅ (D ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [CategoryTheory.Presheaf.isSheaf_of_iso_iff e]
    exact filtered_additive_pointwiseColimit_isSheaf _ (fun i => (D.obj i).property)

end TopCat.Sheaf

namespace TopCat.Sheaf
universe u
variable {X : TopCat.{u}}

lemma colimit_map_sections_epi [NoetherianSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {D E : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : D ⟶ E) (U : Opens X)
    [∀ i, Epi ((φ.app i).hom.app (op U))] :
    Epi ((colim.map φ).hom.app (op U)) := by
  let Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
  have : PreservesColimitsOfShape I Γ := by
    change PreservesColimitsOfShape I
      (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U))
    infer_instance
  have : ∀ i, Epi ((Functor.whiskerRight φ Γ).app i) := fun i =>
    inferInstanceAs (Epi ((φ.app i).hom.app (op U)))
  have : Epi (Functor.whiskerRight φ Γ) := NatTrans.epi_of_epi_app _
  have : Epi (colim.map (Functor.whiskerRight φ Γ)) :=
    Functor.map_epi colim (Functor.whiskerRight φ Γ)
  let e := preservesColimitNatIso (J := I) Γ
  have h : Epi (Γ.map (colim.map φ) ≫ e.hom.app E) := by
    change Epi ((colim ⋙ Γ).map φ ≫ e.hom.app E)
    rw [e.hom.naturality φ]
    change Epi (e.hom.app D ≫ colim.map (Functor.whiskerRight φ Γ))
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp h

end TopCat.Sheaf
