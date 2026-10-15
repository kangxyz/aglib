/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.MayerVietorisSections
public import Aglib.Algebra.Homology.MappingCone.QuasiIso
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
/-!
# Exactness detected by original sections on a topological basis

If the original section short complexes are exact on every member of a basis,
the sheaf short complex is exact. The proof represents a stalk cycle by a
section, shrinks within the basis until its differential vanishes, and then
uses actual section exactness. This gives arbitrary-shape acyclicity detection
and a mapping-cone criterion for original cochain quasi-isomorphisms. There is
no assertion that section evaluation preserves arbitrary exact sequences, and
no boundedness, flasqueness or finiteness premise.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf
universe u
namespace TopCat.Sheaf
variable {X : TopCat.{u}}

lemma exact_of_sections_on_basis (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hS : ∀ U ∈ B, (S.map (sectionsFunctor U)).Exact) : S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, hU, t, rfl⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB S.X₂.obj x z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (TopCat.Presheaf.germ S.X₂.obj U x hxU t) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have he : TopCat.Presheaf.germ S.X₃.obj U x hxU (S.g.hom.app (op U) t) =
      TopCat.Presheaf.germ S.X₃.obj U x hxU 0 := by simpa using hz
  obtain ⟨V, hxV, hV, hVU, _, hv⟩ :=
    TopCat.Presheaf.germ_eq_of_isBasis hB S.X₃.obj x hxU hxU he
  let tV := S.X₂.obj.map (homOfLE hVU).op t
  have htV : S.g.hom.app (op V) tV = 0 := by
    change S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hVU).op t) = 0
    rw [S.g.hom.naturality_apply]
    simpa using hv
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).mp (hS V hV) tV htV
  change S.f.hom.app (op V) a = tV at ha
  refine ⟨TopCat.Presheaf.germ S.X₁.obj V x hxV a, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (TopCat.Presheaf.germ S.X₁.obj V x hxV a) = TopCat.Presheaf.germ S.X₂.obj U x hxU t
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ S.X₂.obj V x hxV (S.f.hom.app (op V) a) = _
  rw [ha]
  exact TopCat.Presheaf.germ_res_apply S.X₂.obj (homOfLE hVU) x hxV t

lemma exactAt_of_sections_on_basis {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (TopCat.Sheaf AddCommGrpCat.{u} X) c) (n : ι)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B, (((sectionsFunctor U).mapHomologicalComplex c).obj K).ExactAt n) :
    K.ExactAt n := by
  apply exact_of_sections_on_basis (K.sc n) hB
  intro U hU
  exact hK U hU

lemma acyclic_of_sections_on_basis {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (TopCat.Sheaf AddCommGrpCat.{u} X) c)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B, (((sectionsFunctor U).mapHomologicalComplex c).obj K).Acyclic) :
    K.Acyclic := fun n => exactAt_of_sections_on_basis K n hB (fun U hU => hK U hU n)

lemma quasiIso_of_sections_on_basis
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso
      (((sectionsFunctor U).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  apply acyclic_of_sections_on_basis _ hB
  intro U hU
  let F := (sectionsFunctor (A := AddCommGrpCat.{u}) U).mapHomologicalComplex (.up ℤ)
  have hfc : (CochainComplex.mappingCone (F.map f)).Acyclic := by
    let P := HomotopyCategory.subcategoryAcyclic AddCommGrpCat.{u}
    have hs : P.trW ((HomotopyCategory.quotient AddCommGrpCat (.up ℤ)).map (F.map f)) := by
      rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (hf U hU)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      ((P.trW_iff_of_distinguished (CochainComplex.mappingCone.triangleh (F.map f))
        (HomotopyCategory.mappingCone_triangleh_distinguished (F.map f))).1 hs)
  intro n
  exact (hfc n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (sectionsFunctor U)).symm
end TopCat.Sheaf
