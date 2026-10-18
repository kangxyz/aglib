/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.IdealSheaf.FaithfullyFlat
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Precoverage
public import Aglib.AlgebraicGeometry.IdealSheaf.Glue
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Closed subschemes as an fpqc and fppf sheaf

Closed subschemes of a scheme `X` are ideal sheaves, Mathlib's `X.IdealSheafData`, with pullback
`IdealSheafData.comap`. This file packages them as a presheaf of types on schemes and proves that
it is a sheaf for the Zariski, fpqc and fppf topologies.

* `idealSheafPresheaf`: the presheaf `X ↦ X.IdealSheafData`, `f ↦ (·.comap f)`;
* `isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact`: it
  satisfies the sheaf condition for the singleton presieve of every flat, surjective and
  quasi-compact morphism (the descent theorem `existsUnique_comap_eq_of_flat_of_surjective` of
  [FaithfullyFlat](FaithfullyFlat.lean), Nitsure, arXiv:math/0504590v1, Lemma 6.7(2));
* `isSeparated_idealSheafPresheaf_zariskiTopology`: it is separated for the Zariski topology
  (`ext_of_comap_eq` of [Pullback](Pullback.lean));
* `isSheaf_idealSheafPresheaf_zariskiTopology`: it is a sheaf for the Zariski topology; ideal
  sheaves on the members of an open cover that agree on the overlaps glue
  (`IdealSheafData.glue`, `IdealSheafData.comap_glue` of
  [IdealSheaf/Glue](../../IdealSheaf/Glue.lean));
* `isSeparated_idealSheafPresheaf_fppfTopology`: it is separated for the fppf topology. A member
  `f i : X i ⟶ S` of an fppf covering family is open; it factors through its open image `V i` by a
  flat surjective morphism, along which `comap` is injective
  (`comap_injective_of_flat_of_surjective`, no quasi-compactness needed), and the `V i` cover
  `S`;
* `isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology`,
  `isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology`: if it is a sheaf for the
  Zariski topology, it is a sheaf for the fpqc and the fppf topology (Mathlib's
  `isSheaf_type_propQCTopology_iff`, Stacks Project, Tag 022H as cited there);
* `isSheaf_idealSheafPresheaf_fpqcTopology`, `isSheaf_idealSheafPresheaf_fppfTopology`: closed
  subschemes form an fpqc sheaf and an fppf sheaf, from the Zariski sheaf property and the
  `_of_isSheaf_zariskiTopology` pair above.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

/-- The presheaf of ideal sheaves (closed subschemes) on schemes: `X ↦ X.IdealSheafData`, with
the pullback maps `IdealSheafData.comap`. -/
@[simps]
def idealSheafPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop.IdealSheafData
  map f := TypeCat.ofHom fun I ↦ I.comap f.unop
  map_id _ := ConcreteCategory.hom_ext _ _ fun I ↦ I.comap_id
  map_comp f g := ConcreteCategory.hom_ext _ _ fun I ↦ I.comap_comp g.unop f.unop

/-- Closed subschemes satisfy the sheaf condition for the singleton presieve of a flat,
surjective and quasi-compact morphism. -/
theorem isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] :
    Presieve.IsSheafFor idealSheafPresheaf.{u} (Presieve.singleton f) := by
  rw [Presieve.isSheafFor_singleton]
  intro Z hZ
  exact IdealSheafData.existsUnique_comap_eq_of_flat_of_surjective f Z
    (hZ (pullback.fst f f) (pullback.snd f f) pullback.condition)

/-- Closed subschemes form a separated presheaf for the Zariski topology. -/
theorem isSeparated_idealSheafPresheaf_zariskiTopology :
    Presieve.IsSeparated Scheme.zariskiTopology idealSheafPresheaf.{u} := by
  intro X S hS x t₁ t₂ h₁ h₂
  obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hS
  have : ∀ j, IsOpenImmersion (𝒰.f j) := 𝒰.map_prop
  refine IdealSheafData.ext_of_comap_eq 𝒰.f
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨𝒰.idx x, 𝒰.covers x⟩) fun j ↦ ?_
  have e₁ := h₁ (𝒰.f j) (hle _ _ (Presieve.ofArrows.mk j))
  have e₂ := h₂ (𝒰.f j) (hle _ _ (Presieve.ofArrows.mk j))
  exact e₁.trans e₂.symm

/-- **Closed subschemes form a Zariski sheaf**: ideal sheaves on the members of an open cover that
agree on the overlaps come from a unique ideal sheaf (`IdealSheafData.glue` for existence,
`IdealSheafData.ext_of_comap_eq` for uniqueness). -/
theorem isSheaf_idealSheafPresheaf_zariskiTopology :
    Presieve.IsSheaf Scheme.zariskiTopology idealSheafPresheaf.{u} := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y R hR x hx
  obtain ⟨(𝒰 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hR
  have : ∀ j, IsOpenImmersion (𝒰.f j) := 𝒰.map_prop
  have hcov : ∀ y : Y, ∃ j z, 𝒰.f j z = y := fun y ↦ ⟨𝒰.idx y, 𝒰.covers y⟩
  let I : ∀ j, (𝒰.X j).IdealSheafData := fun j ↦ x (𝒰.f j) (.mk j)
  have hI : ∀ i j, (I i).comap (pullback.fst (𝒰.f i) (𝒰.f j)) =
      (I j).comap (pullback.snd (𝒰.f i) (𝒰.f j)) := fun i j ↦
    hx (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j)) (.mk i) (.mk j)
      pullback.condition
  have hglue : ∀ j, (IdealSheafData.glue 𝒰.f I hcov hI).comap (𝒰.f j) = I j :=
    IdealSheafData.comap_glue hcov hI
  refine ⟨IdealSheafData.glue 𝒰.f I hcov hI, ?_, fun J hJ ↦ ?_⟩
  · rintro _ _ ⟨j⟩
    exact hglue j
  · refine IdealSheafData.ext_of_comap_eq 𝒰.f
      (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩) fun j ↦ ?_
    exact (hJ (𝒰.f j) (.mk j)).trans (hglue j).symm

-- Mathlib's instance `HasOfPostcompProperty` for a variable `P` applies at `P := @Flat` only when
-- types are compared without the transparency restriction (as in Mathlib's `Sites/Fpqc.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- Closed subschemes form a separated presheaf for the fppf topology: ideal sheaves with equal
pullbacks along the members of an fppf covering sieve are equal. -/
theorem isSeparated_idealSheafPresheaf_fppfTopology :
    Presieve.IsSeparated Scheme.fppfTopology idealSheafPresheaf.{u} := by
  intro S R hR x t₁ t₂ h₁ h₂
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨R₀, hR₀, hle⟩ := hR
  obtain ⟨ι, X, f, rfl⟩ := R₀.exists_eq_ofArrows
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hR₀
  obtain ⟨hsurj, hP⟩ := hR₀
  have heq : ∀ i, t₁.comap (f i) = t₂.comap (f i) := fun i ↦
    (h₁ (f i) (hle _ _ (Presieve.ofArrows.mk i))).trans
      (h₂ (f i) (hle _ _ (Presieve.ofArrows.mk i))).symm
  have hopen : ∀ i, IsOpen (Set.range (f i)) := fun i ↦ by
    have : Flat (f i) := (hP i).1
    have : LocallyOfFinitePresentation (f i) := (hP i).2
    exact (f i).isOpenMap.isOpen_range
  let V : ι → S.Opens := fun i ↦ ⟨Set.range (f i), hopen i⟩
  have hV : ∀ i, Set.range (f i) ⊆ Set.range (V i).ι := fun i ↦ by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let g : ∀ i, X i ⟶ (V i).toScheme := fun i ↦ IsOpenImmersion.lift (V i).ι (f i) (hV i)
  have hg : ∀ i, g i ≫ (V i).ι = f i := fun i ↦ IsOpenImmersion.lift_fac _ _ _
  have hflat : ∀ i, Flat (g i) := fun i ↦
    MorphismProperty.of_postcomp (W' := @IsOpenImmersion) @Flat (g i) (V i).ι
      (show IsOpenImmersion (V i).ι from inferInstance) (by rw [hg i]; exact (hP i).1)
  have hsurjg : ∀ i, Surjective (g i) := fun i ↦ ⟨fun y ↦ by
    obtain ⟨x, hx⟩ : (V i).ι y ∈ Set.range (f i) := by
      have h : (V i).ι y ∈ Set.range (V i).ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι] at h
    refine ⟨x, (V i).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg i, hx]⟩
  have hcomap : ∀ i, t₁.comap (V i).ι = t₂.comap (V i).ι := fun i ↦ by
    apply IdealSheafData.comap_injective_of_flat_of_surjective (g i)
    simp only
    rw [← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp, hg i]
    exact heq i
  refine IdealSheafData.ext_of_comap_eq (fun i ↦ (V i).ι)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ?_) hcomap
  obtain ⟨i, hi⟩ := hsurj y
  exact ⟨i, by rw [Scheme.Opens.range_ι]; exact hi⟩

-- Mathlib's instances for `IsZariskiLocalAtSource P` and the like, stated for a variable `P`, apply
-- at `P := @Flat` only when types are compared without the transparency restriction, as in
-- Mathlib's own use of `isSheaf_type_propQCTopology_iff` (`Sites/Fpqc.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- **Closed subschemes form an fpqc sheaf**, given that they form a Zariski sheaf. -/
theorem isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology
    (hZar : Presieve.IsSheaf Scheme.zariskiTopology idealSheafPresheaf.{u}) :
    Presieve.IsSheaf Scheme.fpqcTopology idealSheafPresheaf.{u} :=
  (isSheaf_type_propQCTopology_iff (P := @Flat) _).2 ⟨hZar, fun {_ _} f hf hs ↦
    have : Flat (Spec.map f) := hf
    have : Surjective (Spec.map f) := hs
    isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact (Spec.map f)⟩

/-- **Closed subschemes form an fppf sheaf**, given that they form a Zariski sheaf. -/
theorem isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology
    (hZar : Presieve.IsSheaf Scheme.zariskiTopology idealSheafPresheaf.{u}) :
    Presieve.IsSheaf Scheme.fppfTopology idealSheafPresheaf.{u} :=
  Presieve.isSheaf_of_le _ fppfTopology_le_fpqcTopology
    (isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology hZar)

/-- **Closed subschemes form an fpqc sheaf.** -/
theorem isSheaf_idealSheafPresheaf_fpqcTopology :
    Presieve.IsSheaf Scheme.fpqcTopology idealSheafPresheaf.{u} :=
  isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology
    isSheaf_idealSheafPresheaf_zariskiTopology

/-- **Closed subschemes form an fppf sheaf.** -/
theorem isSheaf_idealSheafPresheaf_fppfTopology :
    Presieve.IsSheaf Scheme.fppfTopology idealSheafPresheaf.{u} :=
  isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology
    isSheaf_idealSheafPresheaf_zariskiTopology

end AlgebraicGeometry.Scheme
