/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantFiniteGenerators
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Local lifting from finite projective constant modules

Finitely many generators give one covering sieve on which the original section
map lands in the actual image of an epimorphism. Projectivity lifts through that
image. The original section-to-slice constructor then gives a lift of the whole
restricted sheaf morphism, retaining its original constant unit equation.
Projectivity belongs to the specified source module; finite modules over a
composite ZMod ring are not asserted to satisfy it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace ModuleCat.Presheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ]

/-- A map from a finite projective module lifts locally through the original section map. -/
theorem exists_cover_projective_lift {F G : Cᵒᵖ ⥤ ModuleCat.{m} Λ} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    (M : ModuleCat.{m} Λ) [Module.Finite Λ M] [Module.Projective Λ M]
    {U : C} (g : M ⟶ G.obj (op U)) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ a : M ⟶ F.obj (op V), a ≫ η.app (op V) = g ≫ G.map f.op := by
  obtain ⟨T, hT, h⟩ := exists_cover_finite_span_lifts J η M g
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨P, _, hP⟩ := h f hf
  let p := (η.app (op V)).hom
  let q := (G.map f.op).hom.comp g.hom
  have hq (x : M) : q x ∈ LinearMap.range p := by
    obtain ⟨y, hy⟩ := hP x
    exact ⟨y, hy⟩
  let q' := q.codRestrict (LinearMap.range p) hq
  obtain ⟨a, ha⟩ := Module.projective_lifting_property p.rangeRestrict q'
    p.surjective_rangeRestrict
  refine ⟨ModuleCat.ofHom a, ?_⟩
  ext x
  exact congrArg Subtype.val (LinearMap.congr_fun ha x)

end ModuleCat.Presheaf

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ]

attribute [local instance] hasSheafify

set_option backward.isDefEq.respectTransparency false in
/-- The lift is an equality of the original morphisms on the entire actual slice. -/
theorem exists_cover_constant_projective_lift
    {F G : Sheaf J (ModuleCat.{max c h} Λ)} (p : F ⟶ G) [Epi p]
    (M : ModuleCat.{max c h} Λ) [Module.Finite Λ M] [Module.Projective Λ M]
    (φ : (constantSheaf J (ModuleCat.{max c h} Λ)).obj M ⟶ G) (U : C) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ a : (constantSheaf (J.over V) (ModuleCat.{max c h} Λ)).obj M ⟶
          (J.overPullback (ModuleCat.{max c h} Λ) V).obj F,
        a ≫ (J.overPullback (ModuleCat.{max c h} Λ) V).map p =
          constantOverMap J V M ≫ (J.overPullback (ModuleCat.{max c h} Λ) V).map φ := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max c h} Λ)) :=
    forget_preservesFilteredColimits Λ
  let : J.PreservesSheafification (forget (ModuleCat.{max c h} Λ)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max c h} Λ))
  let : CategoryTheory.Sheaf.IsLocallySurjective p :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max c h} Λ) p).mpr
      inferInstance
  obtain ⟨T, hT, h⟩ := ModuleCat.Presheaf.exists_cover_projective_lift J p.hom M
    ((constantUnit J M).app (op U) ≫ φ.hom.app (op U))
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨a, ha⟩ := h f hf
  have ha' : a ≫ p.hom.app (op V) = (constantUnit J M).app (op V) ≫
      φ.hom.app (op V) := by
    rw [ha, Category.assoc, ← φ.hom.naturality, ← Category.assoc,
      ← (constantUnit J M).naturality]
    change (𝟙 M ≫ (constantUnit J M).app (op V)) ≫ φ.hom.app (op V) = _
    rw [Category.id_comp]
  refine ⟨sectionToSlice J V F M a, ?_⟩
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (J.over V) _ _
    ((J.overPullback (ModuleCat.{max c h} Λ) V).obj G).property
  apply NatTrans.ext
  funext W
  change (constantUnit (J.over V) M).app W ≫
      (sectionToSlice J V F M a).hom.app W ≫ p.hom.app (op W.unop.left) =
    (constantUnit (J.over V) M).app W ≫ (constantOverMap J V M).hom.app W ≫
      φ.hom.app (op W.unop.left)
  rw [← Category.assoc, sectionToSlice_unit, Category.assoc, p.hom.naturality,
    ← Category.assoc, ha', Category.assoc, ← φ.hom.naturality, ← Category.assoc,
    ← (constantUnit J M).naturality]
  have hu : (constantUnit (J.over V) M).app W ≫ (constantOverMap J V M).hom.app W =
      (constantUnit J M).app (op W.unop.left) :=
    congrArg (fun α => α.app W) (constantOverMap_unit J V M)
  change (𝟙 M ≫ (constantUnit J M).app (op W.unop.left)) ≫
      φ.hom.app (op W.unop.left) = _
  rw [Category.id_comp, ← Category.assoc, hu]

/-- Closed finite-projective section maps in an exact sheaf complex are locally boundaries. -/
theorem exists_cover_projective_boundary
    (S : ShortComplex (Sheaf J (ModuleCat.{max c h} Λ))) (hS : S.Exact)
    (M : ModuleCat.{max c h} Λ) [Module.Finite Λ M] [Module.Projective Λ M]
    {U : C} (g : M ⟶ S.X₂.obj.obj (op U))
    (hg : g ≫ S.g.hom.app (op U) = 0) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ a : M ⟶ S.X₁.obj.obj (op V), a ≫ S.f.hom.app (op V) =
        g ≫ S.X₂.obj.map f.op := by
  let E := (sheafSections J (ModuleCat.{max c h} Λ)).obj (op U)
  let : PreservesFiniteLimits E := by
    change PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{max c h} Λ) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{max c h} Λ)).obj (op U))
    infer_instance
  have hker := KernelFork.mapIsLimit _ S.cyclesIsKernel E
  obtain ⟨g', hg'⟩ := KernelFork.IsLimit.lift' hker g hg
  change g' ≫ S.iCycles.hom.app (op U) = g at hg'
  let : PreservesFilteredColimits (forget (ModuleCat.{max c h} Λ)) :=
    forget_preservesFilteredColimits Λ
  let : J.PreservesSheafification (forget (ModuleCat.{max c h} Λ)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max c h} Λ))
  let : Epi S.toCycles := hS.epi_toCycles
  let : CategoryTheory.Sheaf.IsLocallySurjective S.toCycles :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      (ModuleCat.{max c h} Λ) S.toCycles).mpr inferInstance
  obtain ⟨T, hT, h⟩ := ModuleCat.Presheaf.exists_cover_projective_lift J S.toCycles.hom M g'
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨a, ha⟩ := h f hf
  refine ⟨a, ?_⟩
  have hd : S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V) =
      S.f.hom.app (op V) := congrArg (fun k => k.hom.app (op V)) S.toCycles_i
  rw [← hd, ← Category.assoc, ha, Category.assoc, S.iCycles.hom.naturality,
    ← Category.assoc, hg']

/-- The same local lifting uses the original differentials of an arbitrary-shape complex. -/
theorem exists_cover_projective_boundary_of_exactAt {ι : Type*} {s : ComplexShape ι}
    (K : HomologicalComplex (Sheaf J (ModuleCat.{max c h} Λ)) s) (i : ι)
    (hK : K.ExactAt i) (M : ModuleCat.{max c h} Λ)
    [Module.Finite Λ M] [Module.Projective Λ M]
    {U : C} (g : M ⟶ (K.X i).obj.obj (op U))
    (hg : g ≫ (K.d i (s.next i)).hom.app (op U) = 0) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ a : M ⟶ (K.X (s.prev i)).obj.obj (op V),
        a ≫ (K.d (s.prev i) i).hom.app (op V) = g ≫ (K.X i).obj.map f.op :=
  exists_cover_projective_boundary J (K.sc i) hK M g hg

end ModuleCat.Sheaf
