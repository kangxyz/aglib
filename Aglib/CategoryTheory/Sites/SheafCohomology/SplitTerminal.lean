/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ProjectiveInt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! # Exact sections when covers of a terminal object split -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SheafCohomology.SplitTerminal

universe u₁ v₁ v w

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (T : C)

/-- A covering sieve containing a split arrow is maximal. This hypothesis is
required only at the specified object. -/
theorem covering_sieve_eq_top_of_split
    (h : ∀ (S : Sieve T), S ∈ J T →
      ∃ (U : C) (f : U ⟶ T) (s : T ⟶ U), S f ∧ s ≫ f = 𝟙 T)
    (S : Sieve T) (hS : S ∈ J T) : S = ⊤ := by
  obtain ⟨U, f, s, hf, hs⟩ := h S hS
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [hs] using S.downward_closed hf s

private abbrev localImage {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    Subfunctor (G.obj ⋙ forget AddCommGrpCat.{v}) :=
  (Subfunctor.range (Functor.whiskerRight f.hom (forget AddCommGrpCat.{v}))).sheafify J

private def localImageGroup {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : Cᵒᵖ) :
    AddSubgroup (G.obj.obj U) where
  carrier := (localImage J f).obj U
  zero_mem' := by
    change Presheaf.imageSieve f.hom (0 : G.obj.obj U) ∈ J U.unop
    have hz := Presheaf.imageSieve_app f.hom (0 : F.obj.obj U)
    rw [map_zero] at hz
    rw [hz]
    exact J.top_mem _
  add_mem' := by
    intro x y hx hy
    change Presheaf.imageSieve f.hom x ∈ J U.unop at hx
    change Presheaf.imageSieve f.hom y ∈ J U.unop at hy
    change Presheaf.imageSieve f.hom (x + y) ∈ J U.unop
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    intro V i hi
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hi
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  neg_mem' := by
    intro x hx
    change Presheaf.imageSieve f.hom x ∈ J U.unop at hx
    change Presheaf.imageSieve f.hom (-x) ∈ J U.unop
    refine J.superset_covering ?_ hx
    intro V i hi
    obtain ⟨a, ha⟩ := hi
    exact ⟨-a, by rw [map_neg, map_neg, ha]⟩

private def localImagePresheaf {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj U := .of (localImageGroup J f U)
  map g := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨G.obj.map g x.val, (localImage J f).map g x.property⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _ }
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom (G.obj.map_id U) x.val
  map_comp g h := by
    ext x
    exact ConcreteCategory.congr_hom (G.obj.map_comp g h) x.val

private def localImageSheaf {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    Sheaf J AddCommGrpCat.{v} :=
  ⟨localImagePresheaf J f, by
    apply Presheaf.isSheaf_of_isSheaf_comp J (s := forget AddCommGrpCat.{v})
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf J (localImage J f).toFunctor
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ G.property⟩

private def localImageι {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    localImageSheaf J f ⟶ G :=
  ⟨{ app U := AddCommGrpCat.ofHom (localImageGroup J f U).subtype
     naturality := by intros; ext x; rfl }⟩

private def toLocalImage {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    F ⟶ localImageSheaf J f :=
  ⟨{ app U := AddCommGrpCat.ofHom
       { toFun := fun x => ⟨f.hom.app U x,
           (Subfunctor.range (Functor.whiskerRight f.hom (forget AddCommGrpCat.{v}))).le_sheafify
             J U ⟨x, rfl⟩⟩
         map_zero' := by apply Subtype.ext; exact map_zero _
         map_add' := by intros; apply Subtype.ext; exact map_add _ _ _ }
     naturality := by
       intro U V i
       ext x
       apply Subtype.ext
       exact f.hom.naturality_apply i x }⟩

variable [HasSheafify J AddCommGrpCat.{v}]

private theorem imageSieve_mem_of_epi
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Epi f]
    {U : Cᵒᵖ} (y : G.obj.obj U) : Presheaf.imageSieve f.hom y ∈ J U.unop := by
  let ι := localImageι J f
  have hι : Mono ι := by
    apply (sheafToPresheaf J _).mono_of_mono_map
    exact (NatTrans.mono_iff_mono_app ι.hom).mpr fun V =>
      (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  have hfac : toLocalImage J f ≫ ι = f := by ext V x; rfl
  have hιepi : Epi ι := epi_of_epi_fac hfac
  let : IsIso ι := isIso_of_mono_of_epi ι
  let x := ((inv ι).hom.app U) y
  have hx : ι.hom.app U x = y := by
    exact ConcreteCategory.congr_hom
      (congr_app ((sheafToPresheaf J _).congr_map (IsIso.inv_hom_id ι)) U) y
  have hxp : Presheaf.imageSieve f.hom x.val ∈ J U.unop := x.property
  exact hx ▸ hxp

/-- An epi of abelian sheaves is surjective on sections at any object with
no proper covering sieve. -/
theorem epi_app_surjective
    (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op T)) := by
  intro y
  have hS : Presheaf.imageSieve f.hom y = ⊤ :=
    h _ (imageSieve_mem_of_epi J f y)
  have hid : Presheaf.imageSieve f.hom y (𝟙 T) := by
    rw [hS]
    trivial
  obtain ⟨x, hx⟩ := hid
  exact ⟨x, by simpa using hx⟩

/-- Actual evaluation at the specified object preserves epimorphisms. -/
theorem sections_preservesEpimorphisms
    (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op T)).PreservesEpimorphisms where
  preserves f _ :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (epi_app_surjective J T h f)

/-- Actual global sections preserve finite limits by the native constant-sheaf adjunction. -/
theorem sections_preservesFiniteLimits (hT : IsTerminal T) :
    PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{v}).obj (op T)) := by
  let Γ := (sheafSections J AddCommGrpCat.{v}).obj (op T)
  let : Γ.IsRightAdjoint := (constantSheafAdj J AddCommGrpCat hT).isRightAdjoint
  infer_instance

/-- Global sections at a terminal object with split covers are exact. -/
theorem sections_preservesFiniteColimits
    (hT : IsTerminal T) (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤) :
    PreservesFiniteColimits ((sheafSections J AddCommGrpCat.{v}).obj (op T)) := by
  let Γ := (sheafSections J AddCommGrpCat.{v}).obj (op T)
  let : Γ.IsRightAdjoint := (constantSheafAdj J AddCommGrpCat hT).isRightAdjoint
  let : Γ.PreservesEpimorphisms := sections_preservesEpimorphisms J T h
  let : Γ.Additive := { map_add := by intros; rfl }
  let : Γ.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels Γ
  exact Functor.preservesFiniteColimits_of_preservesHomology Γ

/-- The actual constant integer sheaf is projective, using the native constant
sheaf/evaluation adjunction. -/
theorem constant_integer_projective
    (hT : IsTerminal T) (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤) :
    Projective ((constantSheaf J AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of (ULift.{v} ℤ))) := by
  let : ((sheafSections J AddCommGrpCat.{v}).obj (op T)).PreservesEpimorphisms :=
    sections_preservesEpimorphisms J T h
  exact (constantSheafAdj J AddCommGrpCat hT).map_projective _ AddCommGrpCat.projective_uliftZ

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Positive-degree cohomology is zero for the original Ext-based Sheaf.H. -/
theorem H_eq_zero
    (hT : IsTerminal T) (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤)
    (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (x : Sheaf.H.{w} F q) : x = 0 := by
  let := constant_integer_projective J T hT h
  cases q with
  | zero => simp at hq
  | succ n => exact Abelian.Ext.eq_zero_of_projective x

/-- Original positive-degree cohomology is trivial at the specified Ext universe. -/
theorem subsingleton_H
    (hT : IsTerminal T) (h : ∀ (S : Sieve T), S ∈ J T → S = ⊤)
    (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_of_forall_eq 0 (H_eq_zero J T hT h F q hq)

end CategoryTheory.SheafCohomology.SplitTerminal
