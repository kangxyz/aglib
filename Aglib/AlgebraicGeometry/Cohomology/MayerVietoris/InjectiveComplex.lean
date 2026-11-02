/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
/-! # The genuine two-open sequence on injective sheaf complexes

Original section restriction maps on a binary open cover give a short exact
sequence after applying them to an injective module-sheaf complex. This is the
cochain-level input to a two-open derived-global-section comparison; no such
comparison is assumed here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
universe u v
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {X : Scheme.{u}}

/-- Original restriction of additive sections. -/
abbrev res (M : X.Modules) {U V : X.Opens} (h : U ≤ V) : Γ(M, V) →+ Γ(M, U) :=
  (M.presheaf.map (homOfLE h).op).hom

@[simp] lemma res_res (M : X.Modules) {U V W : X.Opens} (h : U ≤ V) (k : V ≤ W)
    (s : Γ(M, W)) : res M h (res M k s) = res M (h.trans k) s := by
  change ((M.presheaf.map (homOfLE h).op).hom.comp
    (M.presheaf.map (homOfLE k).op).hom) s = _
  rw [← AddCommGrpCat.hom_comp, ← Functor.map_comp]
  rfl

/-- The restriction pair on the original global sections. -/
def augmentation (M : X.Modules) (U V : X.Opens) :
    Γ(M, ⊤) →+ Γ(M, U) × Γ(M, V) :=
  (res M le_top).prod (res M le_top)

/-- The signed difference of the original section restrictions. -/
def difference (M : X.Modules) (U V : X.Opens) :
    Γ(M, U) × Γ(M, V) →+ Γ(M, U ⊓ V) :=
  (res M inf_le_left).comp (AddMonoidHom.fst _ _) -
    (res M inf_le_right).comp (AddMonoidHom.snd _ _)

@[simp] lemma difference_apply (M : X.Modules) (U V : X.Opens)
    (a : Γ(M, U)) (b : Γ(M, V)) :
    difference M U V (a, b) = res M inf_le_left a - res M inf_le_right b := rfl

lemma difference_augmentation (M : X.Modules) (U V : X.Opens) :
    (difference M U V).comp (augmentation M U V) = 0 := by
  ext s
  change res M inf_le_left (res M le_top s) -
    res M inf_le_right (res M le_top s) = 0
  simp only [res_res, sub_self]

/-- The augmented original two-open section sequence. -/
def sectionSequence (M : X.Modules) (U V : X.Opens) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (augmentation M U V))
    (AddCommGrpCat.ofHom (difference M U V))
    (AddCommGrpCat.hom_ext (difference_augmentation M U V))

lemma augmentation_injective (M : X.Modules) (U V : X.Opens) (hUV : U ⊔ V = ⊤) :
    Function.Injective (augmentation M U V) := by
  intro a b hab
  let W : Bool → X.Opens := fun i => if i then U else V
  have hw : (⨆ i, W i) = ⊤ := by
    simpa only [iSup_bool_eq, W, Bool.false_eq_true, ite_false, ite_true, sup_comm]
      using hUV
  apply TopCat.Sheaf.eq_of_locally_eq' ((toAdditiveSheaf X).obj M)
    W ⊤ (fun _ => homOfLE le_top) (by rw [hw])
  intro i
  cases i
  · exact congrArg Prod.snd hab
  · exact congrArg Prod.fst hab

lemma sectionSequence_exact (M : X.Modules) (U V : X.Opens) (hUV : U ⊔ V = ⊤) :
    (sectionSequence M U V).Exact := by
  rw [ShortComplex.ab_exact_iff]
  rintro ⟨a, b⟩ hab
  have hab' : res M inf_le_left a = res M inf_le_right b := sub_eq_zero.mp hab
  let W : Bool → X.Opens := fun i => if i then U else V
  have hw : (⨆ i, W i) = ⊤ := by
    simpa only [iSup_bool_eq, W, Bool.false_eq_true, ite_false, ite_true, sup_comm]
      using hUV
  let s : ∀ i, Γ(M, W i) := fun i => by
    cases i
    · exact b
    · exact a
  have hs : TopCat.Presheaf.IsCompatible M.presheaf W s := by
    intro i j
    cases i <;> cases j
    · rfl
    · change res M inf_le_left b = res M inf_le_right a
      have hh := congrArg (res M (show V ⊓ U ≤ U ⊓ V from
        le_inf inf_le_right inf_le_left)) hab'
      simpa only [res_res] using hh.symm
    · exact hab'
    · rfl
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing' ((toAdditiveSheaf X).obj M)
    W ⊤ (fun _ => homOfLE le_top) (by rw [hw]) s hs
  exact ⟨t, Prod.ext (ht true) (ht false)⟩

lemma difference_surjective (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf]
    (U V : X.Opens) : Function.Surjective (difference M U V) := by
  have h := TopCat.Presheaf.IsFlasque.epi (F := M.presheaf)
    (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
  obtain hs := (AddCommGrpCat.epi_iff_surjective _).mp h
  intro z
  obtain ⟨a, ha⟩ := hs z
  refine ⟨(a, 0), ?_⟩
  change res M inf_le_left a - res M inf_le_right 0 = z
  simpa using ha

/-- The original section sequence of a flasque module sheaf is short exact. -/
theorem sectionSequence_shortExact (M : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] (U V : X.Opens) (hUV : U ⊔ V = ⊤) :
    (sectionSequence M U V).ShortExact where
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (augmentation_injective M U V hUV)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (difference_surjective M U V)
  exact := sectionSequence_exact M U V hUV

/-- The original additive section functor on an open. -/
abbrev sectionsFunctor (X : Scheme.{u}) (U : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.additiveEvaluation X.ringCatSheaf (op U)

instance sectionsFunctor_additive (X : Scheme.{u}) (U : X.Opens) :
    (sectionsFunctor X U).Additive where
  map_add := by intros; rfl

/-- Pairs of original sections, retaining functoriality in the module sheaf. -/
def pairFunctor (X : Scheme.{u}) (U V : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} where
  obj M := .of (Γ(M, U) × Γ(M, V))
  map f := AddCommGrpCat.ofHom ((f.app U).hom.prodMap (f.app V).hom)
  map_id M := by ext s <;> rfl
  map_comp f g := by ext s <;> rfl

instance pairFunctor_additive (X : Scheme.{u}) (U V : X.Opens) :
    (pairFunctor X U V).Additive where
  map_add := by intros; ext s; rfl

@[simp] lemma app_res {M N : X.Modules} (f : M ⟶ N) {U V : X.Opens}
    (h : U ≤ V) (s : Γ(M, V)) :
    (f.app U).hom (res M h s) = res N h ((f.app V).hom s) := by
  have hh := congrArg (fun g => AddCommGrpCat.Hom.hom g s)
    (f.mapPresheaf.naturality (homOfLE h).op)
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, Scheme.Modules.mapPresheaf_app]
    using hh

/-- The natural global restriction pair. -/
def augmentationNat (X : Scheme.{u}) (U V : X.Opens) :
    sectionsFunctor X ⊤ ⟶ pairFunctor X U V where
  app M := AddCommGrpCat.ofHom (augmentation M U V)
  naturality M N f := by
    ext s
    apply Prod.ext
    · exact (app_res f le_top s).symm
    · exact (app_res f le_top s).symm

/-- The natural signed overlap restriction. -/
def differenceNat (X : Scheme.{u}) (U V : X.Opens) :
    pairFunctor X U V ⟶ sectionsFunctor X (U ⊓ V) where
  app M := AddCommGrpCat.ofHom (difference M U V)
  naturality M N f := by
    ext s
    change res N inf_le_left ((f.app U).hom s.1) -
      res N inf_le_right ((f.app V).hom s.2) =
      (f.app (U ⊓ V)).hom (res M inf_le_left s.1 - res M inf_le_right s.2)
    rw [map_sub, app_res, app_res]

/-- The genuine two-open restriction sequence of additive cochain complexes. -/
def cochainSequence (U V : X.Opens) (I : CochainComplex X.Modules ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex (augmentationNat X U V) _).app I)
    ((NatTrans.mapHomologicalComplex (differenceNat X U V) _).app I) (by
      ext n s
      exact congrArg (fun f : Γ(I.X n, ⊤) →+ Γ(I.X n, U ⊓ V) => f s)
        (difference_augmentation (I.X n) U V))

/-- Flasque terms make the original two-open cochain sequence short exact. -/
theorem cochainSequence_shortExact (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (I : CochainComplex X.Modules ℕ)
    (hI : ∀ n, TopCat.Presheaf.IsFlasque (I.X n).presheaf) :
    (cochainSequence U V I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let := hI n
  exact sectionSequence_shortExact (I.X n) U V hUV

/-- An actual injective sheaf resolution gives a short exact sequence of the
original additive section complexes on any binary open cover. -/
theorem injectiveResolution_cochainSequence_shortExact (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (M : X.Modules) (I : InjectiveResolution M) :
    (cochainSequence U V I.cocomplex).ShortExact := by
  apply cochainSequence_shortExact U V hUV
  intro n
  exact injective_isFlasque X (I.cocomplex.X n)

end AlgebraicGeometry.Scheme.Modules.TwoOpen
