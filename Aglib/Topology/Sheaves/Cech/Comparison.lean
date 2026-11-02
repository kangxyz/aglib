/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Augmentation
public import Aglib.Topology.Sheaves.Cech.Resolution
public import Aglib.Algebra.Homology.CochainComplex.Augmentation
public import Aglib.Algebra.Homology.TotalComplex.AddCommGrp
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Original Cech comparison for acyclic open covers

The original Cech complex, row restriction augmentation and column resolution
augmentation form one actual bicomplex. Gluing and the topological stalk
calculation give the row quasi-isomorphisms. Positive exactness of the actual
resolution sections on tuple intersections gives the column quasi-isomorphisms.
Both augmentations use the existing first-quadrant total-complex construction.

The resulting comparison is natural for supplied resolution lifts and independent
of the supplied resolution. The ordinary cohomology API selects one resolution
internally and requires only the open-cover condition and vanishing of the
original positive open-Ext groups on each tuple intersection. It retains the
same section-cycle normalization and original `Sheaf.H.map`.

Extraction source: `AlgebraicGeometry.Scheme.Cohomology` in Cech/Comparison,
original R5Lab revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite
open TopCat.Sheaf.Cohomology

namespace TopCat.Sheaf.Cech
universe u

section CechAugmentation
open CategoryTheory.Cech HomologicalComplex
universe v
variable (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)


section Additive
variable (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Restriction of additive sections along an inclusion of opens. -/
abbrev aRes {V W : Opens X} (h : V ≤ W) :=
  (A.obj.map (homOfLE h).op).hom

private theorem aRes_comp {V W T : Opens X} (h : V ≤ W) (k : W ≤ T)
    (s : A.obj.obj (op T)) : aRes X A h (aRes X A k s) = aRes X A (h.trans k) s := by
  change (A.obj.map (homOfLE k).op ≫ A.obj.map (homOfLE h).op) s = _
  rw [← A.obj.map_comp]
  rfl

private theorem aRes_component_congr
    (z : ((cechComplexFunctor U).obj A.obj).X 0)
    {a a' : Fin 1 → ι} (e : a = a') {V : Opens X}
    (h : V ≤ ∏ᶜ fun i => U (a i)) (h' : V ≤ ∏ᶜ fun i => U (a' i)) :
    aRes X A h (Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun i => U (b i)))) a z) =
      aRes X A h' (Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun i => U (b i)))) a' z) := by
  subst a'
  rfl

/-- The section on each cover open obtained from a degree-zero Cech cochain. -/
def cechZeroFamily (z : ((cechComplexFunctor U).obj A.obj).X 0) (i : ι) :
    A.obj.obj (op (U i)) :=
  aRes X A (le_tupleOpen_const U i)
    (Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) (fun _ => i) z)

private theorem cechZeroFamily_compatible
    (z : ((cechComplexFunctor U).obj A.obj).X 0)
    (hz : ((cechComplexFunctor U).obj A.obj).d 0 1 z = 0) :
    TopCat.Presheaf.IsCompatible A.obj U (cechZeroFamily X U A z) := by
  intro i j
  have hh := congrArg (fun t => aRes X A (pair_le_tupleOpen U i j)
    (Pi.π (fun b : Fin 2 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) ![i, j] t)) hz
  have hd := congrArg (fun f : ((cechComplexFunctor U).obj A.obj).X 0 ⟶
    A.obj.obj (op (∏ᶜ fun k : Fin 2 => U ((![i, j] : Fin 2 → ι) k))) => f.hom z)
      (cech_d_comp_π U A.obj 0 ![i, j])
  erw [Fin.sum_univ_two] at hd
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul,
    AddCommGrpCat.hom_add, AddCommGrpCat.hom_neg,
    AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddCommGrpCat.hom_comp,
    AddMonoidHom.comp_apply] at hd
  erw [hd] at hh
  have h₀ : (fun k : Fin 1 => (![i, j] : Fin 2 → ι) ((0 : Fin 2).succAbove k)) =
      (fun _ => j) := by funext k; fin_cases k; rfl
  have h₁ : (fun k : Fin 1 => (![i, j] : Fin 2 → ι) ((1 : Fin 2).succAbove k)) =
      (fun _ => i) := by funext k; fin_cases k; rfl
  simp only [map_zero, map_add, map_neg] at hh
  change aRes X A (pair_le_tupleOpen U i j) (aRes X A _ _) +
    -aRes X A (pair_le_tupleOpen U i j) (aRes X A _ _) = 0 at hh
  simp only [aRes_comp] at hh
  erw [aRes_component_congr X U A z h₀ _ (inf_le_right.trans (le_tupleOpen_const U j)),
    aRes_component_congr X U A z h₁ _ (inf_le_left.trans (le_tupleOpen_const U i))] at hh
  have he := (add_neg_eq_zero.mp hh).symm
  change aRes X A inf_le_left (cechZeroFamily X U A z i) =
    aRes X A inf_le_right (cechZeroFamily X U A z j)
  simpa only [cechZeroFamily, aRes_comp] using he

private theorem cechZeroFamily_component
    (z : ((cechComplexFunctor U).obj A.obj).X 0) (a : Fin 1 → ι) :
    aRes X A (leOfHom (Pi.π (fun k : Fin 1 => U (a k)) 0))
        (cechZeroFamily X U A z (a 0)) =
      Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) a z := by
  obtain ⟨i, rfl⟩ : ∃ i, a = fun _ => i :=
    ⟨a 0, funext fun k => congrArg a (Subsingleton.elim k 0)⟩
  simp only [cechZeroFamily, aRes_comp]
  change (A.obj.map (𝟙 _)) _ = _
  simp

/-- Gluing identifies the kernel of the actual degree-zero Cech differential. -/
theorem additiveCechAugmentation_exact (hU : iSup U = ⊤) :
    (ShortComplex.mk (cechAugmentationZero X U A.obj)
      (((cechComplexFunctor U).obj A.obj).d 0 1) (cechAugmentationZero_d X U A.obj)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' (X := X) A U ⊤ (fun _ =>
    homOfLE le_top)
    hU.ge (cechZeroFamily X U A z) (cechZeroFamily_compatible X U A z hz)
  refine ⟨s, ?_⟩
  apply Concrete.limit_ext (Discrete.functor
    (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))))
  intro a
  change Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) a.as
    (cechAugmentationZero X U A.obj s) =
      Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) a.as z
  have he := ConcreteCategory.congr_hom (cechAugmentationZero_π X U A.obj a.as) s
  change Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) a.as
    (cechAugmentationZero X U A.obj s) = _ at he
  erw [he]
  rw [← cechZeroFamily_component X U A z a.as, ← hs (a.as 0)]
  change aRes X A le_top s = aRes X A _ (aRes X A le_top s)
  rw [aRes_comp]

/-- Restriction along an actual open cover is injective. -/
theorem additiveCechAugmentation_mono (hU : iSup U = ⊤) :
    Mono (cechAugmentationZero X U A.obj) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro s t h
  apply TopCat.Sheaf.eq_of_locally_eq' (X := X) A U ⊤ (fun _ => homOfLE le_top) hU.ge s t
  intro i
  have hh := congrArg (cechZeroFamily X U A · i) h
  have hc (w : A.obj.obj (op ⊤)) :
      cechZeroFamily X U A (cechAugmentationZero X U A.obj w) i =
        A.obj.map (homOfLE le_top).op w := by
    dsimp only [cechZeroFamily]
    have he := ConcreteCategory.congr_hom (cechAugmentationZero_π X U A.obj (fun _ => i)) w
    change Pi.π (fun b : Fin 1 → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) (fun _ => i)
      (cechAugmentationZero X U A.obj w) = _ at he
    erw [he]
    change aRes X A _ (aRes X A le_top w) = aRes X A le_top w
    rw [aRes_comp]
  simpa only [hc] using hh

/-- The actual restriction augmentation is a quasi-isomorphism for additive-injective sheaves on
  an open cover. -/
theorem additiveInjectiveCechAugmentation_quasiIso [Injective A] (hU : iSup U = ⊤) :
    QuasiIso (cechAugmentation X U A.obj) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    have : Mono ((cechAugmentation X U A.obj).f 0) := by
      rw [cechAugmentation_f_zero]
      exact additiveCechAugmentation_mono X U A hU
    apply CochainComplex.quasiIsoAtZero_of_augmentation_exact
    simpa only [cechAugmentation_f_zero] using additiveCechAugmentation_exact X U A hU
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n)]
    exact additiveInjectiveCech_exact_succ X A U n

end Additive

end CechAugmentation

section CechResolution
open CategoryTheory.Cech HomologicalComplex HomologicalComplex₂
variable (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)

instance additiveCechComplexFunctor_additive :
    (cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive where
  map_add := by
    intro P Q f g
    ext n : 1
    apply Pi.hom_ext
    intro a
    simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Preadditive.add_comp]

/-- The Cech complex functor on the actual underlying additive presheaf. -/
def additiveCechFunctor : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CochainComplex AddCommGrpCat.{u} ℕ :=
  sheafToPresheaf _ _ ⋙ cechComplexFunctor U

instance : (additiveCechFunctor X U).Additive := by
  dsimp [additiveCechFunctor]
  infer_instance

/-- The functor concentrating the second degree of an additive bicomplex in zero. -/
abbrev additiveCechSingleSecondZero :=
  (CochainComplex.single₀ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)

variable {X} {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A)

/-- The actual additive resolution and actual Cech functor, with Cech degree first. -/
def additiveCechResolution : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip (((additiveCechFunctor X U).mapHomologicalComplex _).obj R.cocomplex)

/-- Row augmentation by the actual restrictions of each resolution term. -/
def additiveCechRowAugmentation :
    additiveCechSingleSecondZero.obj
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex) ⟶
    (additiveCechResolution U R).flip where
  f q := cechAugmentation X U (R.cocomplex.X q).obj
  comm' i j _ := (cechAugmentation_naturality X U (R.cocomplex.d i j).hom).symm

theorem additiveCechRowAugmentation_quasiIso (hU : iSup U = ⊤) (q : ℕ) :
    QuasiIso ((additiveCechRowAugmentation U R).f q) :=
  additiveInjectiveCechAugmentation_quasiIso X U (R.cocomplex.X q) hU

theorem cechResolutionAugmentationZero_d (p : ℕ) :
    ((additiveCechFunctor X U).map (R.ι.f 0)).f p ≫
      ((additiveCechResolution U R).X p).d 0 1 = 0 := by
  change ((additiveCechFunctor X U).map (R.ι.f 0)).f p ≫
    ((additiveCechFunctor X U).map (R.cocomplex.d 0 1)).f p = 0
  rw [← comp_f, ← Functor.map_comp]
  have h : R.ι.f 0 ≫ R.cocomplex.d 0 1 = 0 := by simp
  rw [h, Functor.map_zero, zero_f]

/-- Column augmentation induced by the unchanged coefficient-to-resolution inclusion. -/
def additiveCechColumnAugmentation :
    additiveCechSingleSecondZero.obj ((additiveCechFunctor X U).obj A) ⟶
      additiveCechResolution U R where
  f p := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨((additiveCechFunctor X U).map (R.ι.f 0)).f p,
      cechResolutionAugmentationZero_d U R p⟩
  comm' i j _ := by
    apply from_single_hom_ext
    simp only [comp_f, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
      ]
    exact ((additiveCechFunctor X U).map (R.ι.f 0)).comm i j

@[simp] theorem additiveCechColumnAugmentation_f_zero (p : ℕ) :
    ((additiveCechColumnAugmentation U R).f p).f 0 =
      ((additiveCechFunctor X U).map (R.ι.f 0)).f p := by
  simp [additiveCechColumnAugmentation]

variable (X)

/-- Degree `p` of the Cech complex of an additive sheaf. -/
def additiveCechDegreeFunctor (p : ℕ) :=
  additiveCechFunctor X U ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (.up ℕ) p

instance (p : ℕ) : (additiveCechDegreeFunctor X U p).Additive := by
  dsimp [additiveCechDegreeFunctor]
  infer_instance

/-- The discrete diagram of `(p + 1)`-fold intersections of the chosen opens. -/
def cechTupleOpens (p : ℕ) : Discrete (Fin (p + 1) → ι) ⥤ (Opens X)ᵒᵖ :=
  Discrete.functor fun a => op (∏ᶜ fun k => U (a k))

/-- The family of section groups on all degree-`p` tuple intersections. -/
def additiveCechSectionFamilyFunctor (p : ℕ) :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft _ _ _).obj (cechTupleOpens X U p)

instance (p : ℕ) : (additiveCechSectionFamilyFunctor X U p).Additive := by
  dsimp [additiveCechSectionFamilyFunctor]
  infer_instance

instance (p : ℕ) : PreservesFiniteLimits (additiveCechSectionFamilyFunctor X U p) := by
  dsimp [additiveCechSectionFamilyFunctor]
  infer_instance

/-- A Cech degree as the limit of its discrete family of section groups. -/
def additiveCechDegreeIsoLimit (p : ℕ) :
    additiveCechDegreeFunctor X U p ≅ additiveCechSectionFamilyFunctor X U p ⋙ lim := by
  refine NatIso.ofComponents
    (fun A => Pi.isoLimit ((additiveCechSectionFamilyFunctor X U p).obj A)) ?_
  intro A B f
  apply limit.hom_ext
  rintro ⟨a⟩
  simp only [Category.assoc, Functor.comp_map, Pi.isoLimit_hom_π, lim_map, limMap_π,
    Pi.isoLimit_hom_π_assoc]
  change ((cechComplexFunctor U).map f.hom).f p ≫ Pi.π _ a =
    Pi.π _ a ≫ f.hom.app _
  simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, Pi.map_π]

instance (p : ℕ) : PreservesFiniteLimits (additiveCechDegreeFunctor X U p) :=
  preservesFiniteLimits_of_natIso (additiveCechDegreeIsoLimit X U p).symm

variable {X}

/-- Left exactness of actual products of sections gives the column augmentation in degree zero. -/
theorem additiveCechColumnAugmentation_quasiIsoAt_zero (p : ℕ) :
    QuasiIsoAt ((additiveCechColumnAugmentation U R).f p) 0 := by
  let F := additiveCechDegreeFunctor X U p
  have hi : IsIso (R.toRightDerivedZero' F) := inferInstance
  have hh := (CochainComplex.isIso_liftCycles_iff
    ((F.mapHomologicalComplex _).obj R.cocomplex) (F.map (R.ι.f 0))
      (by dsimp; rw [← F.map_comp, R.ι_f_zero_comp_complex_d, F.map_zero])).mp hi
  have : Mono (((additiveCechColumnAugmentation U R).f p).f 0) := by
    rw [additiveCechColumnAugmentation_f_zero]
    exact hh.2
  apply CochainComplex.quasiIsoAtZero_of_augmentation_exact
  simpa [F, additiveCechDegreeFunctor, additiveCechResolution, HomologicalComplex₂.flip,
    Functor.mapHomologicalComplex, HomologicalComplex.eval] using hh.1

/-- Products of the actual exact resolution-section columns are exact in positive degrees. -/
theorem additiveCechResolution_column_exact_succ
    (hex : ∀ (p : ℕ) (a : Fin (p + 1) → ι) (n : ℕ),
      (((additiveSectionsFunctor X (∏ᶜ fun k => U (a k))).mapHomologicalComplex _).obj
        R.cocomplex).ExactAt (n + 1))
    (p n : ℕ) : ((additiveCechResolution U R).X p).ExactAt (n + 1) := by
  let G := additiveCechSectionFamilyFunctor X U p
  let T := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  have hT : T.ExactAt (n + 1) := by
    rw [exactAt_iff_isZero_homology]
    apply Functor.isZero
    intro a
    let E := (CategoryTheory.evaluation (Discrete (Fin (p + 1) → ι)) AddCommGrpCat.{u}).obj a
    have h := hex p a.as n
    exact h.isZero_homology.of_iso ((T.sc (n + 1)).mapHomologyIso E).symm
  have hprod : ((lim.mapHomologicalComplex (.up ℕ)).obj T).ExactAt (n + 1) :=
    hT.map (lim (J := Discrete (Fin (p + 1) → ι)) (C := AddCommGrpCat.{u}))
  let e : (((additiveCechDegreeFunctor X U p).mapHomologicalComplex _).obj R.cocomplex) ≅
      ((lim.mapHomologicalComplex (.up ℕ)).obj T) :=
    (NatIso.mapHomologicalComplex (additiveCechDegreeIsoLimit X U p) _).app R.cocomplex ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ lim)) _).app R.cocomplex).symm
  exact hprod.of_iso e.symm

/-- Positive exactness of actual resolution sections makes the original column
  augmentations quasi-isomorphisms. -/
theorem additiveCechColumnAugmentation_quasiIso
    (hex : ∀ (p : ℕ) (a : Fin (p + 1) → ι) (n : ℕ),
      (((additiveSectionsFunctor X (∏ᶜ fun k => U (a k))).mapHomologicalComplex _).obj
        R.cocomplex).ExactAt (n + 1))
    (p : ℕ) : QuasiIso ((additiveCechColumnAugmentation U R).f p) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact additiveCechColumnAugmentation_quasiIsoAt_zero U R p
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n)]
    exact additiveCechResolution_column_exact_succ U R hex p n

section Naturality
variable {U} {B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B} {R}

/-- The actual Cech bicomplex map of a lift between additive injective resolutions. -/
def additiveCechResolutionMap (φ : InjectiveResolution.Hom R S f) :
    additiveCechResolution U R ⟶ additiveCechResolution U S :=
  (flipFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ)).map
    (((additiveCechFunctor X U).mapHomologicalComplex _).map φ.hom)

/-- The row augmentation commutes with every actual coefficient-resolution lift. -/
theorem additiveCechRowAugmentation_naturality (φ : InjectiveResolution.Hom R S f) :
    additiveCechSingleSecondZero.map
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) ≫
        additiveCechRowAugmentation U S =
      additiveCechRowAugmentation U R ≫
        (flipFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ)).map (additiveCechResolutionMap φ) := by
  ext q : 1
  exact cechAugmentation_naturality X U (φ.hom.f q).hom

/-- The column augmentation commutes with the original coefficient map and every lift. -/
theorem additiveCechColumnAugmentation_naturality (φ : InjectiveResolution.Hom R S f) :
    additiveCechSingleSecondZero.map ((additiveCechFunctor X U).map f) ≫
      additiveCechColumnAugmentation U S =
    additiveCechColumnAugmentation U R ≫ additiveCechResolutionMap φ := by
  ext p : 1
  apply from_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero, additiveCechColumnAugmentation_f_zero]
  change ((additiveCechFunctor X U).map f).f p ≫
    ((additiveCechFunctor X U).map (S.ι.f 0)).f p =
      ((additiveCechFunctor X U).map (R.ι.f 0)).f p ≫
        ((additiveCechFunctor X U).map (φ.hom.f 0)).f p
  rw [← comp_f, ← comp_f, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun g => ((additiveCechFunctor X U).map g).f p)
    φ.ι_f_zero_comp_hom_f_zero.symm

end Naturality

end CechResolution

section CechTotalComparison
open HomologicalComplex HomologicalComplex₂
open HomologicalComplex₂.AddCommGrp
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
variable {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A)

/-- The actual Cech complex maps to the total through the resolution inclusion. -/
def additiveCechToTotal : (additiveCechFunctor X U).obj A ⟶
    (additiveCechResolution U R).total (.up ℕ) :=
  totalAugmentation (additiveCechColumnAugmentation U R)

/-- Actual global resolution sections map to the same total through restrictions. -/
def additiveResolutionSectionsToTotal :
    ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex ⟶
      (additiveCechResolution U R).total (.up ℕ) :=
  totalAugmentationFlip (additiveCechRowAugmentation U R)

theorem additiveResolutionSectionsToTotal_quasiIso (hU : iSup U = ⊤) :
    QuasiIso (additiveResolutionSectionsToTotal U R) :=
  quasiIso_totalAugmentationFlip _ (additiveCechRowAugmentation_quasiIso U R hU)

theorem additiveCechToTotal_quasiIso
    (hex : ∀ (p : ℕ) (a : Fin (p + 1) → ι) (n : ℕ),
      (((additiveSectionsFunctor X (∏ᶜ fun k => U (a k))).mapHomologicalComplex _).obj
        R.cocomplex).ExactAt (n + 1)) :
    QuasiIso (additiveCechToTotal U R) :=
  quasiIso_totalAugmentation _ (additiveCechColumnAugmentation_quasiIso U R hex)

section Naturality
variable {U R} {B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B}

theorem additiveCechToTotal_naturality (φ : InjectiveResolution.Hom R S f) :
    (additiveCechFunctor X U).map f ≫ additiveCechToTotal U S =
      additiveCechToTotal U R ≫ HomologicalComplex₂.total.map (additiveCechResolutionMap φ) (.up
        ℕ) :=
  totalAugmentation_naturality _ _ _ _ (additiveCechColumnAugmentation_naturality φ)

theorem additiveResolutionSectionsToTotal_naturality (φ : InjectiveResolution.Hom R S f) :
    ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom ≫
      additiveResolutionSectionsToTotal U S =
    additiveResolutionSectionsToTotal U R ≫
      HomologicalComplex₂.total.map (additiveCechResolutionMap φ) (.up ℕ) :=
  totalAugmentationFlip_naturality _ _ _ _ (additiveCechRowAugmentation_naturality φ)

end Naturality

/-- Positive exactness of the original section complex on every tuple intersection. -/
abbrev HasExactIntersections (R : InjectiveResolution A) : Prop :=
  ∀ (p : ℕ) (a : Fin (p + 1) → ι) (n : ℕ),
    (((additiveSectionsFunctor X (∏ᶜ fun k => U (a k))).mapHomologicalComplex _).obj
      R.cocomplex).ExactAt (n + 1)

variable (hcover : iSup U = ⊤) (hex : HasExactIntersections U R)

/-- The two original augmentations identify Cech homology with actual resolution sections. -/
def additiveCechResolutionHomologyIso (n : ℕ) :
    ((additiveCechFunctor X U).obj A).homology n ≅
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology n := by
  have := additiveCechToTotal_quasiIso U R hex
  have := additiveResolutionSectionsToTotal_quasiIso U R hcover
  exact asIso (homologyMap (additiveCechToTotal U R) n) ≪≫
    (asIso (homologyMap (additiveResolutionSectionsToTotal U R) n)).symm

@[reassoc (attr := simp)]
theorem additiveCechResolutionHomologyIso_hom_comp (n : ℕ) :
    (additiveCechResolutionHomologyIso U R hcover hex n).hom ≫
      homologyMap (additiveResolutionSectionsToTotal U R) n =
        homologyMap (additiveCechToTotal U R) n := by
  unfold additiveCechResolutionHomologyIso
  simp

variable {R} {B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B}

/-- The comparison of the two actual augmentations respects every resolution lift. -/
theorem additiveCechResolutionHomologyIso_naturality
    (hexS : HasExactIntersections U S) (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    homologyMap ((additiveCechFunctor X U).map f) n ≫
      (additiveCechResolutionHomologyIso U S hcover hexS n).hom =
    (additiveCechResolutionHomologyIso U R hcover hex n).hom ≫
      homologyMap (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) n := by
  have := additiveResolutionSectionsToTotal_quasiIso U S hcover
  apply (cancel_mono (homologyMap (additiveResolutionSectionsToTotal U S) n)).mp
  have hc := congrArg (fun g => homologyMap g n) (additiveCechToTotal_naturality (U := U) φ)
  have hr := congrArg (fun g => homologyMap g n)
    (additiveResolutionSectionsToTotal_naturality (U := U) φ)
  simp only [homologyMap_comp] at hc hr
  rw [Category.assoc, additiveCechResolutionHomologyIso_hom_comp,
    Category.assoc, hr, ← Category.assoc, additiveCechResolutionHomologyIso_hom_comp]
  exact hc

variable (R)

/-- The original positive Cech homology computes `Sheaf.H` through the supplied resolution. -/
def additiveCechCohomologyAddEquiv (n : ℕ) :
    ((additiveCechFunctor X U).obj A).homology (n + 1) ≃+
      CategoryTheory.Sheaf.H.{u + 1} A (n + 1) :=
  (additiveCechResolutionHomologyIso U R hcover hex (n + 1)).addCommGroupIsoToAddEquiv.trans
    (additiveResolutionHomologyEquiv R n)

variable {R}

/-- Naturality of the supplied-resolution normalization with the original coefficient map. -/
theorem additiveCechCohomologyAddEquiv_naturality
    (hexS : HasExactIntersections U S) (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((additiveCechFunctor X U).obj A).homology (n + 1)) :
    additiveCechCohomologyAddEquiv U S hcover hexS n
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x) =
    CategoryTheory.Sheaf.H.map f (n + 1)
      (additiveCechCohomologyAddEquiv U R hcover hex n x) := by
  have h := ConcreteCategory.congr_hom
    (additiveCechResolutionHomologyIso_naturality U hcover hex hexS φ (n + 1)) x
  change additiveResolutionHomologyEquiv S n
    ((additiveCechResolutionHomologyIso U S hcover hexS (n + 1)).hom
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x)) = _
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  exact additiveResolutionHomologyEquiv_naturality φ n _

/-- The original comparison does not depend on its supplied resolution. -/
theorem additiveCechCohomologyAddEquiv_independent
    (R S : InjectiveResolution A) (hexR : HasExactIntersections U R)
    (hexS : HasExactIntersections U S) (n : ℕ) :
    additiveCechCohomologyAddEquiv U R hcover hexR n =
      additiveCechCohomologyAddEquiv U S hcover hexS n := by
  let φ : InjectiveResolution.Hom R S (𝟙 A) :=
    ⟨InjectiveResolution.desc (𝟙 _) S R, by simp⟩
  ext x
  have h := additiveCechCohomologyAddEquiv_naturality U hcover hexR hexS φ n x
  erw [(additiveCechFunctor X U).map_id, homologyMap_id] at h
  simpa only [ConcreteCategory.id_apply, CategoryTheory.Sheaf.H.map_id_apply] using h.symm

/-- Acyclicity of the original positive open Ext groups on tuple intersections. -/
abbrev HasAcyclicIntersections
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ (p : ℕ) (a : Fin (p + 1) → ι) (n : ℕ),
    Subsingleton (CategoryTheory.Sheaf.H'.{u + 1} A (n + 1) (∏ᶜ fun k => U (a k)))

/-- Original open-Ext acyclicity gives the actual section exactness needed by the columns. -/
theorem HasAcyclicIntersections.exact (hA : HasAcyclicIntersections U A)
    (R : InjectiveResolution A) : HasExactIntersections U R := by
  intro p a n
  let := hA p a n
  exact additiveResolution_sections_exact_of_HPrime_zero R _ n

/-- Ordinary Cech cohomology computes the original sheaf cohomology with one internal resolution. -/
def cechCohomologyAddEquiv (hcover : iSup U = ⊤)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : HasAcyclicIntersections U A) (n : ℕ) :
    ((additiveCechFunctor X U).obj A).homology (n + 1) ≃+
      CategoryTheory.Sheaf.H.{u + 1} A (n + 1) :=
  additiveCechCohomologyAddEquiv U (injectiveResolution A) hcover
    (HasAcyclicIntersections.exact U hA (injectiveResolution A)) n

/-- The canonical comparison has the exact supplied-resolution normalization. -/
theorem additiveCechCohomologyAddEquiv_eq_canonical
    (R : InjectiveResolution A) (hexR : HasExactIntersections U R)
    (hA : HasAcyclicIntersections U A) (n : ℕ) :
    additiveCechCohomologyAddEquiv U R hcover hexR n =
      cechCohomologyAddEquiv U hcover A hA n :=
  additiveCechCohomologyAddEquiv_independent U hcover R (injectiveResolution A)
    hexR (HasAcyclicIntersections.exact U hA (injectiveResolution A)) n

/-- Canonical naturality uses the original coefficient map without a public resolution choice. -/
theorem cechCohomologyAddEquiv_naturality
    (hA : HasAcyclicIntersections U A) (hB : HasAcyclicIntersections U B)
    (f : A ⟶ B) (n : ℕ) (x : ((additiveCechFunctor X U).obj A).homology (n + 1)) :
    cechCohomologyAddEquiv U hcover B hB n
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x) =
      CategoryTheory.Sheaf.H.map f (n + 1) (cechCohomologyAddEquiv U hcover A hA n x) := by
  let φ : InjectiveResolution.Hom (injectiveResolution A) (injectiveResolution B) f :=
    ⟨InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A), by simp⟩
  exact additiveCechCohomologyAddEquiv_naturality U hcover
    (HasAcyclicIntersections.exact U hA (injectiveResolution A)) (HasAcyclicIntersections.exact U
      hB (injectiveResolution B)) φ n x

end CechTotalComparison

end TopCat.Sheaf.Cech
