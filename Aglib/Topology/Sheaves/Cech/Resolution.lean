/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.SectionCycles
public import Aglib.Topology.Sheaves.FreeAbelianPullback
public import Aglib.Topology.Sheaves.Cech.Restriction
public import Aglib.Topology.Sheaves.Cech.Cocycles
public import Aglib.CategoryTheory.Abelian.Injective.ResolutionKernels
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Homology.Functor

/-!
# Original Cech rows and additive resolution sections on topological spaces

The open-free object and its represented sections are the native free-abelian
sheaf construction. The stalk-skyscraper calculation proves exactness of the
original Cech chain complex on topological spaces. It uses the actual stalk
exactness theorem and makes no enough-points assertion for arbitrary sites.

Resolution homology is identified with the original `Sheaf.H` through the one
section-cycle construction. Naturality retains arbitrary supplied lifts only at
this resolution-normalization boundary. The original `Sheaf.H'` comparison at
the whole space retains the actual constant-integer unit and section values.

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
variable (X : TopCat.{u})

/-- The sheafified free abelian presheaf functor on the open site of `X`. -/
abbrev additiveFreeFunctor :=
  (Functor.whiskeringRight (Opens X)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
/-- The adjunction between sheafified free abelian presheaves and underlying presheaves of sets. -/
abbrev additiveFreeAdjunction :=
  (AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The native free abelian sheaf on each original representable open. -/
abbrev additiveOpenFreeFunctor := TopCat.Sheaf.openFreeAbelianFunctor X

/-- The native open-section representation, with its original unit value. -/
abbrev additiveOpenHomEquiv := TopCat.Sheaf.openFreeAbelianHomEquiv X

/-- Open restriction in the original represented section equivalence. -/
theorem additiveOpenHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (f : (additiveOpenFreeFunctor X).obj V ⟶ A) :
    additiveOpenHomEquiv X U A ((additiveOpenFreeFunctor X).map i ≫ f) =
      A.obj.map i.op (additiveOpenHomEquiv X V A f) :=
  TopCat.Sheaf.openFreeAbelianHomEquiv_naturality X i A f

instance additiveOpenFreeFunctor_map_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((additiveOpenFreeFunctor X).map i) := by
  change Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free))
  have : Mono (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) := by
    apply NatTrans.mono_of_mono_app
  infer_instance

instance additiveSheaf_injective_isFlasque
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective A] :
    TopCat.Presheaf.IsFlasque A.obj where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    let f := (additiveOpenHomEquiv X V.unop A).symm s
    let g := Injective.factorThru f ((additiveOpenFreeFunctor X).map i.unop)
    refine ⟨additiveOpenHomEquiv X U.unop A g, ?_⟩
    calc
      _ = additiveOpenHomEquiv X V.unop A ((additiveOpenFreeFunctor X).map i.unop ≫ g) :=
        (additiveOpenHomEquiv_naturality X i.unop A g).symm
      _ = additiveOpenHomEquiv X V.unop A f :=
        congrArg (additiveOpenHomEquiv X V.unop A) (Injective.comp_factorThru f _)
      _ = s := (additiveOpenHomEquiv X V.unop A).apply_symm_apply s

/-- The open-section representing equivalence is natural in the actual coefficient sheaf. -/
theorem additiveOpenHomEquiv_naturality_coefficient (U : Opens X)
    {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : (additiveOpenFreeFunctor X).obj U ⟶ A) (g : A ⟶ B) :
    additiveOpenHomEquiv X U B (f ≫ g) =
      g.hom.app (op U) (additiveOpenHomEquiv X U A f) :=
  TopCat.Sheaf.openFreeAbelianHomEquiv_comp X U f g

/-- The free additive sheaf on the whole space is canonically the constant integer sheaf. -/
def additiveOpenTopIsoInteger : (additiveOpenFreeFunctor X).obj ⊤ ≅
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) where
  hom := (additiveOpenHomEquiv X ⊤ _).symm (integerSheafHomEquiv _ (𝟙 _))
  inv := (integerSheafHomEquiv _).symm (additiveOpenHomEquiv X ⊤ _ (𝟙 _))
  hom_inv_id := by
    apply (additiveOpenHomEquiv X ⊤ _).injective
    rw [additiveOpenHomEquiv_naturality_coefficient, Equiv.apply_symm_apply,
      ← integerSheafHomEquiv_comp, Category.id_comp, AddEquiv.apply_symm_apply]
  inv_hom_id := by
    apply (integerSheafHomEquiv _).injective
    rw [integerSheafHomEquiv_comp, AddEquiv.apply_symm_apply,
      ← additiveOpenHomEquiv_naturality_coefficient, Category.id_comp,
      Equiv.apply_symm_apply]

/-- The existing open-Ext cohomology on the whole space equals the original
  CategoryTheory.Sheaf.H. -/
def sheafHPrimeTopAddEquiv
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u + 1} A n ⊤ ≃+ CategoryTheory.Sheaf.H.{u + 1} A n :=
  (((Abelian.extFunctor n).mapIso (additiveOpenTopIsoInteger X).op).app
    A).symm.addCommGroupIsoToAddEquiv

/-- The whole-space comparison intertwines the existing coefficient maps in every degree. -/
theorem sheafHPrimeTopAddEquiv_naturality
    {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : A ⟶ B) (n : ℕ) (x : CategoryTheory.Sheaf.H'.{u + 1} A n ⊤) :
    sheafHPrimeTopAddEquiv X B n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app (op ⊤) x) =
      CategoryTheory.Sheaf.H.map f n (sheafHPrimeTopAddEquiv X A n x) := by
  exact congrArg (fun q => q.hom x)
    (((Abelian.extFunctor n).mapIso (additiveOpenTopIsoInteger X).op).inv.naturality f)

/-- In degree zero the comparison is normalized by the actual section-representing equivalences. -/
theorem sheafHPrimeTopAddEquiv_equiv₀
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : CategoryTheory.Sheaf.H'.{u + 1} A 0 ⊤) :
    CategoryTheory.Sheaf.H.equiv₀ A isTerminalTop (sheafHPrimeTopAddEquiv X A 0 x) =
      additiveOpenHomEquiv X ⊤ A (Abelian.Ext.addEquiv₀ x) := by
  change integerSheafHomEquiv A (Abelian.Ext.addEquiv₀
    ((Abelian.Ext.mk₀ (additiveOpenTopIsoInteger X).inv).comp x (Nat.zero_add 0))) = _
  have he : Abelian.Ext.addEquiv₀
      ((Abelian.Ext.mk₀ (additiveOpenTopIsoInteger X).inv).comp x (Nat.zero_add 0)) =
      (additiveOpenTopIsoInteger X).inv ≫ Abelian.Ext.addEquiv₀ x := by
    apply (Abelian.Ext.mk₀_bijective _ _).injective
    rw [Abelian.Ext.mk₀_addEquiv₀_apply]
    conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply x]
    rw [Abelian.Ext.mk₀_comp_mk₀]
    rfl
  rw [he, integerSheafHomEquiv_comp]
  change (Abelian.Ext.addEquiv₀ x).hom.app (op ⊤)
    ((integerSheafHomEquiv _)
      ((integerSheafHomEquiv _).symm (additiveOpenHomEquiv X ⊤ _ (𝟙 _)))) = _
  rw [AddEquiv.apply_symm_apply, ← additiveOpenHomEquiv_naturality_coefficient, Category.id_comp]
  rfl

variable {X}
open CategoryTheory.Abelian

/-- Hom lifting and vanishing in the middle term kill the first Ext group. -/
lemma subsingleton_ext_one_of_shortExact
    (T : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Subsingleton (Ext.{u + 1} T S.X₂ 1)]
    (hs : Function.Surjective (fun f : T ⟶ S.X₂ => f ≫ S.g)) :
    Subsingleton (Ext.{u + 1} T S.X₁ 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x (Subsingleton.elim _ _) rfl
  obtain ⟨f, hf⟩ := hs (Ext.addEquiv₀ z)
  change f ≫ S.g = Ext.addEquiv₀ z at hf
  have hzero := (Ext.covariantSequence_exact T hS 0 1 rfl).zero 1
  have h := congrArg (fun q : AddCommGrpCat.of (Ext.{u + 1} T S.X₂ 0) ⟶
      AddCommGrpCat.of (Ext.{u + 1} T S.X₁ 1) => q.hom (Ext.mk₀ f)) hzero
  change ((Ext.mk₀ f).comp (Ext.mk₀ S.g) (Nat.add_zero 0)).comp hS.extClass rfl = 0 at h
  rw [Ext.mk₀_comp_mk₀, hf, Ext.mk₀_addEquiv₀_apply] at h
  exact hz.symm.trans h

/-- Dimension shifting through a short exact sequence with the indicated actual Ext groups zero. -/
lemma subsingleton_ext_succ_of_shortExact
    (T : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext.{u + 1} T S.X₂ (n + 1))]
    [Subsingleton (Ext.{u + 1} T S.X₃ n)] :
    Subsingleton (Ext.{u + 1} T S.X₁ (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x (Subsingleton.elim _ _) rfl
  exact hz.symm.trans (by rw [Subsingleton.elim z 0, Ext.zero_comp])

/-- Actual section lifting is exactly the lifting of maps from the open-free sheaf. -/
lemma openFree_postcomp_surjective_of_sections (U : Opens X)
    {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : A ⟶ B)
    (hg : Function.Surjective (g.hom.app (op U))) :
    Function.Surjective (fun f : (additiveOpenFreeFunctor X).obj U ⟶ A => f ≫ g) := by
  intro q
  obtain ⟨s, hs⟩ := hg (additiveOpenHomEquiv X U B q)
  refine ⟨(additiveOpenHomEquiv X U A).symm s, ?_⟩
  apply (additiveOpenHomEquiv X U B).injective
  rw [additiveOpenHomEquiv_naturality_coefficient, Equiv.apply_symm_apply]
  exact hs

/-- A flasque additive sheaf is acyclic for the existing open-Ext cohomology on every open. -/
theorem subsingleton_sheafHPrime_of_isFlasque (U : Opens X)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque A.obj] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u + 1} A (n + 1) U) := by
  let T := (additiveOpenFreeFunctor X).obj U
  change Subsingleton (Ext.{u + 1} T A (n + 1))
  induction n generalizing A with
  | zero =>
    let I := injectiveResolution A
    let S := CategoryTheory.InjectiveResolution.initialSequence I
    have hS : S.ShortExact :=
      CategoryTheory.InjectiveResolution.initialSequence_shortExact I
    let : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque A.obj)
    let : Injective S.X₂ := inferInstanceAs (Injective (I.cocomplex.X 0))
    let : Subsingleton (Ext.{u + 1} T S.X₂ 1) :=
      subsingleton_of_forall_eq 0 (fun x => Ext.eq_zero_of_injective x)
    apply subsingleton_ext_one_of_shortExact T hS
    apply openFree_postcomp_surjective_of_sections U
    exact (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS)
  | succ n ih =>
    let I := injectiveResolution A
    let S := CategoryTheory.InjectiveResolution.initialSequence I
    have hS : S.ShortExact :=
      CategoryTheory.InjectiveResolution.initialSequence_shortExact I
    let : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque A.obj)
    let : Injective S.X₂ := inferInstanceAs (Injective (I.cocomplex.X 0))
    let : TopCat.Presheaf.IsFlasque S.X₂.obj := additiveSheaf_injective_isFlasque X S.X₂
    let : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    let : Subsingleton (Ext.{u + 1} T S.X₂ (n + 1 + 1)) :=
      subsingleton_of_forall_eq 0 (fun x => Ext.eq_zero_of_injective x)
    let : Subsingleton (Ext.{u + 1} T S.X₃ (n + 1)) := ih S.X₃
    exact subsingleton_ext_succ_of_shortExact T hS (n + 1)

variable (X : TopCat.{u})

/-- The open-section representing equivalence preserves the actual additive group structures. -/
def additiveOpenHomAddEquiv (U : Opens X)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((additiveOpenFreeFunctor X).obj U ⟶ A) ≃+ A.obj.obj (op U) where
  __ := additiveOpenHomEquiv X U A
  map_add' f g := by
    have he (h : (additiveOpenFreeFunctor X).obj U ⟶ A) :
        additiveOpenHomEquiv X U A h =
          h.hom.app (op U) (additiveOpenHomEquiv X U _ (𝟙 _)) := by
      simpa only [Category.id_comp] using
        additiveOpenHomEquiv_naturality_coefficient X U (𝟙 _) h
    change additiveOpenHomEquiv X U A (f + g) =
      additiveOpenHomEquiv X U A f + additiveOpenHomEquiv X U A g
    rw [he, he f, he g]
    rfl

/-- Actual evaluation of additive sheaves on the indicated open. -/
abbrev additiveSectionsFunctor (U : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u}).obj (op U)

instance additiveSectionsFunctor_additive (U : Opens X) :
    (additiveSectionsFunctor X U).Additive where
  map_add := by intros; rfl

variable {X}

/-- Vanishing of the actual open Ext group forces exactness of any actual additive-injective
  resolution on that open. -/
theorem additiveResolution_sections_exact_of_HPrime_zero
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (U : Opens X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{u + 1} A (n + 1) U)] :
    (((additiveSectionsFunctor X U).mapHomologicalComplex _).obj R.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro s hs
  let f := (additiveOpenHomAddEquiv X U (R.cocomplex.X (n + 1))).symm s
  have hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (additiveOpenHomAddEquiv X U _).injective
    change additiveOpenHomEquiv X U _ (f ≫ R.cocomplex.d (n + 1) (n + 2)) = _
    rw [additiveOpenHomEquiv_naturality_coefficient]
    rw [map_zero]
    change (R.cocomplex.d (n + 1) (n + 2)).hom.app (op U)
      (additiveOpenHomAddEquiv X U _ ((additiveOpenHomAddEquiv X U _).symm s)) = 0
    rw [AddEquiv.apply_symm_apply]
    exact hs
  have hz : R.extMk f (n + 2) rfl hf = 0 :=
    (inferInstance : Subsingleton (CategoryTheory.Sheaf.H'.{u + 1} A (n + 1) U)).elim _ _
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp hz
  refine ⟨additiveOpenHomAddEquiv X U _ g, ?_⟩
  change (R.cocomplex.d n (n + 1)).hom.app (op U)
    (additiveOpenHomEquiv X U _ g) = s
  rw [← additiveOpenHomEquiv_naturality_coefficient, hg]
  exact (additiveOpenHomAddEquiv X U _).apply_symm_apply s


/-- Positive homology of the actual additive-injective resolution sections equals the original
  CategoryTheory.Sheaf.H, through the canonical cycles/boundaries quotient. -/
def additiveResolutionHomologyEquiv
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (n : ℕ) :
    ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n + 1)) ≃+
      CategoryTheory.Sheaf.H.{u + 1} A (n + 1) :=
  (((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).sc'
      n (n + 1) (n + 2)).abHomologyIso).addCommGroupIsoToAddEquiv.trans
        (resolutionSectionsCohomologyEquiv R n)

section CechRows

variable (X : TopCat.{u})
attribute [local instance] Classical.propDecidable

/-- The stalk functor on the actual additive sheaves of the topological space. -/
abbrev cechStalkFunctor (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance cechStalkFunctor_isLeftAdjoint (x : X) :
    (cechStalkFunctor X x).IsLeftAdjoint :=
  (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).isLeftAdjoint

instance cechStalkFunctor_op_isRightAdjoint (x : X) :
    (cechStalkFunctor X x).op.IsRightAdjoint :=
  (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).op.isRightAdjoint

/-- The stalk-skyscraper adjunction composed with open-section representability. -/
def cechOpenStalkHomEquiv (x : X) (U : Opens X) (B : AddCommGrpCat.{u}) :
    (((cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj U)) ⟶ B) ≃
      ((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.obj (op U) :=
  ((stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).homEquiv _ B).trans
    (additiveOpenHomEquiv X U _)

private theorem cechOpenStalkHomEquiv_naturality_open (x : X) {U V : Opens X} (i : U ⟶ V)
    (B : AddCommGrpCat.{u}) (f : (cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj V)
      ⟶ B) :
    cechOpenStalkHomEquiv X x U B
      ((cechStalkFunctor X x).map ((additiveOpenFreeFunctor X).map i) ≫ f) =
      ((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.map i.op
        (cechOpenStalkHomEquiv X x V B f) := by
  exact (congrArg (additiveOpenHomEquiv X U _)
    (Adjunction.homEquiv_naturality_left
      (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x)
      ((additiveOpenFreeFunctor X).map i) f)).trans
        (additiveOpenHomEquiv_naturality X i _ _)

private theorem cechSkyscraper_restrict_isIso (x : X) {U V : Opens X} (i : U ⟶ V)
    (hx : x ∈ V → x ∈ U) (B : AddCommGrpCat.{u}) :
    IsIso (((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.map i.op) := by
  by_cases hv : x ∈ V
  · have hu := hx hv
    change IsIso ((skyscraperSheaf x B).obj.map i.op)
    simp only [skyscraperSheaf_obj_map, hu, ↓reduceDIte]
    infer_instance
  · have hu : x ∉ U := fun h => hv (i.le h)
    exact isIso_of_isTerminal
      (isTerminalSkyscraperSheafObjObjOfNotMem hv)
      (isTerminalSkyscraperSheafObjObjOfNotMem hu) _

private theorem cechOpenFree_stalk_map_isIso (x : X) {U V : Opens X} (i : U ⟶ V)
    (hx : x ∈ V → x ∈ U) :
    IsIso ((cechStalkFunctor X x).map ((additiveOpenFreeFunctor X).map i)) := by
  let p := (cechStalkFunctor X x).map ((additiveOpenFreeFunctor X).map i)
  have hb (B : AddCommGrpCat.{u}) : Function.Bijective
      (fun f : (cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj V) ⟶ B => p ≫ f) := by
    let := cechSkyscraper_restrict_isIso X x i hx B
    apply (Function.Bijective.of_comp_iff' (cechOpenStalkHomEquiv X x U B).bijective _).mp
    have h := (ConcreteCategory.bijective_of_isIso
      (((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.map i.op)).comp
        (cechOpenStalkHomEquiv X x V B).bijective
    convert h using 1
    funext f
    exact cechOpenStalkHomEquiv_naturality_open X x i B f
  obtain ⟨q, hq⟩ := (hb _).surjective (𝟙 _)
  change p ≫ q = 𝟙 _ at hq
  have hq' : q ≫ p = 𝟙 _ := by
    apply (hb _).injective
    change p ≫ (q ≫ p) = p ≫ 𝟙 _
    rw [← Category.assoc, hq, Category.id_comp, Category.comp_id]
  exact ⟨⟨q, hq, hq'⟩⟩

private theorem cechOpenFree_stalk_isZero_of_not_mem (x : X) (U : Opens X) (hx : x ∉ U) :
    IsZero ((cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj U)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cechOpenStalkHomEquiv X x U _).injective
  let : Subsingleton
      (((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj
        ((cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj U))).obj.obj (op U)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (isTerminalSkyscraperSheafObjObjOfNotMem hx).isZero
  exact Subsingleton.elim _ _

open CategoryTheory.Cech

instance cechSheaf_op_hasProducts :
    HasProducts.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})ᵒᵖ := by
  intro J
  exact hasLimitsOfShape_op_of_hasColimitsOfShape

instance cechStalkFunctor_additive (x : X) :
    (cechStalkFunctor X x).Additive where
  map_add := by
    intro A B f g
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (f.hom + g.hom) = _
    exact Functor.map_add _

instance cechStalkFunctor_op_additive (x : X) :
    (cechStalkFunctor X x).op.Additive := by infer_instance

private theorem cechOpenFree_stalkCech_exact_succ (x : X) {ι : Type u}
    (U : ι → Opens X) (i₀ : ι) (hx : x ∈ U i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X ⋙ cechStalkFunctor X x).op).ExactAt
      (n + 1) := by
  let Q := additiveOpenFreeFunctor X ⋙ cechStalkFunctor X x
  let p : Q.op ⟶ (intersectFunctor (U i₀)).op ⋙ Q.op :=
    NatTrans.op (Functor.whiskerRight (intersectToId (U i₀)) Q)
  have hp (V : (Opens X)ᵒᵖ) : IsIso (p.app V) := by
    change IsIso (((cechStalkFunctor X x).map ((additiveOpenFreeFunctor X).map
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)))).op)
    have := cechOpenFree_stalk_map_isIso X x
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)) (fun hv => ⟨hv, hx⟩)
    infer_instance
  let : IsIso p := NatIso.isIso_of_isIso_app p
  exact (restrictedCech_exactAt_succ U Q.op i₀ n).of_iso
    ((cechComplexFunctor U).mapIso (asIso p)).symm

private theorem cechOpenFree_stalkCech_exact_succ_any (x : X) {ι : Type u}
    (U : ι → Opens X) (n : ℕ) :
    ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X ⋙ cechStalkFunctor X x).op).ExactAt
      (n + 1) := by
  by_cases h : ∃ i, x ∈ U i
  · obtain ⟨i, hi⟩ := h
    exact cechOpenFree_stalkCech_exact_succ X x U i hi n
  · apply HomologicalComplex.ExactAt.of_isZero
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro a
    have hx : x ∉ (∏ᶜ fun k : Fin (n + 2) => U (a k)) := by
      intro ha
      exact h ⟨a 0, (leOfHom (Pi.π (fun k : Fin (n + 2) => U (a k)) 0)) ha⟩
    exact (cechOpenFree_stalk_isZero_of_not_mem X x _ hx).op.eq_of_tgt _ _

/-- The actual additive open-free Cech chain complex, obtained by opposing mathlib's Cech
  functor. -/
abbrev additiveOpenFreeCechComplex {ι : Type u} (U : ι → Opens X) :=
  ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X).op).unop

/-- Stalkwise contraction proves exactness of the original open-free chain complex in positive
  degrees. -/
theorem additiveOpenFreeCechComplex_exact_succ {ι : Type u}
    (U : ι → Opens X) (n : ℕ) : (additiveOpenFreeCechComplex X U).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  have h := (cechOpenFree_stalkCech_exact_succ_any X x U n).of_iso
    (cechComplexCoefficientIso (cechStalkFunctor X x).op U
      (additiveOpenFreeFunctor X).op).symm
  exact h.unop

/-- The actual additive Hom presheaf on open-free generators is the coefficient sheaf's section
  presheaf. -/
def additiveOpenFreeYonedaIso
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (additiveOpenFreeFunctor X).op ⋙ preadditiveYoneda.obj A ≅ A.obj := by
  refine NatIso.ofComponents (fun U =>
    (additiveOpenHomAddEquiv X U.unop A).toAddCommGrpIso) ?_
  intro U V h
  ext f
  exact additiveOpenHomEquiv_naturality X h.unop A f

/-- Actual additive-injective coefficients have exact original Cech complexes in positive
  degrees, for every family of opens. -/
theorem additiveInjectiveCech_exact_succ
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective A]
    {ι : Type u} (U : ι → Opens X) (n : ℕ) :
    ((cechComplexFunctor U).obj A.obj).ExactAt (n + 1) := by
  let F := preadditiveYoneda.obj A
  let : F.PreservesHomology := by
    change (preadditiveYonedaObj A ⋙ forget₂ _ _).PreservesHomology
    infer_instance
  have h : ((F.mapHomologicalComplex _).obj
      ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X).op)).ExactAt (n + 1) :=
    (additiveOpenFreeCechComplex_exact_succ X U n).op.map F
  exact h.of_iso ((cechComplexCoefficientIso F U (additiveOpenFreeFunctor X).op) ≪≫
    (cechComplexFunctor U).mapIso (additiveOpenFreeYonedaIso X A))

end CechRows

section ResolutionNaturality

variable {X : TopCat.{u}}
variable {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A) {S : InjectiveResolution B} {f : A ⟶ B}

theorem resolutionSectionsCohomologyEquiv_mk (n : ℕ) (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionsCohomologyEquiv R n
      (QuotientAddGroup.mk' (resolutionSectionBoundary R n).range s) =
      resolutionSectionClass R (n + 1) s := by
  simp [resolutionSectionsCohomologyEquiv]
  rfl

/-- The cycle-class formula with the canonical quotient coercion on the left. -/
@[simp]
theorem resolutionSectionsCohomologyEquiv_coe (n : ℕ)
    (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionsCohomologyEquiv R n
      (s : resolutionSectionCycles R (n + 1) ⧸ (resolutionSectionBoundary R n).range) =
      resolutionSectionClass R (n + 1) s :=
  resolutionSectionsCohomologyEquiv_mk R n s

/-- The global-section short complex in degrees `n`, `n + 1`, and `n + 2`. -/
abbrev resolutionSectionShortComplex (n : ℕ) :=
  ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).sc'
    n (n + 1) (n + 2))

variable {R}
/-- The section short-complex map induced by a morphism of injective resolutions. -/
abbrev resolutionSectionShortComplexMap (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    resolutionSectionShortComplex R n ⟶ resolutionSectionShortComplex S n :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (.up ℕ) n (n + 1) (n + 2)).map
    (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom)

/-- Cycle and quotient maps realizing the induced map on actual `CategoryTheory.Sheaf.H`. -/
def resolutionSectionHomologyMapData (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    ShortComplex.LeftHomologyMapData (resolutionSectionShortComplexMap φ n)
      (resolutionSectionShortComplex R n).abLeftHomologyData
      (resolutionSectionShortComplex S n).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (resolutionSectionCyclesMap φ (n + 1))
  φH := AddCommGrpCat.ofHom
    ((resolutionSectionsCohomologyEquiv S n).symm.toAddMonoidHom.comp
      ((CategoryTheory.Sheaf.H.map f (n + 1)).comp (resolutionSectionsCohomologyEquiv R
        n).toAddMonoidHom))
  commi := by ext s; rfl
  commf' := by
    ext s
    apply Subtype.ext
    exact congrArg (fun g : R.cocomplex.X n ⟶ S.cocomplex.X (n + 1) =>
      g.hom.app (op ⊤) s) (φ.hom.comm n (n + 1)).symm
  commπ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply (resolutionSectionsCohomologyEquiv S n).injective
    change resolutionSectionsCohomologyEquiv S n
      ((resolutionSectionsCohomologyEquiv S n).symm
        (CategoryTheory.Sheaf.H.map f (n + 1) (resolutionSectionsCohomologyEquiv R n
          (QuotientAddGroup.mk' (resolutionSectionBoundary R n).range s)))) =
      resolutionSectionsCohomologyEquiv S n
        (QuotientAddGroup.mk' (resolutionSectionBoundary S n).range
          (resolutionSectionCyclesMap φ (n + 1) s))
    rw [AddEquiv.apply_symm_apply, resolutionSectionsCohomologyEquiv_mk,
      resolutionSectionsCohomologyEquiv_mk]
    exact resolutionSectionClass_naturality φ (n + 1) s

/-- Section short-complex homology identified with the original `CategoryTheory.Sheaf.H`. -/
def resolutionSectionShortHomologyEquiv (R : InjectiveResolution A) (n : ℕ) :
    (resolutionSectionShortComplex R n).homology ≃+ CategoryTheory.Sheaf.H.{u + 1} A (n + 1) :=
  (resolutionSectionShortComplex R n).abHomologyIso.addCommGroupIsoToAddEquiv.trans
    (resolutionSectionsCohomologyEquiv R n)

private theorem resolutionSectionShortHomologyEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : (resolutionSectionShortComplex R n).homology) :
    resolutionSectionShortHomologyEquiv S n
      (ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n) x) =
      CategoryTheory.Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n x) := by
  have h := congrArg (fun q => resolutionSectionsCohomologyEquiv S n (q.hom x))
    (resolutionSectionHomologyMapData φ n).homologyMap_comm
  change resolutionSectionShortHomologyEquiv S n
      (ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n) x) =
    resolutionSectionsCohomologyEquiv S n ((resolutionSectionsCohomologyEquiv S n).symm
      (CategoryTheory.Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n x))) at h
  simpa only [AddEquiv.apply_symm_apply] using h

/-- The actual resolution-homology comparison is natural for every lift of a coefficient map. -/
theorem additiveResolutionHomologyEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n
      + 1))) :
    additiveResolutionHomologyEquiv S n
      (HomologicalComplex.homologyMap
        (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) (n + 1) x) =
      CategoryTheory.Sheaf.H.map f (n + 1) (additiveResolutionHomologyEquiv R n x) := by
  let C := ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex
  let D := ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj S.cocomplex
  let g := ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom
  have hsc : HomologicalComplex.homologyMap g (n + 1) ≫
      (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n) := by
    simpa [HomologicalComplex.homologyFunctorIso', HomologicalComplex.homologyFunctorIso,
      HomologicalComplex.homologyIsoSc'] using
      (HomologicalComplex.homologyFunctorIso' AddCommGrpCat.{u} (.up ℕ)
        n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality g
  change resolutionSectionShortHomologyEquiv S n
    ((D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      (HomologicalComplex.homologyMap g (n + 1) x)) =
    CategoryTheory.Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n
      ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))
  rw [show (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      (HomologicalComplex.homologyMap g (n + 1) x) =
      ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n)
        ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x) from
      congrArg (fun q => q.hom x) hsc]
  exact resolutionSectionShortHomologyEquiv_naturality φ n _

end ResolutionNaturality

end TopCat.Sheaf.Cech
