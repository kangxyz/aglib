/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Augmentation
public import Aglib.Algebra.Homology.CochainComplex.Augmentation
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Category.Grp.AB
public import Aglib.Algebra.Homology.TotalComplex.AddCommGrp
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Affine
/-!
# Original Cech cohomology and canonical comparison with Sheaf.H

Mathlib's existing `Sheaf.H'` uses Ext from the free additive sheaf on an
open. At the whole space, its canonical identification with the unchanged
`Sheaf.H` is proved in every degree, with coefficient naturality, the actual
H⁰ normalization and compatibility with the original structural scalar action.

For every quasicoherent module sheaf and every affine open, positive-degree
`Sheaf.H'` vanishes. The proof uses actual open sections, flasque acyclicity
and the original native module-resolution kernel sequences. It assumes neither
injectivity of forgotten module injectives nor a cohomology-comparison family.

Actual additive-injective resolutions now supply exact Cech rows and exact
section columns on affine opens. Their positive global-section homology is
canonically identified with the original `Sheaf.H`, naturally for coefficient
resolution lifts and with the original scalar action. The actual Cech bicomplex
has canonical row and column augmentations, proved to be quasi-isomorphisms
under the open-cover and affine-intersection conditions, respectively. Both
augmentations commute with every coefficient-resolution lift. The genuine
first-quadrant total comparison identifies positive Cech homology of an affine
open cover in a separated scheme with the original `Sheaf.H`. This comparison
is independent of the additive injective resolution and preserves the original
structural scalar action. No finite generation assumption is used.

Actual inverse-image coefficient maps give geometric Cech maps, both geometric
augmentation squares, and the correct constant-sheaf map on resolution sections.
Identifying the induced positive-degree geometric comparison with the original
`zariskiCohomologyMap` still requires the exact-functor Ext/resolution-cycle
identity; proper positive-degree field base change is not asserted.

Source basis: project `34505bcad247d07872f5037e8fd0907debb08650`, including
AffineHigherComparison SHA-256 `0b65dba3f1a7082b0245031bbbe1a96d43346e5c3f1c33be446854c67b898593`;
Lean 4.34.1, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Quillen
`83629578a3d70787d41ec631f5234af8758716af`. The additive total transport is
`AdditiveFirstQuadrant.lean` SHA-256
`ce9f0268d99eb378e2205c1da4a21e88c7bc4c3fd942b18c8a405117951bbf8e`;
its author build/audit and the principal-owned independent review are separate
evidence stages.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.CechComparison` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable (X : Scheme.{u})

/-- The open-section representing equivalence is natural in the actual coefficient sheaf. -/
theorem additiveOpenHomEquiv_naturality_coefficient (U : X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : (additiveOpenFreeFunctor X).obj U ⟶ A) (g : A ⟶ B) :
    additiveOpenHomEquiv X U B (f ≫ g) =
      g.hom.app (op U) (additiveOpenHomEquiv X U A f) := by
  change yonedaEquiv ((additiveFreeAdjunction X).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

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

/-- The existing open-Ext cohomology on the whole space equals the original Sheaf.H. -/
def sheafHPrimeTopAddEquiv
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H'.{u + 1} A n ⊤ ≃+ Sheaf.H.{u + 1} A n :=
  (((Abelian.extFunctor n).mapIso (additiveOpenTopIsoInteger X).op).app
    A).symm.addCommGroupIsoToAddEquiv

/-- The whole-space comparison intertwines the existing coefficient maps in every degree. -/
theorem sheafHPrimeTopAddEquiv_naturality
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : A ⟶ B) (n : ℕ) (x : Sheaf.H'.{u + 1} A n ⊤) :
    sheafHPrimeTopAddEquiv X B n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app (op ⊤) x) =
      Sheaf.H.map f n (sheafHPrimeTopAddEquiv X A n x) := by
  exact congrArg (fun q => q.hom x)
    (((Abelian.extFunctor n).mapIso (additiveOpenTopIsoInteger X).op).inv.naturality f)

/-- In degree zero the comparison is normalized by the actual section-representing equivalences. -/
theorem sheafHPrimeTopAddEquiv_equiv₀
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : Sheaf.H'.{u + 1} A 0 ⊤) :
    Sheaf.H.equiv₀ A isTerminalTop (sheafHPrimeTopAddEquiv X A 0 x) =
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
    (T : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
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
    (T : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext.{u + 1} T S.X₂ (n + 1))]
    [Subsingleton (Ext.{u + 1} T S.X₃ n)] :
    Subsingleton (Ext.{u + 1} T S.X₁ (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x (Subsingleton.elim _ _) rfl
  exact hz.symm.trans (by rw [Subsingleton.elim z 0, Ext.zero_comp])

/-- Actual section lifting is exactly the lifting of maps from the open-free sheaf. -/
lemma openFree_postcomp_surjective_of_sections (U : X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : A ⟶ B)
    (hg : Function.Surjective (g.hom.app (op U))) :
    Function.Surjective (fun f : (additiveOpenFreeFunctor X).obj U ⟶ A => f ≫ g) := by
  intro q
  obtain ⟨s, hs⟩ := hg (additiveOpenHomEquiv X U B q)
  refine ⟨(additiveOpenHomEquiv X U A).symm s, ?_⟩
  apply (additiveOpenHomEquiv X U B).injective
  rw [additiveOpenHomEquiv_naturality_coefficient, Equiv.apply_symm_apply]
  exact hs

/-- A flasque additive sheaf is acyclic for the existing open-Ext cohomology on every open. -/
theorem subsingleton_sheafHPrime_of_isFlasque (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque A.obj] (n : ℕ) :
    Subsingleton (Sheaf.H'.{u + 1} A (n + 1) U) := by
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

open AlgebraicGeometry.Scheme.Modules.TwoOpen

/-- Exactness of actual resolution sections on an open lifts sections to the next native kernel. -/
theorem moduleResolution_openKernelSections_surjective {M : X.Modules}
    (I : InjectiveResolution M) (U : X.Opens) (n : ℕ)
    (hex : (((sectionsFunctor X U).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1)) :
    Function.Surjective
      (((AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X).map
        (CategoryTheory.InjectiveResolution.kernelSequence I n).g).hom.app (op U)) := by
  let G := sectionsFunctor X U
  let ι := kernel.ι (I.cocomplex.d (n + 1) (n + 2))
  have hi : Function.Injective (G.map ι) := by
    change Function.Injective
      (((SheafOfModules.toSheaf X.ringCatSheaf).map ι).hom.app (op U))
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro y
  have hy : G.map (I.cocomplex.d (n + 1) (n + 2)) (G.map ι y) = 0 := by
    change (G.map ι ≫ G.map (I.cocomplex.d (n + 1) (n + 2))) y = 0
    rw [← G.map_comp, kernel.condition, G.map_zero]
    rfl
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hex
  obtain ⟨x, hx⟩ := hex (G.map ι y) hy
  refine ⟨x, hi ?_⟩
  change (G.map (CategoryTheory.InjectiveResolution.kernelSequence I n).g ≫ G.map ι) x =
    G.map ι y
  rw [← G.map_comp]
  change G.map (kernel.lift (I.cocomplex.d (n + 1) (n + 2))
    (I.cocomplex.d n (n + 1)) _ ≫ kernel.ι _) x = _
  rw [kernel.lift_ι]
  exact hx

/-- The acyclic underlying terms compare native resolution section exactness with actual open
  Ext. -/
theorem subsingleton_sheafHPrime_of_moduleResolution_sections_exact
    {M : X.Modules} (I : InjectiveResolution M) (U : X.Opens)
    (hex : ∀ n : ℕ,
      (((sectionsFunctor X U).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1))
    (n : ℕ) : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) (n + 1) U) := by
  let T := (additiveOpenFreeFunctor X).obj U
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  have hmid (m k : ℕ) : Subsingleton (Ext.{u + 1} T (F.obj (I.cocomplex.X m)) (k + 1)) := by
    let : TopCat.Presheaf.IsFlasque (F.obj (I.cocomplex.X m)).obj :=
      AlgebraicGeometry.Scheme.Modules.injective_isFlasque X (I.cocomplex.X m)
    exact subsingleton_sheafHPrime_of_isFlasque U _ k
  have hk (k : ℕ) : ∀ m : ℕ,
      Subsingleton (Ext.{u + 1} T (F.obj (kernel (I.cocomplex.d m (m + 1)))) (k + 1)) := by
    induction k with
    | zero =>
      intro m
      let S := (CategoryTheory.InjectiveResolution.kernelSequence I m).map F
      have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I m)
      let : Subsingleton (Ext.{u + 1} T S.X₂ 1) := hmid m 0
      apply subsingleton_ext_one_of_shortExact T hS
      exact openFree_postcomp_surjective_of_sections U S.g
        (moduleResolution_openKernelSections_surjective I U m (hex m))
    | succ k ih =>
      intro m
      let S := (CategoryTheory.InjectiveResolution.kernelSequence I m).map F
      have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I m)
      let : Subsingleton (Ext.{u + 1} T S.X₂ (k + 1 + 1)) := hmid m (k + 1)
      let : Subsingleton (Ext.{u + 1} T S.X₃ (k + 1)) := ih (m + 1)
      exact subsingleton_ext_succ_of_shortExact T hS (k + 1)
  let S := (CategoryTheory.InjectiveResolution.initialSequence I).map F
  have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
    (CategoryTheory.InjectiveResolution.initialSequence_shortExact I)
  cases n with
  | zero =>
    let : Subsingleton (Ext.{u + 1} T S.X₂ 1) := hmid 0 0
    apply subsingleton_ext_one_of_shortExact T hS
    exact openFree_postcomp_surjective_of_sections U S.g
      (moduleResolution_openKernelSections_surjective I U 0 (hex 0))
  | succ n =>
    let : Subsingleton (Ext.{u + 1} T S.X₂ (n + 1 + 1)) := hmid 0 (n + 1)
    let : Subsingleton (Ext.{u + 1} T S.X₃ (n + 1)) := hk n 1
    exact subsingleton_ext_succ_of_shortExact T hS (n + 1)

/-- Actual positive open-Ext cohomology vanishes on an affine open for quasicoherent module
  coefficients. -/
theorem subsingleton_sheafHPrime_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) (n + 1) U) := by
  let I := injectiveResolution M
  apply subsingleton_sheafHPrime_of_moduleResolution_sections_exact I U _ n
  intro k
  simpa only [hU.opensRange_fromSpec] using
    AlgebraicGeometry.Scheme.Modules.affineOpen_injectiveResolution_exact_succ hU.fromSpec M I k

open AlgebraicGeometry.Scheme.OverField in
/-- The comparison uses exactly the scalar action induced by the original moduleScalar
  coefficient map. -/
theorem moduleHPrimeTopAddEquiv_scalar {F : Type u} [Field F]
    (X : FScheme F) (M : X.left.Modules) (a : F) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAddSheaf X.left M) n ⊤) :
    sheafHPrimeTopAddEquiv X.left (moduleAddSheaf X.left M) n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.left) n).map
        (moduleScalar X M a)).app (op ⊤) x) =
      a • (show moduleCohomology F X M n from
        sheafHPrimeTopAddEquiv X.left (moduleAddSheaf X.left M) n x) :=
  sheafHPrimeTopAddEquiv_naturality X.left (moduleScalar X M a) n x

variable (X : Scheme.{u})

/-- The open-section representing equivalence preserves the actual additive group structures. -/
def additiveOpenHomAddEquiv (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
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
abbrev additiveSectionsFunctor (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u}).obj (op U)

instance additiveSectionsFunctor_additive (U : X.Opens) :
    (additiveSectionsFunctor X U).Additive where
  map_add := by intros; rfl

variable {X}

/-- Vanishing of the actual open Ext group forces exactness of any actual additive-injective
  resolution on that open. -/
theorem additiveResolution_sections_exact_of_HPrime_zero
    {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (U : X.Opens) (n : ℕ)
    [Subsingleton (Sheaf.H'.{u + 1} A (n + 1) U)] :
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
    (inferInstance : Subsingleton (Sheaf.H'.{u + 1} A (n + 1) U)).elim _ _
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp hz
  refine ⟨additiveOpenHomAddEquiv X U _ g, ?_⟩
  change (R.cocomplex.d n (n + 1)).hom.app (op U)
    (additiveOpenHomEquiv X U _ g) = s
  rw [← additiveOpenHomEquiv_naturality_coefficient, hg]
  exact (additiveOpenHomAddEquiv X U _).apply_symm_apply s

/-- Every actual additive-injective resolution of quasicoherent coefficients is section-exact in
  positive degrees on affine opens. -/
theorem additiveResolution_sections_exact_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    (((additiveSectionsFunctor X U).mapHomologicalComplex _).obj R.cocomplex).ExactAt (n + 1) := by
  let := subsingleton_sheafHPrime_of_isAffineOpen M U hU n
  exact additiveResolution_sections_exact_of_HPrime_zero R U n

/-- Positive homology of the actual additive-injective resolution sections equals the original
  Sheaf.H, through the canonical cycles/boundaries quotient. -/
def additiveResolutionHomologyEquiv
    {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (n : ℕ) :
    ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n + 1)) ≃+
      Sheaf.H.{u + 1} A (n + 1) :=
  (((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).sc'
      n (n + 1) (n + 2)).abHomologyIso).addCommGroupIsoToAddEquiv.trans
        (resolutionSectionsCohomologyEquiv R n)

section CechRows

variable (X : Scheme.{u})
attribute [local instance] Classical.propDecidable

/-- The stalk functor on the actual additive sheaves of the scheme. -/
abbrev cechStalkFunctor (x : X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance cechStalkFunctor_isLeftAdjoint (x : X) :
    (cechStalkFunctor X x).IsLeftAdjoint :=
  (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).isLeftAdjoint

instance cechStalkFunctor_op_isRightAdjoint (x : X) :
    (cechStalkFunctor X x).op.IsRightAdjoint :=
  (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).op.isRightAdjoint

/-- The stalk-skyscraper adjunction composed with open-section representability. -/
def cechOpenStalkHomEquiv (x : X) (U : X.Opens) (B : AddCommGrpCat.{u}) :
    (((cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj U)) ⟶ B) ≃
      ((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.obj (op U) :=
  ((stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).homEquiv _ B).trans
    (additiveOpenHomEquiv X U _)

private theorem cechOpenStalkHomEquiv_naturality_open (x : X) {U V : X.Opens} (i : U ⟶ V)
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

private theorem cechSkyscraper_restrict_isIso (x : X) {U V : X.Opens} (i : U ⟶ V)
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

private theorem cechOpenFree_stalk_map_isIso (x : X) {U V : X.Opens} (i : U ⟶ V)
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

private theorem cechOpenFree_stalk_isZero_of_not_mem (x : X) (U : X.Opens) (hx : x ∉ U) :
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
    HasProducts.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})ᵒᵖ := by
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
    (U : ι → X.Opens) (i₀ : ι) (hx : x ∈ U i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X ⋙ cechStalkFunctor X x).op).ExactAt
      (n + 1) := by
  let Q := additiveOpenFreeFunctor X ⋙ cechStalkFunctor X x
  let p : Q.op ⟶ (intersectFunctor (U i₀)).op ⋙ Q.op :=
    NatTrans.op (Functor.whiskerRight (intersectToId (U i₀)) Q)
  have hp (V : X.Opensᵒᵖ) : IsIso (p.app V) := by
    change IsIso (((cechStalkFunctor X x).map ((additiveOpenFreeFunctor X).map
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)))).op)
    have := cechOpenFree_stalk_map_isIso X x
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)) (fun hv => ⟨hv, hx⟩)
    infer_instance
  let : IsIso p := NatIso.isIso_of_isIso_app p
  exact (restrictedCech_exactAt_succ U Q.op i₀ n).of_iso
    ((cechComplexFunctor U).mapIso (asIso p)).symm

private theorem cechOpenFree_stalkCech_exact_succ_any (x : X) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) :
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
abbrev additiveOpenFreeCechComplex {ι : Type u} (U : ι → X.Opens) :=
  ((cechComplexFunctor U).obj (additiveOpenFreeFunctor X).op).unop

/-- Stalkwise contraction proves exactness of the original open-free chain complex in positive
  degrees. -/
theorem additiveOpenFreeCechComplex_exact_succ {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (additiveOpenFreeCechComplex X U).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  have h := (cechOpenFree_stalkCech_exact_succ_any X x U n).of_iso
    (cechComplexCoefficientIso (cechStalkFunctor X x).op U
      (additiveOpenFreeFunctor X).op).symm
  exact h.unop

/-- The actual additive Hom presheaf on open-free generators is the coefficient sheaf's section
  presheaf. -/
def additiveOpenFreeYonedaIso
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (additiveOpenFreeFunctor X).op ⋙ preadditiveYoneda.obj A ≅ A.obj := by
  refine NatIso.ofComponents (fun U =>
    (additiveOpenHomAddEquiv X U.unop A).toAddCommGrpIso) ?_
  intro U V h
  ext f
  exact additiveOpenHomEquiv_naturality X h.unop A f

/-- Actual additive-injective coefficients have exact original Cech complexes in positive
  degrees, for every family of opens. -/
theorem additiveInjectiveCech_exact_succ
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective A]
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
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

variable {X : Scheme.{u}}
variable {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
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

/-- Cycle and quotient maps realizing the induced map on actual `Sheaf.H`. -/
def resolutionSectionHomologyMapData (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    ShortComplex.LeftHomologyMapData (resolutionSectionShortComplexMap φ n)
      (resolutionSectionShortComplex R n).abLeftHomologyData
      (resolutionSectionShortComplex S n).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (resolutionSectionCyclesMap φ (n + 1))
  φH := AddCommGrpCat.ofHom
    ((resolutionSectionsCohomologyEquiv S n).symm.toAddMonoidHom.comp
      ((Sheaf.H.map f (n + 1)).comp (resolutionSectionsCohomologyEquiv R n).toAddMonoidHom))
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
        (Sheaf.H.map f (n + 1) (resolutionSectionsCohomologyEquiv R n
          (QuotientAddGroup.mk' (resolutionSectionBoundary R n).range s)))) =
      resolutionSectionsCohomologyEquiv S n
        (QuotientAddGroup.mk' (resolutionSectionBoundary S n).range
          (resolutionSectionCyclesMap φ (n + 1) s))
    rw [AddEquiv.apply_symm_apply, resolutionSectionsCohomologyEquiv_mk,
      resolutionSectionsCohomologyEquiv_mk]
    exact resolutionSectionClass_naturality φ (n + 1) s

/-- Section short-complex homology identified with the original `Sheaf.H`. -/
def resolutionSectionShortHomologyEquiv (R : InjectiveResolution A) (n : ℕ) :
    (resolutionSectionShortComplex R n).homology ≃+ Sheaf.H.{u + 1} A (n + 1) :=
  (resolutionSectionShortComplex R n).abHomologyIso.addCommGroupIsoToAddEquiv.trans
    (resolutionSectionsCohomologyEquiv R n)

private theorem resolutionSectionShortHomologyEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : (resolutionSectionShortComplex R n).homology) :
    resolutionSectionShortHomologyEquiv S n
      (ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n) x) =
      Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n x) := by
  have h := congrArg (fun q => resolutionSectionsCohomologyEquiv S n (q.hom x))
    (resolutionSectionHomologyMapData φ n).homologyMap_comm
  change resolutionSectionShortHomologyEquiv S n
      (ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n) x) =
    resolutionSectionsCohomologyEquiv S n ((resolutionSectionsCohomologyEquiv S n).symm
      (Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n x))) at h
  simpa only [AddEquiv.apply_symm_apply] using h

/-- The actual resolution-homology comparison is natural for every lift of a coefficient map. -/
theorem additiveResolutionHomologyEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n
      + 1))) :
    additiveResolutionHomologyEquiv S n
      (HomologicalComplex.homologyMap
        (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) (n + 1) x) =
      Sheaf.H.map f (n + 1) (additiveResolutionHomologyEquiv R n x) := by
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
    Sheaf.H.map f (n + 1) (resolutionSectionShortHomologyEquiv R n
      ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))
  rw [show (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      (HomologicalComplex.homologyMap g (n + 1) x) =
      ShortComplex.homologyMap (resolutionSectionShortComplexMap φ n)
        ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x) from
      congrArg (fun q => q.hom x) hsc]
  exact resolutionSectionShortHomologyEquiv_naturality φ n _

open AlgebraicGeometry.Scheme.OverField in
/-- Any actual lift of the original moduleScalar map acts on resolution homology as the
  unchanged structural scalar. -/
theorem module_additiveResolutionHomologyEquiv_scalar {F : Type u} [Field F]
    (X : FScheme F) (M : X.left.Modules) (R : InjectiveResolution (moduleAddSheaf X.left M))
    (a : F) (φ : InjectiveResolution.Hom R R (moduleScalar X M a)) (n : ℕ)
    (x : ((((additiveSectionsFunctor X.left ⊤).mapHomologicalComplex _).obj
      R.cocomplex).homology (n + 1))) :
    additiveResolutionHomologyEquiv R n
      (HomologicalComplex.homologyMap
        (((additiveSectionsFunctor X.left ⊤).mapHomologicalComplex _).map φ.hom) (n + 1) x) =
      a • (show moduleCohomology F X M (n + 1) from additiveResolutionHomologyEquiv R n x) :=
  additiveResolutionHomologyEquiv_naturality φ n x

end ResolutionNaturality

section CechAugmentation
open CategoryTheory.Cech HomologicalComplex
universe v
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)


section Additive
variable (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Restriction of additive sections along an inclusion of opens. -/
abbrev aRes {V W : X.Opens} (h : V ≤ W) :=
  (A.obj.map (homOfLE h).op).hom

private theorem aRes_comp {V W T : X.Opens} (h : V ≤ W) (k : W ≤ T)
    (s : A.obj.obj (op T)) : aRes X A h (aRes X A k s) = aRes X A (h.trans k) s := by
  change (A.obj.map (homOfLE k).op ≫ A.obj.map (homOfLE h).op) s = _
  rw [← A.obj.map_comp]
  rfl

private theorem aRes_component_congr
    (z : ((cechComplexFunctor U).obj A.obj).X 0)
    {a a' : Fin 1 → ι} (e : a = a') {V : X.Opens}
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
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' (X := X.toTopCat) A U ⊤ (fun _ =>
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
  apply TopCat.Sheaf.eq_of_locally_eq' (X := X.toTopCat) A U ⊤ (fun _ => homOfLE le_top) hU.ge s t
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
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

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
def additiveCechFunctor : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CochainComplex AddCommGrpCat.{u} ℕ :=
  sheafToPresheaf _ _ ⋙ cechComplexFunctor U

instance : (additiveCechFunctor X U).Additive := by
  dsimp [additiveCechFunctor]
  infer_instance

/-- The functor concentrating the second degree of an additive bicomplex in zero. -/
abbrev additiveCechSingleSecondZero :=
  (CochainComplex.single₀ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)

variable {X} {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
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
def cechTupleOpens (p : ℕ) : Discrete (Fin (p + 1) → ι) ⥤ X.Opensᵒᵖ :=
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

/-- Products of the genuine affine-open resolution columns are exact in positive degrees. -/
theorem additiveCechResolution_column_exact_succ
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (p n : ℕ) : ((additiveCechResolution U R).X p).ExactAt (n + 1) := by
  let G := additiveCechSectionFamilyFunctor X U p
  let T := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  have hT : T.ExactAt (n + 1) := by
    rw [exactAt_iff_isZero_homology]
    apply Functor.isZero
    intro a
    let E := (CategoryTheory.evaluation (Discrete (Fin (p + 1) → ι)) AddCommGrpCat.{u}).obj a
    have h := additiveResolution_sections_exact_of_isAffineOpen M R _ (hU p a.as) n
    exact h.isZero_homology.of_iso ((T.sc (n + 1)).mapHomologyIso E).symm
  have hprod : ((lim.mapHomologicalComplex (.up ℕ)).obj T).ExactAt (n + 1) :=
    hT.map (lim (J := Discrete (Fin (p + 1) → ι)) (C := AddCommGrpCat.{u}))
  let e : (((additiveCechDegreeFunctor X U p).mapHomologicalComplex _).obj R.cocomplex) ≅
      ((lim.mapHomologicalComplex (.up ℕ)).obj T) :=
    (NatIso.mapHomologicalComplex (additiveCechDegreeIsoLimit X U p) _).app R.cocomplex ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ lim)) _).app R.cocomplex).symm
  exact hprod.of_iso e.symm

/-- For a quasicoherent coefficient and affine tuple intersections, the actual column
  augmentations are quasi-isomorphisms. -/
theorem additiveCechColumnAugmentation_quasiIso
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (p : ℕ) : QuasiIso ((additiveCechColumnAugmentation U R).f p) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact additiveCechColumnAugmentation_quasiIsoAt_zero U R p
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n)]
    exact additiveCechResolution_column_exact_succ U M R hU p n

section Naturality
variable {U} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
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
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
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
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    QuasiIso (additiveCechToTotal U R) :=
  quasiIso_totalAugmentation _ (additiveCechColumnAugmentation_quasiIso U M R hU)

section Naturality
variable {U R} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
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

variable (M : X.Modules) [M.IsQuasicoherent]
variable (R : InjectiveResolution (moduleAddSheaf X M))
variable (hcover : iSup U = ⊤)
variable (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))

/-- The two genuine augmentations compare original Cech homology with actual additive-resolution
  sections. -/
def moduleCechResolutionHomologyIso (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology n ≅
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology n := by
  have := additiveCechToTotal_quasiIso U M R haff
  have := additiveResolutionSectionsToTotal_quasiIso U R hcover
  exact asIso (homologyMap (additiveCechToTotal U R) n) ≪≫
    (asIso (homologyMap (additiveResolutionSectionsToTotal U R) n)).symm

@[reassoc (attr := simp)]
theorem moduleCechResolutionHomologyIso_hom_comp (n : ℕ) :
    (moduleCechResolutionHomologyIso U M R hcover haff n).hom ≫
      homologyMap (additiveResolutionSectionsToTotal U R) n =
        homologyMap (additiveCechToTotal U R) n := by
  unfold moduleCechResolutionHomologyIso
  simp

variable {M R} {N : X.Modules} [N.IsQuasicoherent]
  {S : InjectiveResolution (moduleAddSheaf X N)}
  {f : moduleAddSheaf X M ⟶ moduleAddSheaf X N}

theorem moduleCechResolutionHomologyIso_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    homologyMap ((additiveCechFunctor X U).map f) n ≫
      (moduleCechResolutionHomologyIso U N S hcover haff n).hom =
    (moduleCechResolutionHomologyIso U M R hcover haff n).hom ≫
      homologyMap (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) n := by
  have := additiveResolutionSectionsToTotal_quasiIso U S hcover
  apply (cancel_mono (homologyMap (additiveResolutionSectionsToTotal U S) n)).mp
  have hc := congrArg (fun g => homologyMap g n) (additiveCechToTotal_naturality (U := U) φ)
  have hr := congrArg (fun g => homologyMap g n)
    (additiveResolutionSectionsToTotal_naturality (U := U) φ)
  simp only [homologyMap_comp] at hc hr
  rw [Category.assoc, moduleCechResolutionHomologyIso_hom_comp,
    Category.assoc, hr, ← Category.assoc, moduleCechResolutionHomologyIso_hom_comp]
  exact hc

variable (M R)

/-- Positive-degree original Sheaf.H computed by the original Cech complex of an
  affine-intersection open cover. -/
def moduleCechCohomologyAddEquiv (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1) ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) :=
  (moduleCechResolutionHomologyIso U M R hcover haff (n + 1)).addCommGroupIsoToAddEquiv.trans
    (additiveResolutionHomologyEquiv R n)

variable {M R}

/-- The Cech comparison respects every coefficient map and every additive-resolution lift. -/
theorem moduleCechCohomologyAddEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1)) :
    moduleCechCohomologyAddEquiv U N S hcover haff n
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x) =
    Sheaf.H.map f (n + 1) (moduleCechCohomologyAddEquiv U M R hcover haff n x) := by
  have h := ConcreteCategory.congr_hom
    (moduleCechResolutionHomologyIso_naturality U hcover haff φ (n + 1)) x
  change additiveResolutionHomologyEquiv S n
    ((moduleCechResolutionHomologyIso U N S hcover haff (n + 1)).hom
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x)) = _
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  exact additiveResolutionHomologyEquiv_naturality φ n _

/-- The comparison is independent of the chosen additive injective resolution. -/
theorem moduleCechCohomologyAddEquiv_independent
    (M : X.Modules) [M.IsQuasicoherent]
    (R S : InjectiveResolution (moduleAddSheaf X M)) (n : ℕ) :
    moduleCechCohomologyAddEquiv U M R hcover haff n =
      moduleCechCohomologyAddEquiv U M S hcover haff n := by
  let φ : InjectiveResolution.Hom R S (𝟙 (moduleAddSheaf X M)) :=
    ⟨InjectiveResolution.desc (𝟙 _) S R,
      by simp⟩
  ext x
  have h := moduleCechCohomologyAddEquiv_naturality U hcover haff φ n x
  erw [(additiveCechFunctor X U).map_id, homologyMap_id] at h
  simpa only [ConcreteCategory.id_apply, Sheaf.H.map_id_apply] using h.symm

open AlgebraicGeometry.Scheme.OverField in
/-- Cech cohomology carries the unchanged structural scalar action under the comparison. -/
theorem moduleCechCohomologyAddEquiv_scalar {F : Type u} [Field F]
    (X : FScheme F) (M : X.left.Modules) [M.IsQuasicoherent]
    (R : InjectiveResolution (moduleAddSheaf X.left M))
    {ι : Type u} (U : ι → X.left.Opens) (hcover : iSup U = ⊤)
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (a : F) (φ : InjectiveResolution.Hom R R (moduleScalar X M a)) (n : ℕ)
    (x : ((additiveCechFunctor X.left U).obj (moduleAddSheaf X.left M)).homology (n + 1)) :
    moduleCechCohomologyAddEquiv U M R hcover haff n
      (homologyMap ((additiveCechFunctor X.left U).map (moduleScalar X M a)) (n + 1) x) =
    a • (show moduleCohomology F X M (n + 1) from
      moduleCechCohomologyAddEquiv U M R hcover haff n x) :=
  moduleCechCohomologyAddEquiv_naturality U hcover haff φ n x

/-- An affine open cover of a separated scheme computes the original positive-degree module
  cohomology. -/
def moduleAffineCechCohomologyAddEquiv {X : Scheme.{u}} [X.IsSeparated]
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (haff : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent]
    (R : InjectiveResolution (moduleAddSheaf X M)) (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1) ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) :=
  moduleCechCohomologyAddEquiv U M R hcover (fun p a => by
    have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
      apply le_antisymm
      · exact le_iInf fun k => leOfHom (Limits.Pi.π _ k)
      · exact leOfHom (Limits.Pi.lift fun k => homOfLE (iInf_le _ k))
    rw [he]
    exact IsAffineOpen.iInf (fun k => haff (a k))) n

end CechTotalComparison

section CechGeometricNaturality
open HomologicalComplex HomologicalComplex₂ CategoryTheory.Cech
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)

instance zariskiPushforward_additive : (zariskiPushforward f).Additive where
  map_add := by intros; rfl

/-- Preimage of the actual family gives the same additive Cech complex as pushforward
  coefficients. -/
def additiveCechPushforwardIso :
    zariskiPushforward f ⋙ additiveCechFunctor Y U ≅
      additiveCechFunctor X (fun i => f ⁻¹ᵁ U i) := by
  refine NatIso.ofComponents (fun B =>
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (cechCosimplicialChangeIso (Opens.map f.base) U B.obj)) ?_
  intro A B g
  ext n : 1
  apply Pi.hom_ext
  intro a
  dsimp [additiveCechFunctor, cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, cechCosimplicialChangeIso]
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.map_π, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, Pi.map_π_assoc, Pi.mapIso_hom_π_assoc]
  congr 1
  exact (g.hom.naturality _).symm

/-- The original additive Cech morphism induced by an actual inverse-image coefficient map. -/
def additiveCechGeometricMap
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) :
    (additiveCechFunctor Y U).obj A ⟶
      (additiveCechFunctor X (fun i => f ⁻¹ᵁ U i)).obj B :=
  (additiveCechFunctor Y U).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _ a) ≫
      (additiveCechPushforwardIso f U).hom.app B

theorem additiveCechPushforwardIso_augmentation
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    cechAugmentation Y U ((zariskiPushforward f).obj B).obj ≫
      (additiveCechPushforwardIso f U).hom.app B =
    (CochainComplex.single₀ AddCommGrpCat.{u}).map ((pushforwardSectionsIso f).hom.app B) ≫
      cechAugmentation X (fun i => f ⁻¹ᵁ U i) B.obj := by
  apply from_single_hom_ext
  simp only [comp_f, cechAugmentation_f_zero, CochainComplex.single₀_map_f_zero]
  apply Pi.hom_ext (f := fun b : Fin 1 → ι =>
    B.obj.obj (op (∏ᶜ fun k => f ⁻¹ᵁ U (b k))))
  intro a
  dsimp [additiveCechPushforwardIso, cechCosimplicialChangeIso,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  simp only [Category.assoc]
  erw [Pi.mapIso_hom_π]
  simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv]
  erw [cechAugmentationZero_π_assoc, cechAugmentationZero_π]
  dsimp [pushforwardSectionsIso]
  rw [← B.obj.map_comp, ← B.obj.map_comp]
  rfl

theorem additiveCechGeometricMap_naturality
    {A A' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {B B' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (zariskiPullback f).obj A ⟶ B) (a' : (zariskiPullback f).obj A' ⟶ B')
    (g : A ⟶ A') (h : B ⟶ B') (w : (zariskiPullback f).map g ≫ a' = a ≫ h) :
    (additiveCechFunctor Y U).map g ≫ additiveCechGeometricMap f U A' B' a' =
      additiveCechGeometricMap f U A B a ≫ (additiveCechFunctor X (fun i => f ⁻¹ᵁ U i)).map h := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  have hw : g ≫ adj.homEquiv _ _ a' = adj.homEquiv _ _ a ≫ (zariskiPushforward f).map h := by
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right, w]
  dsimp only [additiveCechGeometricMap]
  rw [← Category.assoc, ← Functor.map_comp, hw, Functor.map_comp, Category.assoc]
  exact congrArg (fun k => (additiveCechFunctor Y U).map (adj.homEquiv _ _ a) ≫ k)
    ((additiveCechPushforwardIso f U).hom.naturality h)

/-- The cochain adjoint of a genuine map from the exact inverse-image resolution. -/
def adjointCochainMap
    {R : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ}
    {S : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ}
    (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R ⟶ S) :
    R ⟶ ((zariskiPushforward f).mapHomologicalComplex _).obj S where
  f n := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _ (φ.f n)
  comm' i j _ := by
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
    change adj.homEquiv _ _ (φ.f i) ≫ (zariskiPushforward f).map (S.d i j) =
      R.d i j ≫ adj.homEquiv _ _ (φ.f j)
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) (φ.comm i j)

/-- The corresponding actual map on global resolution-section complexes. -/
def geometricResolutionSectionsMap
    {R : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ}
    {S : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ}
    (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R ⟶ S) :
    ((additiveSectionsFunctor Y ⊤).mapHomologicalComplex _).obj R ⟶
      ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj S :=
  ((additiveSectionsFunctor Y ⊤).mapHomologicalComplex _).map (adjointCochainMap f φ) ≫
    (NatTrans.mapHomologicalComplex (pushforwardSectionsIso f).hom _).app S

variable {A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
  {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  (R : InjectiveResolution A) (S : InjectiveResolution B)
  (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R.cocomplex ⟶ S.cocomplex)

/-- The actual map of Cech-resolution bicomplexes induced by a geometric resolution lift. -/
def geometricCechResolutionMap :
    additiveCechResolution U R ⟶ additiveCechResolution (fun i => f ⁻¹ᵁ U i) S :=
  (flipFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ)).map
    (((additiveCechFunctor Y U).mapHomologicalComplex _).map (adjointCochainMap f φ) ≫
      (NatTrans.mapHomologicalComplex (additiveCechPushforwardIso f U).hom _).app S.cocomplex)

/-- The actual geometric map commutes with the row restriction augmentation. -/
theorem geometricCechRowAugmentation_naturality :
    additiveCechSingleSecondZero.map (geometricResolutionSectionsMap f φ) ≫
      additiveCechRowAugmentation (fun i => f ⁻¹ᵁ U i) S =
    additiveCechRowAugmentation U R ≫
      (flipFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ)).map
        (geometricCechResolutionMap f U R S φ) := by
  ext q : 1
  change (CochainComplex.single₀ AddCommGrpCat.{u}).map
      (((adjointCochainMap f φ).f q).hom.app (op ⊤) ≫
        (pushforwardSectionsIso f).hom.app (S.cocomplex.X q)) ≫
      cechAugmentation X (fun i => f ⁻¹ᵁ U i) (S.cocomplex.X q).obj =
    cechAugmentation Y U (R.cocomplex.X q).obj ≫
      ((cechComplexFunctor U).map ((adjointCochainMap f φ).f q).hom ≫
        (additiveCechPushforwardIso f U).hom.app (S.cocomplex.X q))
  rw [Functor.map_comp, Category.assoc, ← additiveCechPushforwardIso_augmentation,
    ← Category.assoc]
  erw [cechAugmentation_naturality Y U ((adjointCochainMap f φ).f q).hom]
  rw [Category.assoc]

/-- The actual geometric map commutes with the column augmentation when the
  coefficient-to-resolution square commutes. -/
theorem geometricCechColumnAugmentation_naturality
    (a : (zariskiPullback f).obj A ⟶ B)
    (hφ : (zariskiPullback f).map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0) :
    additiveCechSingleSecondZero.map (additiveCechGeometricMap f U A B a) ≫
      additiveCechColumnAugmentation (fun i => f ⁻¹ᵁ U i) S =
    additiveCechColumnAugmentation U R ≫ geometricCechResolutionMap f U R S φ := by
  ext p : 1
  apply from_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero, additiveCechColumnAugmentation_f_zero]
  exact congrArg (fun g => g.f p)
    (additiveCechGeometricMap_naturality f U a (φ.f 0) (R.ι.f 0) (S.ι.f 0) hφ).symm

/-- The original constant-sheaf transport gives the actual adjoint map on sections. -/
theorem integerSheafHomEquiv_geometric
    (a : (zariskiPullback f).obj A ⟶ B)
    (s : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ A) :
    integerSheafHomEquiv B ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
      (zariskiPullback f).map s ≫ a) =
    (pushforwardSectionsIso f).hom.app B
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _
        a).hom.app
        (op ⊤) (integerSheafHomEquiv A s)) := by
  let x : Sheaf.H.{u + 1} A 0 := Abelian.Ext.mk₀ s
  have h := zariskiCohomologyMap_equiv₀ f A B a x
  change integerSheafHomEquiv B (Abelian.Ext.addEquiv₀ (zariskiCohomologyMap f A B a 0 x)) =
    (pushforwardSectionsIso f).hom.app B
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _
        a).hom.app
        (op ⊤) (integerSheafHomEquiv A (Abelian.Ext.addEquiv₀ x))) at h
  rw [zariskiCohomologyMap_addEquiv₀,
    show Abelian.Ext.addEquiv₀ x = s from Abelian.Ext.addEquiv₀.right_inv s] at h
  exact h

/-- On every resolution term the constant-Ext comparison is the literal section map of the
  adjoint lift. -/
theorem geometricResolutionSectionsMap_integerHom (n : ℕ)
    (s : (R.cocomplex.X n).obj.obj (op ⊤)) :
    integerSheafHomEquiv (S.cocomplex.X n)
      ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback f).map ((integerSheafHomEquiv (R.cocomplex.X n)).symm s) ≫ φ.f n) =
      (geometricResolutionSectionsMap f φ).f n s := by
  rw [integerSheafHomEquiv_geometric, AddEquiv.apply_symm_apply]
  rfl

end CechGeometricNaturality

end AlgebraicGeometry.Scheme.Cohomology
