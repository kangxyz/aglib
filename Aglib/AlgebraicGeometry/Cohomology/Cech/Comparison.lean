/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Comparison
public import Aglib.Topology.Sheaves.Cech.Cocycles
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
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.DegreeZero
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-!
# Scheme applications of the original topological Cech comparison

The topological producers preserve the literal Cech complex and both total
augmentations. This Scheme layer supplies quasicoherent affine acyclicity and
retains the original geometric maps and compatibility names.

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
The exact-functor Ext/resolution-cycle identity and geometric compatibility with
the original `zariskiCohomologyMap` are supplied in `Cech.Geometric`.

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
      g.hom.app (op U) (additiveOpenHomEquiv X U A f) :=
  TopCat.Sheaf.Cech.additiveOpenHomEquiv_naturality_coefficient X.toTopCat U f g

/-- The free additive sheaf on the whole space is canonically the constant integer sheaf. -/
abbrev additiveOpenTopIsoInteger : (additiveOpenFreeFunctor X).obj ⊤ ≅
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  TopCat.Sheaf.Cech.additiveOpenTopIsoInteger X.toTopCat

/-- The existing open-Ext cohomology on the whole space equals the original Sheaf.H. -/
def sheafHPrimeTopAddEquiv
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H'.{u + 1} A n ⊤ ≃+ Sheaf.H.{u + 1} A n :=
  TopCat.Sheaf.Cech.sheafHPrimeTopAddEquiv X.toTopCat A n

/-- The whole-space comparison intertwines the existing coefficient maps in every degree. -/
theorem sheafHPrimeTopAddEquiv_naturality
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : A ⟶ B) (n : ℕ) (x : Sheaf.H'.{u + 1} A n ⊤) :
    sheafHPrimeTopAddEquiv X B n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app (op ⊤) x) =
      Sheaf.H.map f n (sheafHPrimeTopAddEquiv X A n x) :=
  TopCat.Sheaf.Cech.sheafHPrimeTopAddEquiv_naturality X.toTopCat f n x

/-- In degree zero the comparison is normalized by the actual section-representing equivalences. -/
theorem sheafHPrimeTopAddEquiv_equiv₀
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : Sheaf.H'.{u + 1} A 0 ⊤) :
    Sheaf.H.equiv₀ A isTerminalTop (sheafHPrimeTopAddEquiv X A 0 x) =
      additiveOpenHomEquiv X ⊤ A (Abelian.Ext.addEquiv₀ x) :=
  TopCat.Sheaf.Cech.sheafHPrimeTopAddEquiv_equiv₀ X.toTopCat A x

variable {X}
open CategoryTheory.Abelian

/-- Hom lifting and vanishing in the middle term kill the first Ext group. -/
lemma subsingleton_ext_one_of_shortExact
    (T : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Subsingleton (Ext.{u + 1} T S.X₂ 1)]
    (hs : Function.Surjective (fun f : T ⟶ S.X₂ => f ≫ S.g)) :
    Subsingleton (Ext.{u + 1} T S.X₁ 1) :=
  TopCat.Sheaf.Cech.subsingleton_ext_one_of_shortExact (X := X.toTopCat) T hS hs

/-- Dimension shifting through a short exact sequence with the indicated actual Ext groups zero. -/
lemma subsingleton_ext_succ_of_shortExact
    (T : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext.{u + 1} T S.X₂ (n + 1))]
    [Subsingleton (Ext.{u + 1} T S.X₃ n)] :
    Subsingleton (Ext.{u + 1} T S.X₁ (n + 1)) :=
  TopCat.Sheaf.Cech.subsingleton_ext_succ_of_shortExact (X := X.toTopCat) T hS n

/-- Actual section lifting is exactly the lifting of maps from the open-free sheaf. -/
lemma openFree_postcomp_surjective_of_sections (U : X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : A ⟶ B)
    (hg : Function.Surjective (g.hom.app (op U))) :
    Function.Surjective (fun f : (additiveOpenFreeFunctor X).obj U ⟶ A => f ≫ g) :=
  TopCat.Sheaf.Cech.openFree_postcomp_surjective_of_sections (X := X.toTopCat) U g hg

/-- A flasque additive sheaf is acyclic for the existing open-Ext cohomology on every open. -/
theorem subsingleton_sheafHPrime_of_isFlasque (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque A.obj] (n : ℕ) :
    Subsingleton (Sheaf.H'.{u + 1} A (n + 1) U) :=
  TopCat.Sheaf.Cech.subsingleton_sheafHPrime_of_isFlasque (X := X.toTopCat) U A n

open AlgebraicGeometry.Scheme.Modules.TwoOpen

section ModuleResolutionSections

/-- Use the original evaluator's preservation witness at the actual category and zero structures. -/
private theorem moduleSections_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens)
    [sourceZero : HasZeroMorphisms X.Modules]
    [targetZero : HasZeroMorphisms AddCommGrpCat.{u}] :
    @Functor.PreservesZeroMorphisms X.Modules inferInstance
      AddCommGrpCat.{u} inferInstance sourceZero targetZero (sectionsFunctor X U) := by
  exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms X.ringCatSheaf (op U)
    (sourceZero := sourceZero) (targetZero := targetZero)

attribute [local instance] moduleSections_preservesZeroMorphisms

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
  let : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
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

end ModuleResolutionSections

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
abbrev additiveOpenHomAddEquiv (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((additiveOpenFreeFunctor X).obj U ⟶ A) ≃+ A.obj.obj (op U) :=
  TopCat.Sheaf.Cech.additiveOpenHomAddEquiv X.toTopCat U A

/-- Actual evaluation of additive sheaves on the indicated open. -/
abbrev additiveSectionsFunctor (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.Cech.additiveSectionsFunctor X.toTopCat U

instance additiveSectionsFunctor_additive (U : X.Opens) :
    (additiveSectionsFunctor X U).Additive :=
  TopCat.Sheaf.Cech.additiveSectionsFunctor_additive X.toTopCat U

variable {X}

/-- Vanishing of the actual open Ext group forces exactness of any actual additive-injective
  resolution on that open. -/
theorem additiveResolution_sections_exact_of_HPrime_zero
    {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (U : X.Opens) (n : ℕ)
    [h : Subsingleton (Sheaf.H'.{u + 1} A (n + 1) U)] :
    (((additiveSectionsFunctor X U).mapHomologicalComplex _).obj R.cocomplex).ExactAt (n + 1) :=
  @TopCat.Sheaf.Cech.additiveResolution_sections_exact_of_HPrime_zero X.toTopCat A R U n h

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
abbrev additiveResolutionHomologyEquiv
    {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (R : InjectiveResolution A) (n : ℕ) :
    ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n + 1)) ≃+
      Sheaf.H.{u + 1} A (n + 1) :=
  TopCat.Sheaf.Cech.additiveResolutionHomologyEquiv (X := X.toTopCat) R n

section CechRows

variable (X : Scheme.{u})
attribute [local instance] Classical.propDecidable

/-- The stalk functor on the actual additive sheaves of the scheme. -/
abbrev cechStalkFunctor (x : X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.Cech.cechStalkFunctor X.toTopCat x

instance cechStalkFunctor_isLeftAdjoint (x : X) :
    (cechStalkFunctor X x).IsLeftAdjoint :=
  TopCat.Sheaf.Cech.cechStalkFunctor_isLeftAdjoint X.toTopCat x

instance cechStalkFunctor_op_isRightAdjoint (x : X) :
    (cechStalkFunctor X x).op.IsRightAdjoint :=
  TopCat.Sheaf.Cech.cechStalkFunctor_op_isRightAdjoint X.toTopCat x

/-- The stalk-skyscraper adjunction composed with open-section representability. -/
abbrev cechOpenStalkHomEquiv (x : X) (U : X.Opens) (B : AddCommGrpCat.{u}) :
    (((cechStalkFunctor X x).obj ((additiveOpenFreeFunctor X).obj U)) ⟶ B) ≃
      ((skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).obj B).obj.obj (op U) :=
  TopCat.Sheaf.Cech.cechOpenStalkHomEquiv X.toTopCat x U B

open CategoryTheory.Cech

instance cechSheaf_op_hasProducts :
    HasProducts.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})ᵒᵖ :=
  TopCat.Sheaf.Cech.cechSheaf_op_hasProducts X.toTopCat

instance cechStalkFunctor_additive (x : X) :
    (cechStalkFunctor X x).Additive :=
  TopCat.Sheaf.Cech.cechStalkFunctor_additive X.toTopCat x

instance cechStalkFunctor_op_additive (x : X) :
    (cechStalkFunctor X x).op.Additive :=
  TopCat.Sheaf.Cech.cechStalkFunctor_op_additive X.toTopCat x

/-- The actual additive open-free Cech chain complex, obtained by opposing mathlib's Cech
  functor. -/
abbrev additiveOpenFreeCechComplex {ι : Type u} (U : ι → X.Opens) :=
  TopCat.Sheaf.Cech.additiveOpenFreeCechComplex X.toTopCat U

/-- Stalkwise contraction proves exactness of the original open-free chain complex in positive
  degrees. -/
theorem additiveOpenFreeCechComplex_exact_succ {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (additiveOpenFreeCechComplex X U).ExactAt (n + 1) :=
  TopCat.Sheaf.Cech.additiveOpenFreeCechComplex_exact_succ X.toTopCat U n

/-- The actual additive Hom presheaf on open-free generators is the coefficient sheaf's section
  presheaf. -/
abbrev additiveOpenFreeYonedaIso
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (additiveOpenFreeFunctor X).op ⋙ preadditiveYoneda.obj A ≅ A.obj :=
  TopCat.Sheaf.Cech.additiveOpenFreeYonedaIso X.toTopCat A

/-- Actual additive-injective coefficients have exact original Cech complexes in positive
  degrees, for every family of opens. -/
theorem additiveInjectiveCech_exact_succ
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective A]
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((cechComplexFunctor U).obj A.obj).ExactAt (n + 1) :=
  TopCat.Sheaf.Cech.additiveInjectiveCech_exact_succ X.toTopCat A U n

end CechRows

section ResolutionNaturality

variable {X : Scheme.{u}}
variable {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A) {S : InjectiveResolution B} {f : A ⟶ B}

theorem resolutionSectionsCohomologyEquiv_mk (n : ℕ) (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionsCohomologyEquiv R n
      (QuotientAddGroup.mk' (resolutionSectionBoundary R n).range s) =
      resolutionSectionClass R (n + 1) s :=
  TopCat.Sheaf.Cech.resolutionSectionsCohomologyEquiv_mk (X := X.toTopCat) R n s

/-- The cycle-class formula with the canonical quotient coercion on the left. -/
@[simp]
theorem resolutionSectionsCohomologyEquiv_coe (n : ℕ)
    (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionsCohomologyEquiv R n
      (s : resolutionSectionCycles R (n + 1) ⧸ (resolutionSectionBoundary R n).range) =
      resolutionSectionClass R (n + 1) s :=
  TopCat.Sheaf.Cech.resolutionSectionsCohomologyEquiv_coe (X := X.toTopCat) R n s

/-- The global-section short complex in degrees `n`, `n + 1`, and `n + 2`. -/
abbrev resolutionSectionShortComplex (n : ℕ) :=
  TopCat.Sheaf.Cech.resolutionSectionShortComplex (X := X.toTopCat) R n

variable {R}
/-- The section short-complex map induced by a morphism of injective resolutions. -/
abbrev resolutionSectionShortComplexMap (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    resolutionSectionShortComplex R n ⟶ resolutionSectionShortComplex S n :=
  TopCat.Sheaf.Cech.resolutionSectionShortComplexMap (X := X.toTopCat) φ n

/-- Cycle and quotient maps realizing the induced map on actual `Sheaf.H`. -/
abbrev resolutionSectionHomologyMapData (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    ShortComplex.LeftHomologyMapData (resolutionSectionShortComplexMap φ n)
      (resolutionSectionShortComplex R n).abLeftHomologyData
      (resolutionSectionShortComplex S n).abLeftHomologyData :=
  TopCat.Sheaf.Cech.resolutionSectionHomologyMapData (X := X.toTopCat) φ n

/-- Section short-complex homology identified with the original `Sheaf.H`. -/
abbrev resolutionSectionShortHomologyEquiv (R : InjectiveResolution A) (n : ℕ) :
    (resolutionSectionShortComplex R n).homology ≃+ Sheaf.H.{u + 1} A (n + 1) :=
  TopCat.Sheaf.Cech.resolutionSectionShortHomologyEquiv (X := X.toTopCat) R n

/-- The actual resolution-homology comparison is natural for every lift of a coefficient map. -/
theorem additiveResolutionHomologyEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n
      + 1))) :
    additiveResolutionHomologyEquiv S n
      (HomologicalComplex.homologyMap
        (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) (n + 1) x) =
      Sheaf.H.map f (n + 1) (additiveResolutionHomologyEquiv R n x) :=
  TopCat.Sheaf.Cech.additiveResolutionHomologyEquiv_naturality (X := X.toTopCat) φ n x

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
  TopCat.Sheaf.Cech.aRes X.toTopCat A h

/-- The section on each cover open obtained from a degree-zero Cech cochain. -/
abbrev cechZeroFamily (z : ((cechComplexFunctor U).obj A.obj).X 0) (i : ι) :
    A.obj.obj (op (U i)) :=
  TopCat.Sheaf.Cech.cechZeroFamily X.toTopCat U A z i

/-- Gluing identifies the kernel of the actual degree-zero Cech differential. -/
theorem additiveCechAugmentation_exact (hU : iSup U = ⊤) :
    (ShortComplex.mk (cechAugmentationZero X U A.obj)
      (((cechComplexFunctor U).obj A.obj).d 0 1) (cechAugmentationZero_d X U A.obj)).Exact :=
  TopCat.Sheaf.Cech.additiveCechAugmentation_exact X.toTopCat U A hU

/-- Restriction along an actual open cover is injective. -/
theorem additiveCechAugmentation_mono (hU : iSup U = ⊤) :
    Mono (cechAugmentationZero X U A.obj) :=
  TopCat.Sheaf.Cech.additiveCechAugmentation_mono X.toTopCat U A hU

/-- The actual restriction augmentation is a quasi-isomorphism for additive-injective sheaves on
  an open cover. -/
theorem additiveInjectiveCechAugmentation_quasiIso [Injective A] (hU : iSup U = ⊤) :
    QuasiIso (cechAugmentation X U A.obj) :=
  TopCat.Sheaf.Cech.additiveInjectiveCechAugmentation_quasiIso X.toTopCat U A hU

end Additive

end CechAugmentation

section CechResolution
open CategoryTheory.Cech HomologicalComplex HomologicalComplex₂
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

instance additiveCechComplexFunctor_additive :
    (cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive :=
  TopCat.Sheaf.Cech.additiveCechComplexFunctor_additive X.toTopCat U

/-- The Cech complex functor on the actual underlying additive presheaf. -/
abbrev additiveCechFunctor : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CochainComplex AddCommGrpCat.{u} ℕ :=
  TopCat.Sheaf.Cech.additiveCechFunctor X.toTopCat U

instance : (additiveCechFunctor X U).Additive := by
  dsimp [additiveCechFunctor]
  infer_instance

/-- The functor concentrating the second degree of an additive bicomplex in zero. -/
abbrev additiveCechSingleSecondZero :=
  TopCat.Sheaf.Cech.additiveCechSingleSecondZero.{u}

variable {X} {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A)

/-- The actual additive resolution and actual Cech functor, with Cech degree first. -/
abbrev additiveCechResolution : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  TopCat.Sheaf.Cech.additiveCechResolution (X := X.toTopCat) U R

/-- Row augmentation by the actual restrictions of each resolution term. -/
abbrev additiveCechRowAugmentation :
    additiveCechSingleSecondZero.obj
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex) ⟶
    (additiveCechResolution U R).flip :=
  TopCat.Sheaf.Cech.additiveCechRowAugmentation (X := X.toTopCat) U R

theorem additiveCechRowAugmentation_quasiIso (hU : iSup U = ⊤) (q : ℕ) :
    QuasiIso ((additiveCechRowAugmentation U R).f q) :=
  TopCat.Sheaf.Cech.additiveCechRowAugmentation_quasiIso (X := X.toTopCat) U R hU q

theorem cechResolutionAugmentationZero_d (p : ℕ) :
    ((additiveCechFunctor X U).map (R.ι.f 0)).f p ≫
      ((additiveCechResolution U R).X p).d 0 1 = 0 :=
  TopCat.Sheaf.Cech.cechResolutionAugmentationZero_d (X := X.toTopCat) U R p

/-- Column augmentation induced by the unchanged coefficient-to-resolution inclusion. -/
abbrev additiveCechColumnAugmentation :
    additiveCechSingleSecondZero.obj ((additiveCechFunctor X U).obj A) ⟶
      additiveCechResolution U R :=
  TopCat.Sheaf.Cech.additiveCechColumnAugmentation (X := X.toTopCat) U R

@[simp] theorem additiveCechColumnAugmentation_f_zero (p : ℕ) :
    ((additiveCechColumnAugmentation U R).f p).f 0 =
      ((additiveCechFunctor X U).map (R.ι.f 0)).f p :=
  TopCat.Sheaf.Cech.additiveCechColumnAugmentation_f_zero (X := X.toTopCat) U R p

variable (X)

/-- Degree `p` of the Cech complex of an additive sheaf. -/
abbrev additiveCechDegreeFunctor (p : ℕ) :=
  TopCat.Sheaf.Cech.additiveCechDegreeFunctor X.toTopCat U p

instance (p : ℕ) : (additiveCechDegreeFunctor X U p).Additive := by
  dsimp [additiveCechDegreeFunctor]
  infer_instance

/-- The discrete diagram of `(p + 1)`-fold intersections of the chosen opens. -/
abbrev cechTupleOpens (p : ℕ) : Discrete (Fin (p + 1) → ι) ⥤ X.Opensᵒᵖ :=
  TopCat.Sheaf.Cech.cechTupleOpens X.toTopCat U p

/-- The family of section groups on all degree-`p` tuple intersections. -/
abbrev additiveCechSectionFamilyFunctor (p : ℕ) :=
  TopCat.Sheaf.Cech.additiveCechSectionFamilyFunctor X.toTopCat U p

instance (p : ℕ) : (additiveCechSectionFamilyFunctor X U p).Additive := by
  dsimp [additiveCechSectionFamilyFunctor]
  infer_instance

instance (p : ℕ) : PreservesFiniteLimits (additiveCechSectionFamilyFunctor X U p) := by
  dsimp [additiveCechSectionFamilyFunctor]
  infer_instance

/-- A Cech degree as the limit of its discrete family of section groups. -/
abbrev additiveCechDegreeIsoLimit (p : ℕ) :
    additiveCechDegreeFunctor X U p ≅ additiveCechSectionFamilyFunctor X U p ⋙ lim :=
  TopCat.Sheaf.Cech.additiveCechDegreeIsoLimit X.toTopCat U p

instance (p : ℕ) : PreservesFiniteLimits (additiveCechDegreeFunctor X U p) :=
  preservesFiniteLimits_of_natIso (additiveCechDegreeIsoLimit X U p).symm

variable {X}

/-- Left exactness of actual products of sections gives the column augmentation in degree zero. -/
theorem additiveCechColumnAugmentation_quasiIsoAt_zero (p : ℕ) :
    QuasiIsoAt ((additiveCechColumnAugmentation U R).f p) 0 :=
  TopCat.Sheaf.Cech.additiveCechColumnAugmentation_quasiIsoAt_zero (X := X.toTopCat) U R p

/-- Products of the genuine affine-open resolution columns are exact in positive degrees. -/
theorem additiveCechResolution_column_exact_succ
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (p n : ℕ) : ((additiveCechResolution U R).X p).ExactAt (n + 1) :=
  TopCat.Sheaf.Cech.additiveCechResolution_column_exact_succ (X := X.toTopCat) U R
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (hU p a) n) p n

/-- For a quasicoherent coefficient and affine tuple intersections, the actual column
  augmentations are quasi-isomorphisms. -/
theorem additiveCechColumnAugmentation_quasiIso
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (p : ℕ) : QuasiIso ((additiveCechColumnAugmentation U R).f p) :=
  TopCat.Sheaf.Cech.additiveCechColumnAugmentation_quasiIso (X := X.toTopCat) U R
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (hU p a) n) p

section Naturality
variable {U} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B} {R}

/-- The actual Cech bicomplex map of a lift between additive injective resolutions. -/
abbrev additiveCechResolutionMap (φ : InjectiveResolution.Hom R S f) :
    additiveCechResolution U R ⟶ additiveCechResolution U S :=
  TopCat.Sheaf.Cech.additiveCechResolutionMap (X := X.toTopCat) (U := U) φ

/-- The row augmentation commutes with every actual coefficient-resolution lift. -/
theorem additiveCechRowAugmentation_naturality (φ : InjectiveResolution.Hom R S f) :
    additiveCechSingleSecondZero.map
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) ≫
        additiveCechRowAugmentation U S =
      additiveCechRowAugmentation U R ≫
        (flipFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ)).map (additiveCechResolutionMap φ) :=
  TopCat.Sheaf.Cech.additiveCechRowAugmentation_naturality (X := X.toTopCat) (U := U) φ

/-- The column augmentation commutes with the original coefficient map and every lift. -/
theorem additiveCechColumnAugmentation_naturality (φ : InjectiveResolution.Hom R S f) :
    additiveCechSingleSecondZero.map ((additiveCechFunctor X U).map f) ≫
      additiveCechColumnAugmentation U S =
    additiveCechColumnAugmentation U R ≫ additiveCechResolutionMap φ :=
  TopCat.Sheaf.Cech.additiveCechColumnAugmentation_naturality (X := X.toTopCat) (U := U) φ

end Naturality

end CechResolution

section CechTotalComparison
open HomologicalComplex HomologicalComplex₂
open HomologicalComplex₂.AddCommGrp
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A)

/-- The actual Cech complex maps to the total through the resolution inclusion. -/
abbrev additiveCechToTotal : (additiveCechFunctor X U).obj A ⟶
    (additiveCechResolution U R).total (.up ℕ) :=
  TopCat.Sheaf.Cech.additiveCechToTotal (X := X.toTopCat) U R

/-- Actual global resolution sections map to the same total through restrictions. -/
abbrev additiveResolutionSectionsToTotal :
    ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex ⟶
      (additiveCechResolution U R).total (.up ℕ) :=
  TopCat.Sheaf.Cech.additiveResolutionSectionsToTotal (X := X.toTopCat) U R

theorem additiveResolutionSectionsToTotal_quasiIso (hU : iSup U = ⊤) :
    QuasiIso (additiveResolutionSectionsToTotal U R) :=
  TopCat.Sheaf.Cech.additiveResolutionSectionsToTotal_quasiIso (X := X.toTopCat) U R hU

theorem additiveCechToTotal_quasiIso
    (M : X.Modules) [M.IsQuasicoherent] (R : InjectiveResolution (moduleAddSheaf X M))
    (hU : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    QuasiIso (additiveCechToTotal U R) :=
  TopCat.Sheaf.Cech.additiveCechToTotal_quasiIso (X := X.toTopCat) U R
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (hU p a) n)

section Naturality
variable {U R} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B}

theorem additiveCechToTotal_naturality (φ : InjectiveResolution.Hom R S f) :
    (additiveCechFunctor X U).map f ≫ additiveCechToTotal U S =
      additiveCechToTotal U R ≫ HomologicalComplex₂.total.map (additiveCechResolutionMap φ) (.up
        ℕ) :=
  TopCat.Sheaf.Cech.additiveCechToTotal_naturality (X := X.toTopCat) (U := U) φ

theorem additiveResolutionSectionsToTotal_naturality (φ : InjectiveResolution.Hom R S f) :
    ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom ≫
      additiveResolutionSectionsToTotal U S =
    additiveResolutionSectionsToTotal U R ≫
      HomologicalComplex₂.total.map (additiveCechResolutionMap φ) (.up ℕ) :=
  TopCat.Sheaf.Cech.additiveResolutionSectionsToTotal_naturality (X := X.toTopCat) (U := U) φ

end Naturality

variable (M : X.Modules) [M.IsQuasicoherent]
variable (R : InjectiveResolution (moduleAddSheaf X M))
variable (hcover : iSup U = ⊤)
variable (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))

/-- The two genuine augmentations compare original Cech homology with actual additive-resolution
  sections. -/
abbrev moduleCechResolutionHomologyIso (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology n ≅
      (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj R.cocomplex).homology n :=
  TopCat.Sheaf.Cech.additiveCechResolutionHomologyIso (X := X.toTopCat) U R hcover
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n) n

@[reassoc (attr := simp)]
theorem moduleCechResolutionHomologyIso_hom_comp (n : ℕ) :
    (moduleCechResolutionHomologyIso U M R hcover haff n).hom ≫
      homologyMap (additiveResolutionSectionsToTotal U R) n =
        homologyMap (additiveCechToTotal U R) n :=
  TopCat.Sheaf.Cech.additiveCechResolutionHomologyIso_hom_comp (X := X.toTopCat) U R hcover
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n) n

variable {M R} {N : X.Modules} [N.IsQuasicoherent]
  {S : InjectiveResolution (moduleAddSheaf X N)}
  {f : moduleAddSheaf X M ⟶ moduleAddSheaf X N}

theorem moduleCechResolutionHomologyIso_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    homologyMap ((additiveCechFunctor X U).map f) n ≫
      (moduleCechResolutionHomologyIso U N S hcover haff n).hom =
    (moduleCechResolutionHomologyIso U M R hcover haff n).hom ≫
      homologyMap (((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).map φ.hom) n :=
  TopCat.Sheaf.Cech.additiveCechResolutionHomologyIso_naturality (X := X.toTopCat) U hcover
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n)
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen N S _ (haff p a) n) φ n

variable (M R)

/-- Positive-degree original Sheaf.H computed by the original Cech complex of an
  affine-intersection open cover. -/
abbrev moduleCechCohomologyAddEquiv (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1) ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) :=
  TopCat.Sheaf.Cech.additiveCechCohomologyAddEquiv (X := X.toTopCat) U R hcover
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n) n

variable {M R}

/-- The Cech comparison respects every coefficient map and every additive-resolution lift. -/
theorem moduleCechCohomologyAddEquiv_naturality
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (x : ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1)) :
    moduleCechCohomologyAddEquiv U N S hcover haff n
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x) =
    Sheaf.H.map f (n + 1) (moduleCechCohomologyAddEquiv U M R hcover haff n x) :=
  TopCat.Sheaf.Cech.additiveCechCohomologyAddEquiv_naturality (X := X.toTopCat) U hcover
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n)
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen N S _ (haff p a) n) φ n x

/-- The comparison is independent of the chosen additive injective resolution. -/
theorem moduleCechCohomologyAddEquiv_independent
    (M : X.Modules) [M.IsQuasicoherent]
    (R S : InjectiveResolution (moduleAddSheaf X M)) (n : ℕ) :
    moduleCechCohomologyAddEquiv U M R hcover haff n =
      moduleCechCohomologyAddEquiv U M S hcover haff n :=
  TopCat.Sheaf.Cech.additiveCechCohomologyAddEquiv_independent (X := X.toTopCat) U hcover R S
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n)
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M S _ (haff p a) n) n

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

section CanonicalCechComparison
open HomologicalComplex
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (M : X.Modules) [M.IsQuasicoherent]

/-- Genuine affine acyclicity supplies the intrinsic hypothesis of the topological comparison. -/
theorem moduleCech_hasAcyclicIntersections
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    TopCat.Sheaf.Cech.HasAcyclicIntersections U (moduleAddSheaf X M) :=
  fun p a n => subsingleton_sheafHPrime_of_isAffineOpen M _ (haff p a) n

variable (hcover : iSup U = ⊤)
  (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))

/-- The original positive Cech comparison, with the injective resolution selected internally. -/
def moduleCechCohomologyAddEquivCanonical (n : ℕ) :
    ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1) ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) :=
  TopCat.Sheaf.Cech.cechCohomologyAddEquiv U hcover (moduleAddSheaf X M)
    (moduleCech_hasAcyclicIntersections U M haff) n

/-- Every supplied-resolution normalization is the same canonical comparison. -/
theorem moduleCechCohomologyAddEquiv_eq_canonical
    (R : InjectiveResolution (moduleAddSheaf X M)) (n : ℕ) :
    moduleCechCohomologyAddEquiv U M R hcover haff n =
      moduleCechCohomologyAddEquivCanonical U M hcover haff n :=
  TopCat.Sheaf.Cech.additiveCechCohomologyAddEquiv_eq_canonical U hcover R
    (fun p a n => additiveResolution_sections_exact_of_isAffineOpen M R _ (haff p a) n)
    (moduleCech_hasAcyclicIntersections U M haff) n

variable {M} {N : X.Modules} [N.IsQuasicoherent]

/-- Canonical coefficient naturality retains the original sheaf map and needs no supplied lift. -/
theorem moduleCechCohomologyAddEquivCanonical_naturality
    (f : moduleAddSheaf X M ⟶ moduleAddSheaf X N) (n : ℕ)
    (x : ((additiveCechFunctor X U).obj (moduleAddSheaf X M)).homology (n + 1)) :
    moduleCechCohomologyAddEquivCanonical U N hcover haff n
      (homologyMap ((additiveCechFunctor X U).map f) (n + 1) x) =
      Sheaf.H.map f (n + 1) (moduleCechCohomologyAddEquivCanonical U M hcover haff n x) :=
  TopCat.Sheaf.Cech.cechCohomologyAddEquiv_naturality U hcover
    (moduleCech_hasAcyclicIntersections U M haff)
    (moduleCech_hasAcyclicIntersections U N haff) f n x

end CanonicalCechComparison

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
  dsimp [additiveCechFunctor, TopCat.Sheaf.Cech.additiveCechFunctor, cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor,
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
  erw [← Category.assoc, cechAugmentationZero_π, cechAugmentationZero_π]
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
