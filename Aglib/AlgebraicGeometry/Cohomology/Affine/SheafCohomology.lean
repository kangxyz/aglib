/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles
public import Aglib.Topology.Sheaves.Cech.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Injective.RestrictionSections
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
/-!
# Comparing affine module resolutions with actual additive-sheaf cohomology

For every affine scheme and every quasicoherent module sheaf, positive-degree
cohomology of the actual underlying additive sheaf vanishes. The field-scheme
specialization retains the unchanged `moduleCohomology` and its structural
scalar action.

The comparison proves flasque acyclicity for the existing `Sheaf.H`. Native
module injectives enter through their proved flasque and acyclic underlying
additive sheaves. Dimension shifting along their actual kernel short exact
sequences then transfers Quillen's section-complex exactness to the original
Ext cohomology. This does not require preservation of injectives by forgetting
the module structure. It proves the vanishing comparison needed here; a
natural isomorphism of all right-derived functors is not constructed.

Source basis: project `d0dc4cca7af233fe0ba5be27efa436f64cf0e403`, Lean 4.34.1,
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Quillen 0.7 physical
revision `83629578a3d70787d41ec631f5234af8758716af`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.AffineHigherComparison` at R5Lab
  revision
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
/-- The sheafified free abelian presheaf functor on the Zariski site of `X`. -/
abbrev additiveFreeFunctor :=
  TopCat.Sheaf.Cech.additiveFreeFunctor X.toTopCat

/-- The adjunction between sheafified free abelian presheaves and underlying presheaves of sets. -/
abbrev additiveFreeAdjunction :=
  TopCat.Sheaf.Cech.additiveFreeAdjunction X.toTopCat

/-- The functor assigning to each open of `X` the free abelian sheaf on its representable
presheaf. -/
abbrev additiveOpenFreeFunctor :
    X.Opens ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  TopCat.Sheaf.Cech.additiveOpenFreeFunctor X.toTopCat

/-- Morphisms from the free abelian sheaf on `U`, identified with sections of `A` over `U`. -/
abbrev additiveOpenHomEquiv (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((additiveOpenFreeFunctor X).obj U ⟶ A) ≃ A.obj.obj (op U) :=
  TopCat.Sheaf.Cech.additiveOpenHomEquiv X.toTopCat U A

theorem additiveOpenHomEquiv_naturality {U V : X.Opens} (i : U ⟶ V)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (f : (additiveOpenFreeFunctor X).obj V ⟶ A) :
    additiveOpenHomEquiv X U A ((additiveOpenFreeFunctor X).map i ≫ f) =
      A.obj.map i.op (additiveOpenHomEquiv X V A f) :=
  TopCat.Sheaf.Cech.additiveOpenHomEquiv_naturality X.toTopCat i A f

instance additiveOpenFreeFunctor_map_mono {U V : X.Opens} (i : U ⟶ V) :
    Mono ((additiveOpenFreeFunctor X).map i) :=
  TopCat.Sheaf.Cech.additiveOpenFreeFunctor_map_mono X.toTopCat i

instance additiveSheaf_injective_isFlasque
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective A] :
    TopCat.Presheaf.IsFlasque A.obj :=
  TopCat.Sheaf.Cech.additiveSheaf_injective_isFlasque X.toTopCat A

variable {X}

lemma subsingleton_sheafH_one_of_shortExact
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Subsingleton (Sheaf.H.{u + 1} S.X₂ 1)]
    (hs : Function.Surjective (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H.{u + 1} S.X₁ 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
  obtain ⟨s, hs⟩ := hs (Sheaf.H.equiv₀ S.X₃ isTerminalTop z)
  let y := (Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm s
  have hy : Sheaf.H.map S.g 0 y = z := by
    apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
    rw [← Sheaf.H.equiv₀_naturality]
    exact (congrArg (S.g.hom.app (op ⊤)) ((Sheaf.H.equiv₀ S.X₂ isTerminalTop).apply_symm_apply
      s)).trans hs
  have hex := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' hS 0 1 rfl)
  exact hz.symm.trans ((hex z).mpr ⟨y, hy⟩)

lemma subsingleton_sheafH_succ_of_shortExact
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Sheaf.H.{u + 1} S.X₂ (n + 1))]
    [Subsingleton (Sheaf.H.{u + 1} S.X₃ n)] :
    Subsingleton (Sheaf.H.{u + 1} S.X₁ (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
  exact hz.symm.trans (by rw [Subsingleton.elim z 0, map_zero])

theorem subsingleton_sheafH_of_isFlasque
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque A.obj] (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} A (n + 1)) := by
  induction n generalizing A with
  | zero =>
    let I := injectiveResolution A
    let S := CategoryTheory.InjectiveResolution.initialSequence I
    have hS : S.ShortExact :=
      CategoryTheory.InjectiveResolution.initialSequence_shortExact I
    let : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque A.obj)
    let : Injective S.X₂ := inferInstanceAs (Injective (I.cocomplex.X 0))
    apply subsingleton_sheafH_one_of_shortExact hS
    exact (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact hS)
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
    let : Subsingleton (Sheaf.H.{u + 1} S.X₃ (n + 1)) := ih S.X₃
    exact subsingleton_sheafH_succ_of_shortExact hS (n + 1)

open AlgebraicGeometry.Scheme.Modules.TwoOpen

/-- Injective module sheaves are acyclic for the original additive-sheaf H,
because their underlying sheaves are flasque. -/
theorem subsingleton_moduleAddSheafH_of_injective (M : X.Modules) [Injective M] (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)) := by
  let : TopCat.Presheaf.IsFlasque (moduleAddSheaf X M).obj :=
    AlgebraicGeometry.Scheme.Modules.injective_isFlasque X M
  exact subsingleton_sheafH_of_isFlasque _ n

/-- Exactness of the actual section complex lifts sections to the next
kernel in the original module resolution. -/
theorem moduleResolution_kernelSections_surjective {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ)
    (hex : (((sectionsFunctor X ⊤).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1)) :
    Function.Surjective
      (((AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X).map
        (CategoryTheory.InjectiveResolution.kernelSequence I n).g).hom.app (op ⊤)) := by
  let G := sectionsFunctor X ⊤
  let ι := kernel.ι (I.cocomplex.d (n + 1) (n + 2))
  have hi : Function.Injective (G.map ι) := by
    change Function.Injective
      (((SheafOfModules.toSheaf X.ringCatSheaf).map ι).hom.app (op ⊤))
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

/-- An actual module injective resolution whose section complex is exact
in positive degrees has zero original additive-sheaf cohomology. The bridge
is the proved acyclicity of the underlying injective module terms, followed
by the actual cohomology long exact sequences of the resolution kernels. -/
theorem subsingleton_moduleAddSheafH_of_resolutionSections_exact
    {M : X.Modules} (I : InjectiveResolution M)
    (hex : ∀ n : ℕ,
      (((sectionsFunctor X ⊤).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1))
    (n : ℕ) : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  have hmid (m k : ℕ) :
      Subsingleton (Sheaf.H.{u + 1} (F.obj (I.cocomplex.X m)) (k + 1)) :=
    subsingleton_moduleAddSheafH_of_injective (I.cocomplex.X m) k
  have hk (k : ℕ) : ∀ m : ℕ,
      Subsingleton (Sheaf.H.{u + 1} (F.obj (kernel (I.cocomplex.d m (m + 1)))) (k + 1)) := by
    induction k with
    | zero =>
      intro m
      let S := (CategoryTheory.InjectiveResolution.kernelSequence I m).map F
      have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I m)
      let : Subsingleton (Sheaf.H.{u + 1} S.X₂ 1) := hmid m 0
      exact subsingleton_sheafH_one_of_shortExact hS
        (moduleResolution_kernelSections_surjective I m (hex m))
    | succ k ih =>
      intro m
      let S := (CategoryTheory.InjectiveResolution.kernelSequence I m).map F
      have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I m)
      let : Subsingleton (Sheaf.H.{u + 1} S.X₂ (k + 1 + 1)) := hmid m (k + 1)
      let : Subsingleton (Sheaf.H.{u + 1} S.X₃ (k + 1)) := ih (m + 1)
      exact subsingleton_sheafH_succ_of_shortExact hS (k + 1)
  let S := (CategoryTheory.InjectiveResolution.initialSequence I).map F
  have hS : S.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf
    (CategoryTheory.InjectiveResolution.initialSequence_shortExact I)
  cases n with
  | zero =>
    let : Subsingleton (Sheaf.H.{u + 1} S.X₂ 1) := hmid 0 0
    exact subsingleton_sheafH_one_of_shortExact hS
      (moduleResolution_kernelSections_surjective I 0 (hex 0))
  | succ n =>
    let : Subsingleton (Sheaf.H.{u + 1} S.X₂ (n + 1 + 1)) := hmid 0 (n + 1)
    let : Subsingleton (Sheaf.H.{u + 1} S.X₃ (n + 1)) := hk n 1
    exact subsingleton_sheafH_succ_of_shortExact hS (n + 1)

/-- Actual positive-degree additive-sheaf cohomology vanishes for every
quasicoherent module sheaf on an affine scheme. -/
theorem subsingleton_moduleAddSheafH_of_isAffine [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)) := by
  let I := injectiveResolution M
  apply subsingleton_moduleAddSheafH_of_resolutionSections_exact I _ n
  intro k
  simpa only [(isAffineOpen_top X).opensRange_fromSpec] using
    AlgebraicGeometry.Scheme.Modules.affineOpen_injectiveResolution_exact_succ
      (isAffineOpen_top X).fromSpec M I k

open AlgebraicGeometry.Scheme.OverField in
/-- Affine acyclicity for the unchanged F-module cohomology object, whose
scalar action is induced by the structural constants. -/
theorem moduleCohomology_subsingleton_of_isAffine {F : Type u} [Field F]
    (X : FScheme F) [IsAffine X.left] (M : X.left.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (moduleCohomology F X M (n + 1)) :=
  subsingleton_moduleAddSheafH_of_isAffine M n

open AlgebraicGeometry.Scheme.OverField in
/-- Positive-degree vanishing for the unchanged structure-sheaf cohomology
on an affine field scheme. -/
theorem structureCohomology_subsingleton_of_isAffine {F : Type u} [Field F]
    (X : FScheme F) [IsAffine X.left] (n : ℕ) :
    Subsingleton (structureCohomology F X (n + 1)) := by
  let e : SheafOfModules.free (R := X.left.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.left.ringCatSheaf := coproductUniqueIso _
  let : (SheafOfModules.unit X.left.ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).prop_of_iso e (by infer_instance)
  exact moduleCohomology_subsingleton_of_isAffine X (SheafOfModules.unit X.left.ringCatSheaf) n

end AlgebraicGeometry.Scheme.Cohomology

