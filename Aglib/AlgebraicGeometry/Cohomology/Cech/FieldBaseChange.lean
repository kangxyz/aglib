/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GlobalSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.FiniteCoefficients
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
/-!
# Canonical field base change of actual finite-cover Cech complexes

For a finite family of affine opens in a separated field scheme, the actual
Cech complex and its homology commute with field extension. The chain map is
constructed from the actual scheme projection, structural scalar actions,
finite-product comparison, and the original mathlib `cechComplexFunctor`.
A covering hypothesis is unnecessary for this complex-level result.

The coefficient comparison uses only finite products; tensor extension does
not need to preserve arbitrary products. `structureCechForgetIso` identifies
the underlying additive complex with the original structure-sheaf Cech complex.
The comparison with the original `Sheaf.H` is a separate obligation; this leaf
does not assert proper cohomology base change.

Source basis: project entry `d0dc4cca7af233fe0ba5be27efa436f64cf0e403`, integrated
checkout `6a34df6e3e36276c043d35814007f78163a396d0`, Lean 4.34.1, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Quillen
`83629578a3d70787d41ec631f5234af8758716af`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.CechBaseChange` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open scoped Simplicial TensorProduct
open CategoryTheory.Cech
namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {F : Type u} [Field F]
attribute [local instance] globalSectionsModule openSectionsModule

/-- Actual structure-sheaf sections as a presheaf of modules over the structural field. -/
def structureSectionsPresheaf (X : FScheme F) : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} F where
  obj U := ModuleCat.of F Γ(X.left, U.unop)
  map h := ModuleCat.ofHom (openSectionsRestriction X h.unop.le)
  map_id U := by
    ext s
    change X.left.presheaf.map (𝟙 U) s = s
    simp
  map_comp h k := by
    ext s
    exact congrArg (fun q => q.hom s) (X.left.presheaf.map_comp h k)

variable (K : Type u) [Field K] [Algebra F K]

/-- The literal tensor extension M ↦ K ⊗[F] M, retaining the supplied F-algebra structure on K. -/
def fieldTensorFunctor : ModuleCat.{u} F ⥤ ModuleCat.{u} K where
  obj M := ModuleCat.of K (K ⊗[F] M)
  map f := ModuleCat.ofHom (f.hom.baseChange K)
  map_id M := by ext z; rfl
  map_comp f g := by ext z; rfl

instance fieldTensorFunctor_additive : (fieldTensorFunctor (F := F) K).Additive where
  map_add := by intro M N f g; ext z; simp [fieldTensorFunctor]

instance fieldTensorFunctor_preservesHomology :
    (fieldTensorFunctor (F := F) K).PreservesHomology := by
  apply ((Functor.exact_tfae (fieldTensorFunctor (F := F) K)).out 2 3).mp
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact K hS

instance fieldTensorFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fieldTensorFunctor (F := F) K) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

attribute [local instance] baseChangeOpenSectionsModule baseChangeGlobalSectionsModule

/-- The canonical tensor comparison on open sections, natural in the open. -/
def structureSectionsTensorComparison (X : FScheme F) :
    structureSectionsPresheaf X ⋙ fieldTensorFunctor (F := F) K ⟶
      (Opens.map (fieldBaseChangeProjection K X).base).op ⋙
        structureSectionsPresheaf (fieldBaseChange K X) where
  app U := ModuleCat.ofHom (structureOpenSectionsBaseChangeMap K X U.unop)
  naturality U V h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change K ⊗[F] Γ(X.left, U.unop) at z
    induction z using TensorProduct.inductionOn with
    | tmul a s =>
      change a • (fieldBaseChangeProjection K X).app V.unop
        (X.left.presheaf.map h s) =
        (openSectionsRestriction (fieldBaseChange K X) _)
          (a • (fieldBaseChangeProjection K X).app U.unop s)
      rw [map_smul]
      apply congrArg (a • ·)
      exact congrArg (fun q => q.hom s) ((fieldBaseChangeProjection K X).naturality h)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem structureSectionsTensorComparison_app_tmul (X : FScheme F) (U : X.left.Opens)
    (a : K) (s : Γ(X.left, U)) :
    (structureSectionsTensorComparison K X).app (op U) (a ⊗ₜ[F] s) =
      a • (fieldBaseChangeProjection K X).app U s := rfl

/-- Mathlib's original Cech complex with the structural field action on actual sections. -/
abbrev structureCechComplex (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    CochainComplex (ModuleCat.{u} F) ℕ :=
  (cechComplexFunctor U).obj (structureSectionsPresheaf X)

/-- Forgetting scalars gives the original additive structure-sheaf Cech complex. -/
def structureCechForgetIso (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    ((forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (structureCechComplex X U) ≅ (cechComplexFunctor U).obj (structureAddSheaf X.left).obj :=
  CategoryTheory.Cech.cechComplexCoefficientIso (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})
    U (structureSectionsPresheaf X)

/-- Preimages of the open family give the actual Cech complex after scheme base change. -/
def structureCechGeometricIso (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    (cechComplexFunctor U).obj
      ((Opens.map (fieldBaseChangeProjection K X).base).op ⋙
        structureSectionsPresheaf (fieldBaseChange K X)) ≅
      structureCechComplex (fieldBaseChange K X)
        (fun i ↦ fieldBaseChangeProjection K X ⁻¹ᵁ U i) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} K)).mapIso
    (CategoryTheory.Cech.cechCosimplicialChangeIso
      (Opens.map (fieldBaseChangeProjection K X).base) U
      (structureSectionsPresheaf (fieldBaseChange K X)))

/-- Canonical scalar extension of the Cech complex, using actual projection maps on every
  intersection. -/
def structureCechBaseChangeMap (X : FScheme F) {ι : Type u} [Finite ι]
    (U : ι → X.left.Opens) :
    ((fieldTensorFunctor (F := F) K).mapHomologicalComplex _).obj
      (structureCechComplex X U) ⟶
      structureCechComplex (fieldBaseChange K X)
        (fun i ↦ fieldBaseChangeProjection K X ⁻¹ᵁ U i) :=
  (finiteCechComplexCoefficientIso (fieldTensorFunctor (F := F) K) U
      (structureSectionsPresheaf X)).hom ≫
    (cechComplexFunctor U).map (structureSectionsTensorComparison K X) ≫
      (structureCechGeometricIso K X U).hom

/-- Every nonempty finite intersection of affine opens in a separated scheme is affine. -/
lemma isAffineOpen_cechTuple {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) (a : Fin (n + 1) → ι) :
    IsAffineOpen (∏ᶜ fun j => U (a j)) := by
  have he : (∏ᶜ fun j => U (a j)) = ⨅ j, U (a j) := by
    apply le_antisymm
    · exact le_iInf fun j => leOfHom (Limits.Pi.π _ j)
    · exact leOfHom (Limits.Pi.lift fun j => homOfLE (iInf_le _ j))
  rw [he]
  exact IsAffineOpen.iInf (fun j => hU (a j))

/-- Affine-intersection base change makes the coefficient comparison an isomorphism in every
  degree. -/
lemma structureCechTensorComparison_isIso (X : FScheme F) [IsSeparated X.hom]
    {ι : Type u} (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso ((cechComplexFunctor U).map (structureSectionsTensorComparison K X)) := by
  let : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  have hn (n : ℕ) : IsIso (((cechComplexFunctor U).map
      (structureSectionsTensorComparison K X)).f n) := by
    have hi (a : Fin (n + 1) → ι) :
        IsIso ((structureSectionsTensorComparison K X).app (op (∏ᶜ fun j => U (a j)))) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact structureOpenSectionsBaseChangeMap_bijective_of_isAffineOpen K X _
        (isAffineOpen_cechTuple U hU n a)
    let := hi
    change IsIso (Limits.Pi.map (fun a : Fin (n + 1) → ι =>
      (structureSectionsTensorComparison K X).app (op (∏ᶜ fun j => U (a j)))))
    infer_instance
  let := hn
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical Cech tensor map is an isomorphism for a finite affine family in a separated
  field scheme. -/
lemma structureCechBaseChangeMap_isIso (X : FScheme F) [IsSeparated X.hom]
    {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (structureCechBaseChangeMap K X U) := by
  let := structureCechTensorComparison_isIso K X U hU
  unfold structureCechBaseChangeMap
  infer_instance

/-- Flatness and the canonical complex isomorphism give tensor base change of actual Cech
  homology. -/
def structureCechHomologyBaseChangeIso (X : FScheme F) [IsSeparated X.hom]
    {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (fieldTensorFunctor (F := F) K).obj ((structureCechComplex X U).homology n) ≅
      (structureCechComplex (fieldBaseChange K X)
        (fun i ↦ fieldBaseChangeProjection K X ⁻¹ᵁ U i)).homology n := by
  let := structureCechBaseChangeMap_isIso K X U hU
  exact (((structureCechComplex X U).sc n).mapHomologyIso (fieldTensorFunctor (F := F) K)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (.up ℕ) n).mapIso (asIso
      (structureCechBaseChangeMap K X U))

end AlgebraicGeometry.Scheme.Cohomology
