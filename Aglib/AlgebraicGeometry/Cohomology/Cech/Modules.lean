/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.FiniteCoefficients
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Cech computations with arbitrary structural rings and module coefficients

The native module presheaf is restricted to a specified base ring through its
map to global functions. Its Cech homology computes the original additive
`Sheaf.H`, with the same scalar action. The comparison retains the actual
cover and affine-intersection hypotheses; no field or finite-generation
assumption is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The original Cech complex, retaining the structural ring on all sections. -/
abbrev moduleCechComplex (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj (moduleSectionsPresheaf X α M)

variable (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- Forgetting scalars identifies this with the unchanged additive Cech complex. -/
def moduleCechForgetIso :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (moduleCechComplex X α M U) ≅
        (cechComplexFunctor U).obj (moduleAddSheaf X M).obj :=
  cechComplexCoefficientIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) U
    (moduleSectionsPresheaf X α M)

theorem moduleCechForgetIso_hom_f_π (n : ℕ) (b : Fin (n + 1) → ι) :
    (moduleCechForgetIso X α M U).hom.f n ≫
      Pi.π (fun b : Fin (n + 1) → ι ↦
        (moduleAddSheaf X M).obj.obj (op (∏ᶜ fun k ↦ U (b k)))) b =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (Pi.π (fun b : Fin (n + 1) → ι ↦
        (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k ↦ U (b k)))) b) := by
  change (𝟙 _ ≫ piComparison (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (fun b : Fin (n + 1) → ι ↦
      (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k ↦ U (b k))))) ≫ _ = _
  rw [Category.id_comp]
  exact piComparison_comp_π _ _ b

theorem moduleCechForgetIso_scalar (a : R) :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (a • 𝟙 (moduleCechComplex X α M U)) ≫ (moduleCechForgetIso X α M U).hom =
    (moduleCechForgetIso X α M U).hom ≫
      (cechComplexFunctor U).map (moduleScalarOfGlobal X M (α a)).hom := by
  ext n : 1
  apply Pi.hom_ext (f := fun b : Fin (n + 1) → ι ↦
    (moduleAddSheaf X M).obj.obj (op (∏ᶜ fun k ↦ U (b k))))
  intro b
  simp only [comp_f, Category.assoc]
  rw [moduleCechForgetIso_hom_f_π]
  change _ = (moduleCechForgetIso X α M U).hom.f n ≫
    Limits.Pi.map (fun b : Fin (n + 1) → ι ↦
      (moduleScalarOfGlobal X M (α a)).hom.app (op (∏ᶜ fun k ↦ U (b k)))) ≫ _
  rw [Pi.map_π, ← Category.assoc]
  erw [moduleCechForgetIso_hom_f_π]
  ext z
  change ↑(∏ᶜ fun b : Fin (n + 1) → ι ↦
    (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k ↦ U (b k)))) at z
  change (Pi.π (fun b : Fin (n + 1) → ι ↦
    (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k ↦ U (b k))))) b (a • z) =
      a • (Pi.π (fun b : Fin (n + 1) → ι ↦
        (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k ↦ U (b k))))) b z
  exact map_smul _ _ _

/-- Scalar forgetting on actual homology agrees with additive Cech homology. -/
def moduleCechAdditiveHomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
      ((moduleCechComplex X α M U).homology n) ≅
        ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).homology n :=
  (((moduleCechComplex X α M U).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
      (homologyFunctor AddCommGrpCat.{u} (.up ℕ) n).mapIso
        (moduleCechForgetIso X α M U)

private theorem moduleHomologyMap_scalar (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (a : R) (n : ℕ) : homologyMap (a • 𝟙 C) n = a • 𝟙 (C.homology n) := by
  change ShortComplex.homologyMap (a • 𝟙 (C.sc n)) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

theorem moduleCechAdditiveHomologyIso_scalar (n : ℕ) (a : R)
    (x : (moduleCechComplex X α M U).homology n) :
    (moduleCechAdditiveHomologyIso X α M U n).hom (a • x) =
      homologyMap ((cechComplexFunctor U).map (moduleScalarOfGlobal X M (α a)).hom) n
        ((moduleCechAdditiveHomologyIso X α M U n).hom x) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let C := moduleCechComplex X α M U
  let δ := a • 𝟙 C
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map δ) G
  have hc := congrArg (fun g ↦ homologyMap g n) (moduleCechForgetIso_scalar X α M U a)
  simp only [homologyMap_comp] at hc
  have h : G.map (homologyMap δ n) ≫ (moduleCechAdditiveHomologyIso X α M U n).hom =
      (moduleCechAdditiveHomologyIso X α M U n).hom ≫
        homologyMap ((cechComplexFunctor U).map (moduleScalarOfGlobal X M (α a)).hom) n := by
    dsimp only [moduleCechAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc]
    exact congrArg (fun k ↦ ((C.sc n).mapHomologyIso G).inv ≫ k) hc
  rw [moduleHomologyMap_scalar] at h
  exact ConcreteCategory.congr_hom h x

variable [M.IsQuasicoherent] (hcover : iSup U = ⊤)
  (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k)))
  (I : InjectiveResolution (moduleAddSheaf X M))

/-- Positive Cech cohomology computes actual `Sheaf.H` linearly over any structural ring. -/
def moduleCechCohomologyLinearEquiv (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M (n + 1)
    (moduleCechComplex X α M U).homology (n + 1) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) := by
  letI := moduleCohomologyModuleOfHom X α M (n + 1)
  exact {
    __ := (moduleCechAdditiveHomologyIso X α M U (n + 1)).addCommGroupIsoToAddEquiv.trans
      (moduleCechCohomologyAddEquiv U M I hcover haff n)
    map_smul' := fun a x ↦ by
      change moduleCechCohomologyAddEquiv U M I hcover haff n
        ((moduleCechAdditiveHomologyIso X α M U (n + 1)).hom (a • x)) = _
      rw [moduleCechAdditiveHomologyIso_scalar]
      let δ : InjectiveResolution.Hom I I (moduleScalarOfGlobal X M (α a)) :=
        ⟨InjectiveResolution.desc (moduleScalarOfGlobal X M (α a)) I I, by simp⟩
      exact moduleCechCohomologyAddEquiv_naturality U hcover haff δ n _ }

/-- On a separated scheme an affine open cover gives the same linear comparison. -/
def moduleAffineCechCohomologyLinearEquiv [X.IsSeparated] (n : ℕ)
    (haffine : ∀ i, IsAffineOpen (U i)) :
    letI := moduleCohomologyModuleOfHom X α M (n + 1)
    (moduleCechComplex X α M U).homology (n + 1) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1) :=
  moduleCechCohomologyLinearEquiv X α M U hcover (fun p a ↦ by
    have he : (∏ᶜ fun k ↦ U (a k)) = ⨅ k, U (a k) := by
      apply le_antisymm
      · exact le_iInf fun k ↦ leOfHom (Limits.Pi.π _ k)
      · exact leOfHom (Limits.Pi.lift fun k ↦ homOfLE (iInf_le _ k))
    rw [he]
    exact IsAffineOpen.iInf (fun k ↦ haffine (a k))) I n

end AlgebraicGeometry.Scheme.Cohomology
