/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.HomologyZero
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero

/-!
# Scalar forgetting in the original degree-zero Cech comparison

The linear degree-zero computation retains the actual restriction
augmentation after forgetting structural scalars. Its comparison with
`Sheaf.H.equiv₀` is the literal original global section, and its homology
embedding is the native zero-term embedding. No quasicoherence or affine
intersection premise is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Cech
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- Forgetting scalars preserves the original embedding of zero-degree homology. -/
@[reassoc]
theorem moduleCechAdditiveHomologyIso_hom_homologyZeroι :
    (moduleCechAdditiveHomologyIso X α M U 0).hom ≫
        CochainComplex.homologyZeroι ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          (CochainComplex.homologyZeroι (moduleCechComplex X α M U)) ≫
        (moduleCechForgetIso X α M U).hom.f 0 := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let C := moduleCechComplex X α M U
  dsimp only [moduleCechAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change ((C.sc 0).mapHomologyIso G).inv ≫
      homologyMap (moduleCechForgetIso X α M U).hom 0 ≫
        CochainComplex.homologyZeroι ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj) =
    G.map (CochainComplex.homologyZeroι C) ≫ (moduleCechForgetIso X α M U).hom.f 0
  erw [CochainComplex.homologyZeroι_naturality]
  erw [← CochainComplex.mapHomologyIso_hom_homologyZeroι G C]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (hcover : iSup U = ⊤)

/-- The actual inverse comparison followed by the native embedding is the original augmentation. -/
@[reassoc]
theorem moduleCechH0Iso_inv_homologyZeroι :
    (moduleCechH0Iso X α M U hcover).inv ≫
      CochainComplex.homologyZeroι (moduleCechComplex X α M U) =
        cechAugmentationZero X U (moduleSectionsPresheaf X α M) := by
  rw [moduleCechH0Iso_inv, Category.assoc, CochainComplex.augmentation_homologyZeroι]
  rfl

/-- Global sections recovered from Cech homology restrict to the original zero-term cycle. -/
@[reassoc]
theorem moduleCechH0Iso_hom_augmentation :
    (moduleCechH0Iso X α M U hcover).hom ≫
        cechAugmentationZero X U (moduleSectionsPresheaf X α M) =
      CochainComplex.homologyZeroι (moduleCechComplex X α M U) := by
  apply (cancel_epi (moduleCechH0Iso X α M U hcover).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    moduleCechH0Iso_inv_homologyZeroι]

/-- Forgetting scalars retains exactly the original section restriction augmentation. -/
@[reassoc]
theorem moduleCechH0Iso_hom_additiveAugmentation :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (moduleCechH0Iso X α M U hcover).hom ≫
      cechAugmentationZero X U (moduleAddSheaf X M).obj =
    (moduleCechAdditiveHomologyIso X α M U 0).hom ≫
      CochainComplex.homologyZeroι ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj) := by
  rw [← moduleCechAugmentation_forget X α M U, ← Category.assoc, ← Functor.map_comp,
    moduleCechH0Iso_hom_augmentation]
  exact (moduleCechAdditiveHomologyIso_hom_homologyZeroι X α M U).symm

/-- The degree-zero linear cohomology comparison gives its original section under `equiv₀`. -/
theorem moduleCechCohomologyLinearEquivZero_equiv₀
    (x : (moduleCechComplex X α M U).homology 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
        (moduleCechCohomologyLinearEquivZero X α M U hcover x) =
      (moduleCechH0Iso X α M U hcover).hom x := by
  let := moduleCohomologyModuleOfHom X α M 0
  let : Module R Γ(M, ⊤) := Module.compHom _ α
  change moduleH0EquivOfHom X α M
      ((moduleH0EquivOfHom X α M).symm
        ((moduleTopSectionsIso X α M).hom ((moduleCechH0Iso X α M U hcover).hom x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
