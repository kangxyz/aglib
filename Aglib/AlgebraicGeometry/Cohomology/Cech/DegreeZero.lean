/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Degree-zero Cech computation over arbitrary structural rings

Sheaf gluing identifies the kernel of the actual first Cech differential with
global sections. The native augmentation therefore computes degree-zero
homology, linearly over any specified structural ring. No quasicoherence or
affine-intersection premise is needed in degree zero.
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
  (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The unchanged augmentation viewed with its structural ring. -/
abbrev moduleCechAugmentation := cechAugmentation X U (moduleSectionsPresheaf X α M)

/-- The actual augmented degree-zero short complex. -/
def moduleCechAugmentationShort : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (cechAugmentationZero X U (moduleSectionsPresheaf X α M))
    ((moduleCechComplex X α M U).d 0 1)
    (cechAugmentationZero_d X U (moduleSectionsPresheaf X α M))

/-- Forgetting scalars preserves the original restriction augmentation. -/
theorem moduleCechAugmentation_forget :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (cechAugmentationZero X U (moduleSectionsPresheaf X α M)) ≫
      (moduleCechForgetIso X α M U).hom.f 0 =
        cechAugmentationZero X U (moduleAddSheaf X M).obj := by
  apply Pi.hom_ext (f := fun b : Fin 1 → ι =>
    (moduleAddSheaf X M).obj.obj (op (∏ᶜ fun k => U (b k))))
  intro b
  rw [Category.assoc, moduleCechForgetIso_hom_f_π, ← Functor.map_comp,
    cechAugmentationZero_π, cechAugmentationZero_π]
  rfl

/-- The augmented short complex is the original additive one after forgetting scalars. -/
def moduleCechAugmentationShortForgetIso :
    (moduleCechAugmentationShort X α M U).map
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≅
      ShortComplex.mk (cechAugmentationZero X U (moduleAddSheaf X M).obj)
        (((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).d 0 1)
        (cechAugmentationZero_d X U (moduleAddSheaf X M).obj) := by
  refine ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval _ _ 0).mapIso (moduleCechForgetIso X α M U))
    ((HomologicalComplex.eval _ _ 1).mapIso (moduleCechForgetIso X α M U)) ?_ ?_
  · change 𝟙 _ ≫ cechAugmentationZero X U (moduleAddSheaf X M).obj =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          (cechAugmentationZero X U (moduleSectionsPresheaf X α M)) ≫
        (moduleCechForgetIso X α M U).hom.f 0
    rw [CategoryTheory.Category.id_comp]
    exact (moduleCechAugmentation_forget X α M U).symm
  · change (moduleCechForgetIso X α M U).hom.f 0 ≫
        (((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).d 0 1) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((moduleCechComplex X α M U).d 0 1) ≫
        (moduleCechForgetIso X α M U).hom.f 1
    exact (moduleCechForgetIso X α M U).hom.comm 0 1

variable (hcover : iSup U = ⊤)

include hcover

/-- An actual open cover makes its structural-ring augmentation exact and monic. -/
theorem moduleCechAugmentation_exact_mono :
    (moduleCechAugmentationShort X α M U).Exact ∧
      Mono (cechAugmentationZero X U (moduleSectionsPresheaf X α M)) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have he := (ShortComplex.exact_and_mono_f_iff_of_iso
    (moduleCechAugmentationShortForgetIso X α M U)).mpr
      ⟨additiveCechAugmentation_exact X U (moduleAddSheaf X M) hcover,
        additiveCechAugmentation_mono X U (moduleAddSheaf X M) hcover⟩
  refine ⟨(ShortComplex.exact_map_iff_of_faithful _ G).mp he.1, ?_⟩
  exact G.mono_of_mono_map he.2

/-- The actual augmentation induces an isomorphism on native degree-zero homology. -/
theorem moduleCechAugmentation_quasiIsoAt_zero :
    QuasiIsoAt (moduleCechAugmentation X α M U) 0 := by
  have he := moduleCechAugmentation_exact_mono X α M U hcover
  have : Mono ((moduleCechAugmentation X α M U).f 0) := by
    simpa only [moduleCechAugmentation, cechAugmentation_f_zero] using he.2
  apply CochainComplex.quasiIsoAtZero_of_augmentation_exact
  simpa only [moduleCechAugmentation, cechAugmentation_f_zero, moduleCechAugmentationShort]
    using he.1

/-- Original degree-zero Cech homology is the actual structural-ring global-section module. -/
def moduleCechH0Iso :
    (moduleCechComplex X α M U).homology 0 ≅
      (moduleSectionsPresheaf X α M).obj (op ⊤) := by
  let := moduleCechAugmentation_quasiIsoAt_zero X α M U hcover
  exact (asIso (homologyMap (moduleCechAugmentation X α M U) 0)).symm ≪≫
    singleObjHomologySelfIso (.up ℕ) 0 _

/-- The augmentation gives its original inverse formula under the degree-zero comparison. -/
theorem moduleCechH0Iso_inv :
    (moduleCechH0Iso X α M U hcover).inv =
      (singleObjHomologySelfIso (.up ℕ) 0
        ((moduleSectionsPresheaf X α M).obj (op ⊤))).inv ≫
          homologyMap (moduleCechAugmentation X α M U) 0 := rfl

/-- The actual `Sheaf.H` is computed linearly in degree zero over every structural ring. -/
def moduleCechCohomologyLinearEquivZero :
    letI := moduleCohomologyModuleOfHom X α M 0
    (moduleCechComplex X α M U).homology 0 ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) 0 := by
  letI := moduleCohomologyModuleOfHom X α M 0
  letI : Module R Γ(M, ⊤) := Module.compHom _ α
  exact ((moduleCechH0Iso X α M U hcover ≪≫ moduleTopSectionsIso X α M).toLinearEquiv).trans
    (moduleH0EquivOfHom X α M).symm

end AlgebraicGeometry.Scheme.Cohomology
