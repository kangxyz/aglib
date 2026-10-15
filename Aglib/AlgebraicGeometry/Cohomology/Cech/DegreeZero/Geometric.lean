/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Forget
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules

/-!
# Geometric naturality of the original degree-zero Cech comparison

The actual geometric Cech map preserves the original restriction augmentation.
Consequently the linear zero-degree comparison is natural for the unchanged
geometric map on `Sheaf.H`. Only the actual open cover and the displayed
equality on additive Cech homology are used; neither quasicoherence nor affine
intersections are needed.
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

variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)

/-- The original additive geometric map preserves the actual cochain augmentation. -/
theorem additiveCechGeometricMap_augmentation
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) :
    cechAugmentation Y U A.obj ≫ additiveCechGeometricMap p U A B a =
      (CochainComplex.single₀ AddCommGrpCat.{u}).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _
            a).hom.app (op ⊤) ≫ (pushforwardSectionsIso p).hom.app B) ≫
        cechAugmentation X (fun i => p ⁻¹ᵁ U i) B.obj := by
  let t := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _ a
  change cechAugmentation Y U A.obj ≫
      ((cechComplexFunctor U).map t.hom ≫ (additiveCechPushforwardIso p U).hom.app B) = _
  rw [← Category.assoc, ← cechAugmentation_naturality Y U t.hom,
    Category.assoc, additiveCechPushforwardIso_augmentation, ← Category.assoc, ← Functor.map_comp]

variable {M : Y.Modules} {N : X.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)

/-- The module coefficient arrow gives the original section-level augmentation square. -/
theorem moduleAdditiveCechGeometricMap_augmentation_zero :
    cechAugmentationZero Y U (moduleAddSheaf Y M).obj ≫
        (additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
          (moduleCoefficientPullback p φ)).f 0 =
      (((SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
          (modulePushforwardAddSheafIso p N).hom).hom.app (op ⊤)) ≫
        (pushforwardSectionsIso p).hom.app (moduleAddSheaf X N) ≫
          cechAugmentationZero X (fun i => p ⁻¹ᵁ U i) (moduleAddSheaf X N).obj := by
  have h := congrArg (fun f => f.f 0)
    (additiveCechGeometricMap_augmentation p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
      (moduleCoefficientPullback p φ))
  simp only [comp_f, cechAugmentation_f_zero, CochainComplex.single₀_map_f_zero] at h
  simpa only [moduleCoefficientPullback, Equiv.apply_symm_apply, Category.assoc] using h

variable {R S : Type u} [CommRing R] [CommRing S]
  (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤)) (hcover : iSup U = ⊤)

/-- The degree-zero linear comparison is natural for the actual geometric cohomology map. -/
theorem moduleCechCohomologyLinearEquivZero_geometric
    (x : (moduleCechComplex Y α M U).homology 0)
    (y : (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).homology 0)
    (hxy : (moduleCechAdditiveHomologyIso X β N (fun i => p ⁻¹ᵁ U i) 0).hom y =
      homologyMap (additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
        (moduleCoefficientPullback p φ)) 0
          ((moduleCechAdditiveHomologyIso Y α M U 0).hom x)) :
    moduleCechCohomologyLinearEquivZero X β N (fun i => p ⁻¹ᵁ U i)
        (p.iSup_preimage_eq_top hcover) y =
      moduleCohomologyMapAlong p φ 0 (moduleCechCohomologyLinearEquivZero Y α M U hcover x) := by
  apply (Sheaf.H.equiv₀ (moduleAddSheaf X N) isTerminalTop).injective
  rw [moduleCechCohomologyLinearEquivZero_equiv₀, moduleCohomologyMapAlong_equiv₀,
    moduleCechCohomologyLinearEquivZero_equiv₀]
  let V := fun i => p ⁻¹ᵁ U i
  let g := additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
    (moduleCoefficientPullback p φ)
  let : Mono (cechAugmentationZero X V (moduleAddSheaf X N).obj) :=
    additiveCechAugmentation_mono X V (moduleAddSheaf X N) (p.iSup_preimage_eq_top hcover)
  apply (AddCommGrpCat.mono_iff_injective
    (cechAugmentationZero X V (moduleAddSheaf X N).obj)).mp inferInstance
  have h₁ := ConcreteCategory.congr_hom
    (moduleCechH0Iso_hom_additiveAugmentation X β N V (p.iSup_preimage_eq_top hcover)) y
  have h₂ := ConcreteCategory.congr_hom
    (moduleCechH0Iso_hom_additiveAugmentation Y α M U hcover) x
  have hn := ConcreteCategory.congr_hom (CochainComplex.homologyZeroι_naturality g)
    ((moduleCechAdditiveHomologyIso Y α M U 0).hom x)
  have ha := ConcreteCategory.congr_hom
    (moduleAdditiveCechGeometricMap_augmentation_zero p U φ)
    ((moduleCechH0Iso Y α M U hcover).hom x)
  simp only [ConcreteCategory.comp_apply] at h₁ h₂ hn ha
  change cechAugmentationZero X V (moduleAddSheaf X N).obj
    ((moduleCechH0Iso X β N V (p.iSup_preimage_eq_top hcover)).hom y) = _ at h₁
  change cechAugmentationZero Y U (moduleAddSheaf Y M).obj
    ((moduleCechH0Iso Y α M U hcover).hom x) = _ at h₂
  change cechAugmentationZero X V (moduleAddSheaf X N).obj
      ((moduleCechH0Iso X β N V (p.iSup_preimage_eq_top hcover)).hom y) = _
  rw [h₁, hxy]
  exact hn.trans ((congrArg (g.f 0) h₂.symm).trans ha)

end AlgebraicGeometry.Scheme.Cohomology
