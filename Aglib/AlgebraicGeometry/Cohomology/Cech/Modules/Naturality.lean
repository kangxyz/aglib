/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Forget

/-!
# Coefficient naturality of the structural-ring Cech comparison

Original module-sheaf coefficient maps act on the unchanged structural-ring Cech complex.
Forgetting scalars and the native homology comparison preserve these actual maps. The
resulting cohomology naturality uses the same structural ring map and the same `Sheaf.H`.
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
  {M N : X.Modules} {ι : Type u} (U : ι → X.Opens)

/-- The original Cech cochain map induced by a module-sheaf coefficient morphism. -/
abbrev moduleCechMap (φ : M ⟶ N) :
    moduleCechComplex X α M U ⟶ moduleCechComplex X α N U :=
  (cechComplexFunctor U).map ((moduleSectionsPresheafFunctor X α).map φ)

/-- Scalar forgetting preserves the original Cech coefficient map. -/
theorem moduleCechForgetIso_naturality (φ : M ⟶ N) :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (moduleCechMap X α U φ) ≫ (moduleCechForgetIso X α N U).hom =
      (moduleCechForgetIso X α M U).hom ≫
        (cechComplexFunctor U).map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let f : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N :=
    (moduleSectionsPresheafFunctor X α).map φ
  let g : (moduleAddSheaf X M).obj ⟶ (moduleAddSheaf X N).obj :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom
  ext n : 1
  apply Pi.hom_ext (f := fun b : Fin (n + 1) → ι =>
    (moduleAddSheaf X N).obj.obj (op (∏ᶜ fun k => U (b k))))
  intro b
  simp only [comp_f, Category.assoc]
  rw [moduleCechForgetIso_hom_f_π]
  change G.map (Limits.Pi.map
      (fun z : Fin (n + 1) → ι => f.app (op (∏ᶜ fun k => U (z k))))) ≫
      G.map (Pi.π (fun z : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf X α N).obj (op (∏ᶜ fun k => U (z k)))) b) =
    (moduleCechForgetIso X α M U).hom.f n ≫
      Limits.Pi.map (fun z : Fin (n + 1) → ι => g.app (op (∏ᶜ fun k => U (z k)))) ≫
      Pi.π (fun z : Fin (n + 1) → ι =>
        (moduleAddSheaf X N).obj.obj (op (∏ᶜ fun k => U (z k)))) b
  rw [← Functor.map_comp, Pi.map_π, Functor.map_comp, Pi.map_π, ← Category.assoc]
  erw [moduleCechForgetIso_hom_f_π]
  rfl

/-- The native scalar-forgetting homology isomorphism is natural in actual module
coefficients, in every degree and with no quasicoherence hypothesis. -/
theorem moduleCechAdditiveHomologyIso_naturality (φ : M ⟶ N) (n : ℕ)
    (x : (moduleCechComplex X α M U).homology n) :
    (moduleCechAdditiveHomologyIso X α N U n).hom
        (homologyMap (moduleCechMap X α U φ) n x) =
      homologyMap ((cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) n
          ((moduleCechAdditiveHomologyIso X α M U n).hom x) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let C := moduleCechComplex X α M U
  let δ := moduleCechMap X α U φ
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map δ) G
  have hc := congrArg (fun g => homologyMap g n) (moduleCechForgetIso_naturality X α U φ)
  simp only [homologyMap_comp] at hc
  have h : G.map (homologyMap δ n) ≫ (moduleCechAdditiveHomologyIso X α N U n).hom =
      (moduleCechAdditiveHomologyIso X α M U n).hom ≫
        homologyMap ((cechComplexFunctor U).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) n := by
    dsimp only [moduleCechAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc]
    exact congrArg (fun k => ((C.sc n).mapHomologyIso G).inv ≫ k) hc
  exact ConcreteCategory.congr_hom h x

/-- The original coefficient map preserves the structural-ring augmentation in degree zero. -/
theorem moduleCechAugmentationZero_naturality (φ : M ⟶ N) :
    ((moduleSectionsPresheafFunctor X α).map φ).app (op ⊤) ≫
        cechAugmentationZero X U (moduleSectionsPresheaf X α N) =
      cechAugmentationZero X U (moduleSectionsPresheaf X α M) ≫
        (moduleCechMap X α U φ).f 0 := by
  let f : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N :=
    (moduleSectionsPresheafFunctor X α).map φ
  have h := congrArg (fun t => t.f 0) (cechAugmentation_naturality X U f)
  simp only [comp_f, CochainComplex.single₀_map_f_zero, cechAugmentation_f_zero] at h
  exact h

/-- Global sections recovered from native Cech homology retain the actual coefficient map. -/
theorem moduleCechH0Iso_naturality (hcover : iSup U = ⊤) (φ : M ⟶ N) :
    homologyMap (moduleCechMap X α U φ) 0 ≫ (moduleCechH0Iso X α N U hcover).hom =
      (moduleCechH0Iso X α M U hcover).hom ≫
        ((moduleSectionsPresheafFunctor X α).map φ).app (op ⊤) := by
  let : Mono (cechAugmentationZero X U (moduleSectionsPresheaf X α N)) :=
    (moduleCechAugmentation_exact_mono X α N U hcover).2
  apply (cancel_mono (cechAugmentationZero X U (moduleSectionsPresheaf X α N))).mp
  rw [Category.assoc, moduleCechH0Iso_hom_augmentation,
    CochainComplex.homologyZeroι_naturality, Category.assoc,
    moduleCechAugmentationZero_naturality, ← Category.assoc,
    moduleCechH0Iso_hom_augmentation]

/-- The original degree-zero Cech comparison is natural in actual module coefficients,
with no quasicoherence or affine-intersection hypothesis. -/
theorem moduleCechCohomologyLinearEquivZero_naturality (hcover : iSup U = ⊤)
    (φ : M ⟶ N) (x : (moduleCechComplex X α M U).homology 0) :
    moduleCechCohomologyLinearEquivZero X α N U hcover
        (homologyMap (moduleCechMap X α U φ) 0 x) =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) 0
        (moduleCechCohomologyLinearEquivZero X α M U hcover x) := by
  apply (Sheaf.H.equiv₀ (moduleAddSheaf X N) isTerminalTop).injective
  rw [← Sheaf.H.equiv₀_naturality, moduleCechCohomologyLinearEquivZero_equiv₀,
    moduleCechCohomologyLinearEquivZero_equiv₀]
  exact ConcreteCategory.congr_hom (moduleCechH0Iso_naturality X α U hcover φ) x

/-- The original positive-degree structural-ring Cech comparison is natural in every actual
coefficient map, using the original chosen additive injective resolutions. -/
theorem moduleCechCohomologyLinearEquiv_naturality [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hcover : iSup U = ⊤)
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (I : InjectiveResolution (moduleAddSheaf X M))
    (J : InjectiveResolution (moduleAddSheaf X N)) (φ : M ⟶ N) (n : ℕ)
    (x : (moduleCechComplex X α M U).homology (n + 1)) :
    moduleCechCohomologyLinearEquiv X α N U hcover haff J n
        (homologyMap (moduleCechMap X α U φ) (n + 1) x) =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) (n + 1)
        (moduleCechCohomologyLinearEquiv X α M U hcover haff I n x) := by
  let f : moduleAddSheaf X M ⟶ moduleAddSheaf X N :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  let δ : InjectiveResolution.Hom I J f :=
    ⟨InjectiveResolution.desc f J I, by simp⟩
  change moduleCechCohomologyAddEquiv U N J hcover haff n
      ((moduleCechAdditiveHomologyIso X α N U (n + 1)).hom
        (homologyMap (moduleCechMap X α U φ) (n + 1) x)) =
    Sheaf.H.map f (n + 1) (moduleCechCohomologyAddEquiv U M I hcover haff n
      ((moduleCechAdditiveHomologyIso X α M U (n + 1)).hom x))
  rw [moduleCechAdditiveHomologyIso_naturality]
  exact moduleCechCohomologyAddEquiv_naturality U hcover haff δ n _

/-- The single all-degree Cech comparison for a quasicoherent module and an affine-intersection
cover, retaining the native degree-zero augmentation and positive comparison. -/
def moduleCechCohomologyLinearEquivAll (M : X.Modules) [M.IsQuasicoherent]
    (hcover : iSup U = ⊤)
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (I : InjectiveResolution (moduleAddSheaf X M)) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    (moduleCechComplex X α M U).homology n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  cases n with
  | zero => exact moduleCechCohomologyLinearEquivZero X α M U hcover
  | succ n => exact moduleCechCohomologyLinearEquiv X α M U hcover haff I n

/-- In every degree the original coefficient map on Cech homology is the actual `Sheaf.H.map`
under the structural-ring linear comparison. -/
theorem moduleCechCohomologyLinearEquivAll_naturality
    [M.IsQuasicoherent] [N.IsQuasicoherent] (hcover : iSup U = ⊤)
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
    (I : InjectiveResolution (moduleAddSheaf X M))
    (J : InjectiveResolution (moduleAddSheaf X N)) (φ : M ⟶ N) (n : ℕ)
    (x : (moduleCechComplex X α M U).homology n) :
    moduleCechCohomologyLinearEquivAll X α U N hcover haff J n
        (homologyMap (moduleCechMap X α U φ) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n
        (moduleCechCohomologyLinearEquivAll X α U M hcover haff I n x) := by
  cases n with
  | zero => exact moduleCechCohomologyLinearEquivZero_naturality X α U hcover φ x
  | succ n =>
    exact moduleCechCohomologyLinearEquiv_naturality X α U hcover haff I J φ n x

end AlgebraicGeometry.Scheme.Cohomology
