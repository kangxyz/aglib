/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology.Forget
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules

/-! # Canonical finite Cech base change with module coefficients

The complex map is assembled from the native finite-product coefficient
comparison, the original section tensor map, and the native preimage-of-opens
comparison. For a finite affine family in a separated scheme it is an
isomorphism after every homomorphism of commutative rings. Flatness is not
needed at the level of complexes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
  (p : Y ⟶ X) (σ : A →+* B)
  (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤))
  (hσ : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules} {ι : Type u}

/-- The native preimage-of-opens comparison on the original module Cech complex. -/
def moduleCechGeometricIso (N : Y.Modules) (U : ι → X.Opens) :
    (cechComplexFunctor U).obj ((Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β N) ≅
      moduleCechComplex Y β N (fun i => p ⁻¹ᵁ U i) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} B)).mapIso
    (cechCosimplicialChangeIso (Opens.map p.base) U (moduleSectionsPresheaf Y β N))

/-- The geometric comparison restricts along the native preservation-of-products map. -/
theorem moduleCechGeometricIso_hom_f_π (N : Y.Modules) (U : ι → X.Opens)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (moduleCechGeometricIso p β N U).hom.f n ≫
        Pi.π (fun a : Fin (n + 1) → ι =>
          (moduleSectionsPresheaf Y β N).obj (op (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))) a =
      Pi.π (fun a : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf Y β N).obj (op (p ⁻¹ᵁ (∏ᶜ fun k => U (a k))))) a ≫
        (moduleSectionsPresheaf Y β N).map
          (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op := by
  change (Pi.mapIso fun a : Fin (n + 1) → ι =>
    ((moduleSectionsPresheaf Y β N).mapIso
      (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).op).symm).hom ≫ _ = _
  erw [Pi.mapIso_hom_π]
  rfl

/-- Canonical scalar extension of the finite Cech complex through an actual coefficient arrow. -/
def moduleCechTensorMapAlong [Finite ι]
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens) :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj
        (moduleCechComplex X α M U) ⟶
      moduleCechComplex Y β N (fun i => p ⁻¹ᵁ U i) :=
  (finiteCechComplexCoefficientIso (ModuleCat.extendScalars σ) U
    (moduleSectionsPresheaf X α M)).hom ≫
      (cechComplexFunctor U).map (moduleSectionsTensorMapAlong p α β σ hσ φ) ≫
        (moduleCechGeometricIso p β N U).hom

/-- On every tuple intersection, the coefficient comparison uses the actual original
section tensor map after the original product projection. -/
theorem moduleCechTensorMapAlong_f_π [Finite ι]
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (moduleCechTensorMapAlong p σ α β hσ φ U).f n ≫
        (moduleCechGeometricIso p β N U).inv.f n ≫
        Pi.π (fun a : Fin (n + 1) → ι =>
          (moduleSectionsPresheaf Y β N).obj (op (p ⁻¹ᵁ (∏ᶜ fun k => U (a k))))) a =
      (ModuleCat.extendScalars σ).map
        (Pi.π (fun a : Fin (n + 1) → ι =>
          (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k => U (a k)))) a) ≫
        (moduleSectionsTensorMapAlong p α β σ hσ φ).app (op (∏ᶜ fun k => U (a k))) := by
  have hg := congrArg (fun k => k.f n) (moduleCechGeometricIso p β N U).hom_inv_id
  simp only [comp_f, id_f] at hg
  dsimp only [moduleCechTensorMapAlong]
  simp only [comp_f, Category.assoc]
  rw [← Category.assoc ((moduleCechGeometricIso p β N U).hom.f n)
    ((moduleCechGeometricIso p β N U).inv.f n), hg, Category.id_comp]
  change (𝟙 _ ≫ piComparison (ModuleCat.extendScalars σ)
    (fun a : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k => U (a k))))) ≫
    Limits.Pi.map (fun a : Fin (n + 1) → ι =>
      (moduleSectionsTensorMapAlong p α β σ hσ φ).app (op (∏ᶜ fun k => U (a k)))) ≫ _ = _
  rw [Category.id_comp, Pi.map_π, ← Category.assoc, piComparison_comp_π]

/-- The original Cech tensor map on a tuple is the original section tensor map followed
by the actual geometric restriction on that tuple intersection. -/
theorem moduleCechTensorMapAlong_f_π_preimage [Finite ι]
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (moduleCechTensorMapAlong p σ α β hσ φ U).f n ≫
        Pi.π (fun a : Fin (n + 1) → ι =>
          (moduleSectionsPresheaf Y β N).obj (op (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))) a =
      (ModuleCat.extendScalars σ).map
        (Pi.π (fun a : Fin (n + 1) → ι =>
          (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k => U (a k)))) a) ≫
        (moduleSectionsTensorMapAlong p α β σ hσ φ).app (op (∏ᶜ fun k => U (a k))) ≫
        (moduleSectionsPresheaf Y β N).map
          (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op := by
  have hg := congrArg (fun k => k.f n) (moduleCechGeometricIso p β N U).inv_hom_id
  simp only [comp_f, id_f] at hg
  calc
    _ = (moduleCechTensorMapAlong p σ α β hσ φ U).f n ≫
        (moduleCechGeometricIso p β N U).inv.f n ≫
        (moduleCechGeometricIso p β N U).hom.f n ≫ _ := by
      rw [← Category.assoc ((moduleCechGeometricIso p β N U).inv.f n)
        ((moduleCechGeometricIso p β N U).hom.f n), hg, Category.id_comp]
    _ = _ := by
      rw [moduleCechGeometricIso_hom_f_π]
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (moduleSectionsPresheaf Y β N).map
          (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op)
        (moduleCechTensorMapAlong_f_π p σ α β hσ φ U n a)

/-- The unchanged additive geometric Cech map has the same original coefficient and
geometric restriction formula on every tuple intersection. -/
theorem moduleAdditiveCechGeometricMap_f_π
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φ)).f n ≫
        Pi.π (fun a : Fin (n + 1) → ι =>
          N.presheaf.obj (op (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))) a =
      Pi.π (fun a : Fin (n + 1) → ι =>
        M.presheaf.obj (op (∏ᶜ fun k => U (a k)))) a ≫
        φ.mapPresheaf.app (op (∏ᶜ fun k => U (a k))) ≫
        N.presheaf.map
          (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op := by
  unfold additiveCechGeometricMap moduleCoefficientPullback
  rw [Equiv.apply_symm_apply]
  dsimp [additiveCechFunctor, TopCat.Sheaf.Cech.additiveCechFunctor,
    modulePushforwardAddSheafIso, additiveCechPushforwardIso,
    cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, cechCosimplicialChangeIso]
  simp only [Category.assoc]
  erw [Pi.mapIso_hom_π, Pi.map_π_assoc]
  rfl

/-- The scalar-forgetting unit square retains the original additive geometric Cech map. -/
theorem moduleCechTensorMapAlong_forget_unit [Finite ι]
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens) :
    (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℕ)).app
          (moduleCechComplex X α M U) ≫
        ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map
          (moduleCechTensorMapAlong p σ α β hσ φ U) ≫
        (moduleCechForgetIso Y β N (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechForgetIso X α M U).hom ≫
        additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
          (moduleCoefficientPullback p φ) := by
  ext n : 1
  apply Pi.hom_ext (f := fun a : Fin (n + 1) → ι =>
    N.presheaf.obj (op (∏ᶜ fun k => p ⁻¹ᵁ U (a k))))
  intro a
  simp only [comp_f, Category.assoc]
  erw [moduleCechForgetIso_hom_f_π Y β N (fun i => p ⁻¹ᵁ U i) n a]
  change (ModuleCat.extendScalarsForgetUnit σ).app ((moduleCechComplex X α M U).X n) ≫
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      ((moduleCechTensorMapAlong p σ α β hσ φ U).f n) ≫
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      (Pi.π (fun a : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf Y β N).obj (op (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))) a) = _
  erw [← Functor.map_comp, moduleCechTensorMapAlong_f_π_preimage p σ α β hσ φ U n a]
  erw [moduleAdditiveCechGeometricMap_f_π p φ U n a]
  simp only [← Category.assoc]
  erw [moduleCechForgetIso_hom_f_π X α M U n a]
  ext m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  change (moduleSectionsPresheaf Y β N).map _
      ((moduleSectionsTensorMapAlong p α β σ hσ φ).app _
        ((ModuleCat.extendScalars σ).map _ ((1 : B) ⊗ₜ[A,σ] m))) = _
  erw [ModuleCat.ExtendScalars.map_tmul, moduleSectionsTensorMapAlong_one_tmul]
  rfl

/-- The actual unit section comparison is invertible on all tuple intersections of an
affine family in a separated scheme. -/
theorem moduleCechTensorComparison_isIso [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (M : X.Modules) [M.IsQuasicoherent] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso ((cechComplexFunctor U).map (moduleSectionsBaseChangeMap f σ M)) := by
  have hn (n : ℕ) : IsIso (((cechComplexFunctor U).map
      (moduleSectionsBaseChangeMap f σ M)).f n) := by
    have hi (a : Fin (n + 1) → ι) :
        IsIso ((moduleSectionsBaseChangeMap f σ M).app (op (∏ᶜ fun k => U (a k)))) := by
      apply moduleSectionsBaseChangeMap_isIso_app
      have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => hU (a k))
    let := hi
    change IsIso (Limits.Pi.map (fun a : Fin (n + 1) → ι =>
      (moduleSectionsBaseChangeMap f σ M).app (op (∏ᶜ fun k => U (a k)))))
    infer_instance
  let := hn
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical finite Cech tensor map on the actual fibre product, with the original
geometric pullback unit as its coefficient arrow. -/
def moduleCechBaseChangeMap (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (M : X.Modules) [Finite ι] (U : ι → X.Opens) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj
      (moduleCechComplex X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) M U) ⟶
      moduleCechComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        ((Scheme.Modules.pullback p).obj M) (fun i => p ⁻¹ᵁ U i) :=
  moduleCechTensorMapAlong _ σ _ _
    (moduleSectionsBaseChangeScalars _ _ f σ pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction _).unit.app M) U

/-- Every ring homomorphism gives an isomorphism of the original Cech complexes for a finite
affine family in a separated scheme and arbitrary quasicoherent coefficients. -/
theorem moduleCechBaseChangeMap_isIso [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (M : X.Modules) [M.IsQuasicoherent] [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsIso (moduleCechBaseChangeMap f σ M U) := by
  have := moduleCechTensorComparison_isIso f σ M U hU
  change IsIso ((finiteCechComplexCoefficientIso (ModuleCat.extendScalars σ) U
    (moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) M)).hom ≫
      (cechComplexFunctor U).map (moduleSectionsBaseChangeMap f σ M) ≫ _)
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
