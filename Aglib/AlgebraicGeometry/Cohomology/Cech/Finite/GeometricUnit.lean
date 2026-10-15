/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.IntBaseChange

/-!
# The original geometric unit on the integer Cech complex

The scalar-forgetting comparison and the original Cech pullback unit commute
with native extension by zero. These are actual chain squares for every ring
map, without a flatness or homology-preservation hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Forgetting scalars on the unchanged integer Cech complex retains the
original comparison followed by the original extended additive comparison. -/
def moduleCechIntForgetIso {R : Type u} [CommRing R]
    (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj
        (moduleCechIntComplex X α U M) ≅
      ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).extend
        ComplexShape.embeddingUpNat :=
  (moduleCechComplex X α M U).mapExtendIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapIso
      (moduleCechForgetIso X α M U)

variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B]
  (p : Y ⟶ X) (σ : R →+* B)
  (α : R →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤))
  (hσ : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules} {ι : Type u} [Finite ι]
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : ι → X.Opens)

/-- The actual Cech scalar-extension square retains its original additive
geometric unit after native extension to the integers. -/
theorem moduleCechIntTensorMapAlong_forget_unit :
    (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℤ)).app
          (moduleCechIntComplex X α U M) ≫
        ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map
          (((moduleCechComplex X α M U).mapExtendIso
              (ModuleCat.extendScalars σ) ComplexShape.embeddingUpNat).hom ≫
            HomologicalComplex.extendMap
              (moduleCechTensorMapAlong p σ α β hσ φ U) ComplexShape.embeddingUpNat) ≫
        (moduleCechIntForgetIso Y β N (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechIntForgetIso X α M U).hom ≫
        HomologicalComplex.extendMap
          (additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
            (moduleCoefficientPullback p φ)) ComplexShape.embeddingUpNat := by
  have h := (moduleCechComplex X α M U).mapExtendIso_hom_natTrans_square
    (ModuleCat.extendScalars σ)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
    (ModuleCat.extendScalarsForgetUnit σ) ComplexShape.embeddingUpNat
    (moduleCechComplex Y β N (fun i => p ⁻¹ᵁ U i))
    ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj)
    ((cechComplexFunctor (fun i => p ⁻¹ᵁ U i)).obj (moduleAddSheaf Y N).obj)
    (moduleCechTensorMapAlong p σ α β hσ φ U)
    (moduleCechForgetIso X α M U).hom
    (moduleCechForgetIso Y β N (fun i => p ⁻¹ᵁ U i)).hom
    (additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φ))
    (moduleCechTensorMapAlong_forget_unit p σ α β hσ φ U)
  simpa only [moduleCechIntForgetIso, moduleCechIntComplex, moduleCechIntFunctor,
    moduleSectionsPresheafFunctor, moduleCechComplex,
    Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj,
    Iso.trans_hom, Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc] using h

/-- The original integer base-change arrow has exactly the original
ordinary pullback unit as its additive geometric chain map, for every ring map. -/
theorem moduleCechIntBaseChangeMap_forget_unit
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : ι → X.Opens) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℤ)).app
          (moduleCechIntComplex X α U M) ≫
        ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map
          (moduleCechIntBaseChangeMap f σ M U) ≫
        (moduleCechIntForgetIso (pullback f (Spec.map (CommRingCat.ofHom σ))) β N
          (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechIntForgetIso X α M U).hom ≫
        HomologicalComplex.extendMap
          (additiveCechGeometricMap p U (moduleAddSheaf X M)
            (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ))) N)
            (moduleCoefficientPullback p
              ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)))
          ComplexShape.embeddingUpNat := by
  simpa only [Functor.id_obj, moduleCechIntBaseChangeMap, moduleCechBaseChangeMap,
    ComplexShape.Embedding.extendFunctor_map] using
    moduleCechIntTensorMapAlong_forget_unit
      (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) σ _ _
      (moduleSectionsBaseChangeScalars _ _ f σ pullback.condition)
      ((Scheme.Modules.pullbackPushforwardAdjunction _).unit.app M) U

end AlgebraicGeometry.Scheme.Cohomology
