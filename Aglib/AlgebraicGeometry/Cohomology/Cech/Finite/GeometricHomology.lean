/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend.Homology
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.GeometricUnit

/-!
# Original additive homology normalization in integer Cech degrees

Forgetting scalars before or after the native retained-degree homology
comparison gives the same original additive Cech homology map. The integer
base-change arrow therefore retains the original geometric unit on homology
for every ring homomorphism.
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

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The native scalar-forgetting and retained-degree comparisons identify
actual integer Cech homology with the unchanged additive Cech homology. -/
def moduleCechIntAdditiveHomologyIso (q : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((moduleCechIntComplex X α U M).homology (q : ℤ)) ≅
      ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).homology q :=
  (((moduleCechIntComplex X α U M).sc (q : ℤ)).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    (homologyFunctor AddCommGrpCat.{u} (.up ℤ) (q : ℤ)).mapIso
      (moduleCechIntForgetIso X α M U) ≪≫
    ((cechComplexFunctor U).obj (moduleAddSheaf X M).obj).extendHomologyIso
      ComplexShape.embeddingUpNat rfl

/-- The same original integer comparison factors through the original
module retained-degree comparison and the original natural-number
scalar-forgetting comparison. -/
theorem moduleCechIntAdditiveHomologyIso_hom (q : ℕ) :
    (moduleCechIntAdditiveHomologyIso X α M U q).hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((moduleCechComplex X α M U).extendHomologyIso
            ComplexShape.embeddingUpNat (j := q) rfl).hom ≫
        (moduleCechAdditiveHomologyIso X α M U q).hom := by
  let K := moduleCechComplex X α M U
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let e := ComplexShape.embeddingUpNat
  have h := K.mapExtendIso_hom_homologyMap F e (j := q) (j' := (q : ℤ)) rfl
  have hh := congrArg (fun t =>
      (((K.extend e).sc (q : ℤ)).mapHomologyIso F).inv ≫ t ≫
        ((K.sc q).mapHomologyIso F).inv ≫
          homologyMap (moduleCechForgetIso X α M U).hom q) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] at hh
  dsimp only [moduleCechIntAdditiveHomologyIso, moduleCechIntForgetIso,
    moduleCechAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [homologyFunctor_map, ComplexShape.Embedding.extendFunctor_map]
  rw [homologyMap_comp]
  simp only [Category.assoc]
  rw [HomologicalComplex.extendHomologyIso_hom_naturality]
  simpa only [K, F, e, moduleCechIntComplex, moduleCechIntFunctor,
    moduleCechComplex, moduleSectionsPresheafFunctor, Functor.comp_obj,
    ComplexShape.Embedding.extendFunctor_obj] using hh

variable {X} {B : Type u} [CommRing B] (f : X ⟶ Spec (CommRingCat.of R))
  (σ : R →+* B) [Finite ι]

/-- The original integer Cech base-change arrow, composed with the native
homology mate, has the original additive geometric pure-unit formula.
Scalar extension need not preserve homology. -/
theorem moduleCechIntBaseChangeHomologyMap_one_tmul (q : ℕ)
    (x : (moduleCechIntComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).homology
      (q : ℤ)) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    (moduleCechIntAdditiveHomologyIso Y β N (fun i => p ⁻¹ᵁ U i) q).hom
        (homologyMap (moduleCechIntBaseChangeMap f σ M U) (q : ℤ)
          (extendScalarsHomologyMap σ (moduleCechIntComplex X α U M) (q : ℤ)
            ((1 : B) ⊗ₜ[R,σ] x))) =
      homologyMap
        (additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
          (moduleCoefficientPullback p
            ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M))) q
        ((moduleCechIntAdditiveHomologyIso X α M U q).hom x) := by
  dsimp only
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N := (Scheme.Modules.pullback p).obj M
  let C := moduleCechIntComplex X α U M
  let D := moduleCechIntComplex Y β (fun i => p ⁻¹ᵁ U i) N
  let g := additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
    (moduleCoefficientPullback p
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M))
  have h := ModuleCat.extendScalarsForgetUnit_homology_map_of_square σ C (q : ℤ) D
    (moduleCechIntBaseChangeMap f σ M U)
    (moduleCechIntForgetIso X α M U).hom
    (moduleCechIntForgetIso Y β N (fun i => p ⁻¹ᵁ U i)).hom
    (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
    (moduleCechIntBaseChangeMap_forget_unit σ f M U)
  have hx := ConcreteCategory.congr_hom h x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply,
    ModuleCat.extendScalarsForgetUnit_app_apply] at hx
  dsimp only [moduleCechIntAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [ConcreteCategory.comp_apply, homologyFunctor_map]
  erw [hx]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality g ComplexShape.embeddingUpNat
      (j := q) (j' := (q : ℤ)) rfl) _

end AlgebraicGeometry.Scheme.Cohomology
