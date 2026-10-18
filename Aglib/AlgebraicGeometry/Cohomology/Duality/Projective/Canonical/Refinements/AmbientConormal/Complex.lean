/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Arrows

/-!
# The actual conormal complex map on an affine open square

The original positive kernel and differential formulas prove both squares.
Conjugation by the original affine complex comparison retains the original
geometric middle and tangent arrows and the original normal map.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem mapComp_append {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y : C} {Z : D} (u : W ⟶ X) (f : X ⟶ Y) (a : F.obj Y ⟶ Z) :
    F.map u ≫ (F.map f ≫ a) = F.map (u ≫ f) ≫ a :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ a) (F.map_comp u f).symm)

private theorem conormal_f_class_unit
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    canonicalAffineUnitSection (relativeConormalAffineModule α σ hσ)
        (relativeConormalAffineClass α σ hσ x) ≫
        (tilde.functor B).map (relativeConormalAffineLinearF α σ hσ) =
      canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) (x : A)) := by
  rw [← canonicalAffineNormalSectionHom_affineClass α σ hσ x, Category.assoc]
  exact canonicalAffineConormal_f_unit α σ hσ x

variable {R A A' B B' : CommRingCat.{u}} (α : R ⟶ A)
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ τ = σ ≫ ψ) (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)

/-- The actual first positive conormal square, in the original affine coordinates. -/
theorem canonicalAmbientConormalTilde_f :
    canonicalAmbientConormalTildeNormalMap α φ σ τ ψ h hσ hτ ≫
        (tilde.functor B').map (relativeConormalAffineLinearF (α ≫ φ) τ hτ) =
      (restrictFunctor (Spec.map ψ)).map
          ((tilde.functor B).map (relativeConormalAffineLinearF α σ hσ)) ≫
        canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h := by
  let F := restrictFunctor (Spec.map ψ)
  let E := relativeConormalAffineModule α σ hσ
  let E' := relativeConormalAffineModule (α ≫ φ) τ hτ
  let M := (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)
  let M' := (ModuleCat.extendScalars τ.hom).obj (CommRingCat.KaehlerDifferential (α ≫ φ))
  let f := (tilde.functor B).map (relativeConormalAffineLinearF α σ hσ)
  let f' := (tilde.functor B').map (relativeConormalAffineLinearF (α ≫ φ) τ hτ)
  let n := canonicalAmbientConormalTildeNormalMap α φ σ τ ψ h hσ hτ
  let m := canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h
  let r := restrictUnitIso (Spec.map ψ)
  apply canonicalOpenAffineTildeUnit_hom_ext (Spec.map ψ) E
  intro z
  obtain ⟨x, rfl⟩ := canonicalConormalAffineClass_surjective α σ hσ z
  have hx : τ (φ (x : A)) = 0 := by
    have H := congrArg (fun k : A ⟶ B' => k (x : A)) h
    change τ (φ (x : A)) = ψ (σ (x : A)) at H
    exact H.trans ((congrArg ψ.hom x.property).trans (map_zero ψ.hom))
  let y : RingHom.ker τ.hom := ⟨φ (x : A), hx⟩
  let u := canonicalAffineUnitSection E (relativeConormalAffineClass α σ hσ x)
  let u' := canonicalAffineUnitSection E' (relativeConormalAffineClass (α ≫ φ) τ hτ y)
  let v := canonicalAffineUnitSection M
    ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) (x : A))
  let v' := canonicalAffineUnitSection M'
    ((1 : B') ⊗ₜ[A',τ.hom] CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ (x : A)))
  have hnf : F.map u ≫ (n ≫ f') = r.hom ≫ v' := by
    calc
      _ = (F.map u ≫ n) ≫ f' := (Category.assoc _ _ _).symm
      _ = (r.hom ≫ u') ≫ f' := congrArg (fun k => k ≫ f')
        (canonicalAmbientConormalTildeNormalMap_class α φ σ τ ψ h hσ hτ x y rfl)
      _ = r.hom ≫ (u' ≫ f') := Category.assoc _ _ _
      _ = _ := congrArg (fun k => r.hom ≫ k) (conormal_f_class_unit (α ≫ φ) τ hτ y)
  have hfm : F.map u ≫ (F.map f ≫ m) = r.hom ≫ v' := by
    calc
      _ = F.map (u ≫ f) ≫ m := mapComp_append F u f m
      _ = F.map v ≫ m := congrArg (fun k => F.map k ≫ m)
        (conormal_f_class_unit α σ hσ x)
      _ = _ := canonicalAmbientConormalTildeMiddleMap_d α φ σ τ ψ h (x : A)
  exact hnf.trans hfm.symm

/-- The actual second positive conormal square, in the original affine coordinates. -/
theorem canonicalAmbientConormalTilde_g :
    canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h ≫
        (tilde.functor B').map (relativeConormalAffineLinearG (α ≫ φ) τ hτ) =
      (restrictFunctor (Spec.map ψ)).map
          ((tilde.functor B).map (relativeConormalAffineLinearG α σ hσ)) ≫
        canonicalAmbientConormalTildeTangentMap α φ σ τ ψ h := by
  let F := restrictFunctor (Spec.map ψ)
  let M := (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)
  let M' := (ModuleCat.extendScalars τ.hom).obj (CommRingCat.KaehlerDifferential (α ≫ φ))
  let Q := CommRingCat.KaehlerDifferential (α ≫ σ)
  let Q' := CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ τ)
  let g := (tilde.functor B).map (relativeConormalAffineLinearG α σ hσ)
  let g' := (tilde.functor B').map (relativeConormalAffineLinearG (α ≫ φ) τ hτ)
  let m := canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h
  let t := canonicalAmbientConormalTildeTangentMap α φ σ τ ψ h
  let r := restrictUnitIso (Spec.map ψ)
  apply canonicalOpenDifferentialTensor_hom_ext α σ (Spec.map ψ)
  intro a
  let u := canonicalAffineUnitSection M
    ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)
  let u' := canonicalAffineUnitSection M'
    ((1 : B') ⊗ₜ[A',τ.hom] CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a))
  let v := canonicalAffineUnitSection Q (CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a))
  let v' := canonicalAffineUnitSection Q'
    (CommRingCat.KaehlerDifferential.d (f := (α ≫ φ) ≫ τ) (τ (φ a)))
  have hmg : F.map u ≫ (m ≫ g') = r.hom ≫ v' := by
    calc
      _ = (F.map u ≫ m) ≫ g' := (Category.assoc _ _ _).symm
      _ = (r.hom ≫ u') ≫ g' := congrArg (fun k => k ≫ g')
        (canonicalAmbientConormalTildeMiddleMap_d α φ σ τ ψ h a)
      _ = r.hom ≫ (u' ≫ g') := Category.assoc _ _ _
      _ = _ := congrArg (fun k => r.hom ≫ k)
        (canonicalAffineConormal_g_unit (α ≫ φ) τ hτ (φ a))
  have hgt : F.map u ≫ (F.map g ≫ t) = r.hom ≫ v' := by
    calc
      _ = F.map (u ≫ g) ≫ t := mapComp_append F u g t
      _ = F.map v ≫ t := congrArg (fun k => F.map k ≫ t)
        (canonicalAffineConormal_g_unit α σ hσ a)
      _ = r.hom ≫ canonicalAffineUnitSection Q'
          (CommRingCat.KaehlerDifferential.d (f := (α ≫ φ) ≫ τ) (ψ (σ a))) :=
        canonicalAmbientConormalTildeTangentMap_d α φ σ τ ψ h (σ a)
      _ = _ := congrArg (fun b : B' => r.hom ≫ canonicalAffineUnitSection Q'
        (CommRingCat.KaehlerDifferential.d (f := (α ≫ φ) ≫ τ) b))
        (congrArg (fun k : A ⟶ B' => k a) h.symm)
  exact hmg.trans hgt.symm

/-- The original geometric columns form an actual map of the original affine module complexes. -/
def canonicalAmbientConormalTildeComplexMap :
    ((relativeConormalAffineLinearComplex α σ hσ).map (tilde.functor B)).map
        (restrictFunctor (Spec.map ψ)) ⟶
      (relativeConormalAffineLinearComplex (α ≫ φ) τ hτ).map (tilde.functor B') where
  τ₁ := canonicalAmbientConormalTildeNormalMap α φ σ τ ψ h hσ hτ
  τ₂ := canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h
  τ₃ := canonicalAmbientConormalTildeTangentMap α φ σ τ ψ h
  comm₁₂ := canonicalAmbientConormalTilde_f α φ σ τ ψ h hσ hτ
  comm₂₃ := canonicalAmbientConormalTilde_g α φ σ τ ψ h hσ hτ

/-- The actual geometric conormal map uses only the original affine complex comparisons. -/
def canonicalAmbientConormalComplexMap :
    (relativeConormalAffineComplex α σ hσ).map (restrictFunctor (Spec.map ψ)) ⟶
      relativeConormalAffineComplex (α ≫ φ) τ hτ :=
  (restrictFunctor (Spec.map ψ)).mapShortComplex.map
      (relativeConormalAffineComplexIso α σ hσ).hom ≫
    canonicalAmbientConormalTildeComplexMap α φ σ τ ψ h hσ hτ ≫
      (relativeConormalAffineComplexIso (α ≫ φ) τ hτ).inv

private theorem conjugatedIso_recover
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {N E : C} {N' E' : D} (e : N ≅ E) (e' : N' ≅ E') (a : F.obj N ⟶ N') :
    F.map e.hom ≫ (F.map e.inv ≫ a ≫ e'.hom) ≫ e'.inv = a := by
  change (F.mapIso e).hom ≫ ((F.mapIso e).inv ≫ a ≫ e'.hom) ≫ e'.inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The native complex map retains the original middle differential comparison. -/
theorem canonicalAmbientConormalComplexMap_middle :
    (canonicalAmbientConormalComplexMap α φ σ τ ψ h hσ hτ).τ₂ =
      (canonicalAmbientConormalMiddleIso α φ σ τ ψ h).hom := by
  exact conjugatedIso_recover (restrictFunctor (Spec.map ψ))
    (relativeConormalAffineMiddleIso α σ) (relativeConormalAffineMiddleIso (α ≫ φ) τ)
    (canonicalAmbientConormalMiddleIso α φ σ τ ψ h).hom

/-- The native complex map retains the original tangent differential comparison. -/
theorem canonicalAmbientConormalComplexMap_tangent :
    (canonicalAmbientConormalComplexMap α φ σ τ ψ h hσ hτ).τ₃ =
      (canonicalAmbientConormalTangentIso α φ σ τ ψ h).hom := by
  exact conjugatedIso_recover (restrictFunctor (Spec.map ψ))
    (relativeDifferentialAffineIso (α ≫ σ))
    (relativeDifferentialAffineIso ((α ≫ φ) ≫ τ))
    (canonicalAmbientConormalTangentIso α φ σ τ ψ h).hom

/-- The native first column is the same original normal map through the original affine classes. -/
theorem canonicalAmbientConormalComplexMap_normal :
    (restrictFunctor (Spec.map ψ)).map
        (relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫
        (canonicalAmbientConormalComplexMap α φ σ τ ψ h hσ hτ).τ₁ =
      canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ) (Spec.map φ) (Spec.map ψ)
          (canonicalAmbientClosedSquare φ σ τ ψ h) ≫
        (relativeConormalAffineIdealPullbackIso (α ≫ φ) τ hτ).hom := by
  change (restrictFunctor (Spec.map ψ)).map
      (relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫
    ((restrictFunctor (Spec.map ψ)).map (𝟙 _) ≫
      canonicalAmbientConormalTildeNormalMap α φ σ τ ψ h hσ hτ ≫ 𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    canonicalAmbientConormalTildeNormalMap]
  change ((restrictFunctor (Spec.map ψ)).mapIso
      (relativeConormalAffineIdealPullbackIso α σ hσ)).hom ≫
    (((restrictFunctor (Spec.map ψ)).mapIso
      (relativeConormalAffineIdealPullbackIso α σ hσ)).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end AlgebraicGeometry.Scheme.Modules
