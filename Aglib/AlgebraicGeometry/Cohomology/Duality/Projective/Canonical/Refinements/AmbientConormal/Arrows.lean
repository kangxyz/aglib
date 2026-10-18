/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Positive

/-!
# Actual positive conormal arrows on an open square

All three columns are the original geometric maps, expressed through the
original affine module comparisons. Original kernel classes determine the
first column and original unit tensors of differentials determine the
second column. The two positive conormal squares are checked on those
same classes and differentials.
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

private theorem unitIsoConjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O N E : C} {O' N' E' : D} (e : N ≅ E) (e' : N' ≅ E')
    (r : F.obj O ≅ O') (v : O ⟶ N) (v' : O' ⟶ N')
    (u : O ⟶ E) (u' : O' ⟶ E') (a : F.obj N ⟶ N')
    (hv : v ≫ e.hom = u) (hv' : v' ≫ e'.hom = u')
    (ha : F.map v ≫ a = r.hom ≫ v') :
    F.map u ≫ (F.map e.inv ≫ a ≫ e'.hom) = r.hom ≫ u' := by
  rw [← hv, F.map_comp]
  change (F.map v ≫ (F.mapIso e).hom) ≫
    ((F.mapIso e).inv ≫ a ≫ e'.hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ha, Category.assoc, hv']

private theorem unnormalizeUnitIso
    {C : Type*} [Category C] {O O' N : C} (r : O ≅ O')
    (f : O ⟶ N) (g : O' ⟶ N) (h : r.inv ≫ f = g) : f = r.hom ≫ g := by
  exact (r.hom_inv_id_assoc f).symm.trans
    (congrArg (fun k => r.hom ≫ k) h)

private theorem unitIso_inv_cancel
    {C : Type*} [Category C] {O N E : C} (e : N ≅ E)
    (v : O ⟶ N) (u : O ⟶ E) (h : v = u ≫ e.inv) : v ≫ e.hom = u := by
  rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem affineUnit_test {D : CommRingCat.{u}} (E : ModuleCat.{u} D)
    {N : (Spec D).Modules} {f g : tilde E ⟶ N} (x : E)
    (h : canonicalAffineUnitSection E x ≫ f = canonicalAffineUnitSection E x ≫ g) :
    ((tilde.adjunction (R := D)).homEquiv E N f) x =
      ((tilde.adjunction (R := D)).homEquiv E N g) x := by
  have hx := congrArg (unitHomGlobalSectionsEquiv (Spec D) N) h
  change f.val.app (op ⊤)
      ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec D, ⊤))) =
    g.val.app (op ⊤)
      ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec D, ⊤))) at hx
  rw [canonicalAffineUnitSection_app] at hx
  exact hx

/-- Original differential tensors determine a map from their original tilde module
after open restriction. -/
theorem canonicalOpenDifferentialTensor_hom_ext
    {R A B D : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (j : Spec D ⟶ Spec B) [IsOpenImmersion j]
    {N : (Spec D).Modules}
    {f g : (tilde ((ModuleCat.extendScalars σ.hom).obj
      (CommRingCat.KaehlerDifferential α))).restrict j ⟶ N}
    (h : ∀ a : A, (restrictFunctor j).map (canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)) ≫ f =
      (restrictFunctor j).map (canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)) ≫ g) :
    f = g := by
  let E := (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)
  let adj := restrictAdjunction j
  apply (adj.homEquiv _ _).injective
  apply ((tilde.adjunction (R := B)).homEquiv _ _).injective
  apply canonicalAmbientDifferentialMap_ext α σ
  intro a
  let x : E := ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)
  have hf := adj.homEquiv_naturality_left (canonicalAffineUnitSection E x) f
  have hg := adj.homEquiv_naturality_left (canonicalAffineUnitSection E x) g
  exact affineUnit_test E x
    (hf.symm.trans ((congrArg (adj.homEquiv _ N) (h a)).trans hg))

/-- Every original affine cotangent vector is the class of an actual kernel element. -/
theorem canonicalConormalAffineClass_surjective
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) :
    Function.Surjective (relativeConormalAffineClass α σ hσ) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  exact Algebra.Extension.Cotangent.mk_surjective

variable {R A A' B B' : CommRingCat.{u}} (α : R ⟶ A)
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ τ = σ ≫ ψ) (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)

/-- The original normal open map, in the original affine cotangent coordinates. -/
def canonicalAmbientConormalTildeNormalMap :
    (tilde (relativeConormalAffineModule α σ hσ)).restrict (Spec.map ψ) ⟶
      tilde (relativeConormalAffineModule (α ≫ φ) τ hτ) :=
  (restrictFunctor (Spec.map ψ)).map
      (relativeConormalAffineIdealPullbackIso α σ hσ).inv ≫
    canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ) (Spec.map φ) (Spec.map ψ)
      (canonicalAmbientClosedSquare φ σ τ ψ h) ≫
    (relativeConormalAffineIdealPullbackIso (α ≫ φ) τ hτ).hom

omit hσ hτ in
/-- The original mixed middle map, in the original scalar-extended differential coordinates. -/
def canonicalAmbientConormalTildeMiddleMap :
    (tilde ((ModuleCat.extendScalars σ.hom).obj
      (CommRingCat.KaehlerDifferential α))).restrict (Spec.map ψ) ⟶
        tilde ((ModuleCat.extendScalars τ.hom).obj
          (CommRingCat.KaehlerDifferential (α ≫ φ))) :=
  (restrictFunctor (Spec.map ψ)).map (relativeConormalAffineMiddleIso α σ).inv ≫
    (canonicalAmbientConormalMiddleIso α φ σ τ ψ h).hom ≫
    (relativeConormalAffineMiddleIso (α ≫ φ) τ).hom

omit hσ hτ in
/-- The original tangent open map, in the original affine differential coordinates. -/
def canonicalAmbientConormalTildeTangentMap :
    (tilde (CommRingCat.KaehlerDifferential (α ≫ σ))).restrict (Spec.map ψ) ⟶
      tilde (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ τ)) :=
  (restrictFunctor (Spec.map ψ)).map (relativeDifferentialAffineIso (α ≫ σ)).inv ≫
    (canonicalAmbientConormalTangentIso α φ σ τ ψ h).hom ≫
    (relativeDifferentialAffineIso ((α ≫ φ) ≫ τ)).hom

/-- The original normal map carries the original kernel class to its actual image. -/
theorem canonicalAmbientConormalTildeNormalMap_class
    (x : RingHom.ker σ.hom) (y : RingHom.ker τ.hom) (hxy : φ (x : A) = y) :
    (restrictFunctor (Spec.map ψ)).map
        (canonicalAffineUnitSection (relativeConormalAffineModule α σ hσ)
          (relativeConormalAffineClass α σ hσ x)) ≫
        canonicalAmbientConormalTildeNormalMap α φ σ τ ψ h hσ hτ =
      (restrictUnitIso (Spec.map ψ)).hom ≫
        canonicalAffineUnitSection (relativeConormalAffineModule (α ≫ φ) τ hτ)
          (relativeConormalAffineClass (α ≫ φ) τ hτ y) := by
  exact unitIsoConjugation (restrictFunctor (Spec.map ψ))
    (relativeConormalAffineIdealPullbackIso α σ hσ)
    (relativeConormalAffineIdealPullbackIso (α ≫ φ) τ hτ)
    (restrictUnitIso (Spec.map ψ)) (canonicalAffineNormalSectionHom σ x)
    (canonicalAffineNormalSectionHom τ y) _ _ _
    (canonicalAffineNormalSectionHom_affineClass α σ hσ x)
    (canonicalAffineNormalSectionHom_affineClass (α ≫ φ) τ hτ y)
    (canonicalAffineNormalSectionHom_openSquare σ τ φ ψ
      (canonicalAmbientClosedSquare φ σ τ ψ h) x y hxy)

omit hσ hτ in
/-- The original middle map carries each original positive differential tensor to its image. -/
theorem canonicalAmbientConormalTildeMiddleMap_d
    (a : A) :
    (restrictFunctor (Spec.map ψ)).map (canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)) ≫
        canonicalAmbientConormalTildeMiddleMap α φ σ τ ψ h =
      (restrictUnitIso (Spec.map ψ)).hom ≫ canonicalAffineUnitSection
        ((ModuleCat.extendScalars τ.hom).obj (CommRingCat.KaehlerDifferential (α ≫ φ)))
        ((1 : B') ⊗ₜ[A',τ.hom]
          CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a)) := by
  let x := CommRingCat.KaehlerDifferential.d (f := α) a
  let y := CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a)
  have hm := canonicalAmbientConormalMiddleIso_unitSection α φ σ τ ψ h x
  rw [canonicalAmbientDifferentialMap_one_tmul] at hm
  have hn := unnormalizeUnitIso (restrictUnitIso (Spec.map ψ))
    ((restrictFunctor (Spec.map ψ)).map
      ((pullbackUnitIso (Spec.map σ)).inv ≫
        (pullback (Spec.map σ)).map (canonicalDifferentialUnitSection α x)) ≫
      (canonicalAmbientConormalMiddleIso α φ σ τ ψ h).hom)
    ((pullbackUnitIso (Spec.map τ)).inv ≫
      (pullback (Spec.map τ)).map (canonicalDifferentialUnitSection (α ≫ φ) y)) hm
  exact unitIsoConjugation (restrictFunctor (Spec.map ψ))
    (relativeConormalAffineMiddleIso α σ) (relativeConormalAffineMiddleIso (α ≫ φ) τ)
    (restrictUnitIso (Spec.map ψ)) _ _ _ _ _
    (unitIso_inv_cancel _ _ _ (canonicalDifferentialUnitSection_pullback_hom α σ x))
    (unitIso_inv_cancel _ _ _ (canonicalDifferentialUnitSection_pullback_hom (α ≫ φ) τ y)) hn

private theorem differentialOpenSquare_d_unit
    {R D D' : CommRingCat.{u}} (ρ : R ⟶ D) (β : R ⟶ D') (δ : D ⟶ D')
    [IsOpenImmersion (Spec.map δ)] (hβ : β = ρ ≫ δ)
    (H : Spec.map δ ≫ Spec.map ρ = Spec.map β ≫ 𝟙 (Spec R)) (a : D) :
    (restrictUnitIso (Spec.map δ)).inv ≫
        (restrictFunctor (Spec.map δ)).map
          (canonicalDifferentialUnitSection ρ (CommRingCat.KaehlerDifferential.d (f := ρ) a)) ≫
        (relativeDifferentialOpenSquareIso (Spec.map ρ) (Spec.map δ) (Spec.map β)
          (𝟙 (Spec R)) H).hom =
      canonicalDifferentialUnitSection β (CommRingCat.KaehlerDifferential.d (f := β) (δ a)) := by
  subst β
  exact canonicalAmbientDifferentialOpenIso_d_unitSection ρ δ a

omit hσ hτ [IsOpenImmersion (Spec.map φ)] in
/-- The original tangent map carries an original quotient differential to its actual image. -/
theorem canonicalAmbientConormalTildeTangentMap_d (b : B) :
    (restrictFunctor (Spec.map ψ)).map
        (canonicalAffineUnitSection (CommRingCat.KaehlerDifferential (α ≫ σ))
          (CommRingCat.KaehlerDifferential.d (f := α ≫ σ) b)) ≫
        canonicalAmbientConormalTildeTangentMap α φ σ τ ψ h =
      (restrictUnitIso (Spec.map ψ)).hom ≫
        canonicalAffineUnitSection (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ τ))
          (CommRingCat.KaehlerDifferential.d (f := (α ≫ φ) ≫ τ) (ψ b)) := by
  have hβ : (α ≫ φ) ≫ τ = (α ≫ σ) ≫ ψ := by
    simpa only [Category.assoc] using congrArg (fun k => α ≫ k) h
  have hd := differentialOpenSquare_d_unit (α ≫ σ) ((α ≫ φ) ≫ τ) ψ hβ
    (canonicalAmbientSourceSquare α φ σ τ ψ h) b
  have hn := unnormalizeUnitIso (restrictUnitIso (Spec.map ψ)) _ _ hd
  exact unitIsoConjugation (restrictFunctor (Spec.map ψ))
    (relativeDifferentialAffineIso (α ≫ σ))
    (relativeDifferentialAffineIso ((α ≫ φ) ≫ τ))
    (restrictUnitIso (Spec.map ψ)) _ _ _ _ _
    (unitIso_inv_cancel _ _ _ (rfl : canonicalDifferentialUnitSection (α ≫ σ)
      (CommRingCat.KaehlerDifferential.d (f := α ≫ σ) b) = _))
    (unitIso_inv_cancel _ _ _ (rfl : canonicalDifferentialUnitSection ((α ≫ φ) ≫ τ)
      (CommRingCat.KaehlerDifferential.d (f := (α ≫ φ) ≫ τ) (ψ b)) = _)) hn

end AlgebraicGeometry.Scheme.Modules
