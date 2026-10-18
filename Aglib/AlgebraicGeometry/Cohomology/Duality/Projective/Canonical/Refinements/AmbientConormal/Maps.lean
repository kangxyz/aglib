/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientNormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientDifferentials.Geometry

/-!
# Original conormal columns and unit differential vectors on open squares

Original unit-section morphisms let the native scalar adjunction and the
universal Kähler differential test actual sheaf arrows. The mixed square
retains those same unit sections before either conormal arrow is compared.
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

private theorem affineUnitSection_map {D : CommRingCat.{u}} {E E' : ModuleCat.{u} D}
    (f : E ⟶ E') (x : E) :
    canonicalAffineUnitSection E x ≫ (tilde.functor D).map f =
      canonicalAffineUnitSection E' (f x) := by
  apply (unitHomGlobalSectionsEquiv (Spec D) (tilde E')).injective
  change ((tilde.functor D).map f).val.app (op ⊤)
      ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec D, ⊤))) =
    (canonicalAffineUnitSection E' (f x)).val.app (op ⊤) (1 : Γ(Spec D, ⊤))
  rw [canonicalAffineUnitSection_app, canonicalAffineUnitSection_app]
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x

private theorem affineUnitSection_restrictPullback {A A' : CommRingCat.{u}}
    (φ : A ⟶ A') [IsOpenImmersion (Spec.map φ)] (E : ModuleCat.{u} A) (x : E) :
    (restrictUnitIso (Spec.map φ)).inv ≫
        (restrictFunctor (Spec.map φ)).map (canonicalAffineUnitSection E x) ≫
        (restrictFunctorIsoPullback (Spec.map φ)).hom.app (tilde E) ≫
        (tildePullbackIso φ).hom.app E =
      canonicalAffineUnitSection ((ModuleCat.extendScalars φ.hom).obj E)
        ((1 : A') ⊗ₜ[A,φ.hom] x) := by
  let j := Spec.map φ
  let F := restrictFunctor j
  let P := pullback j
  let u := canonicalAffineUnitSection E x
  let O := SheafOfModules.unit (Spec A).ringCatSheaf
  let e := restrictFunctorIsoPullback j
  have hu₀ : e.hom.app O ≫ (pullbackUnitIso j).hom = (restrictUnitIso j).hom :=
    restrictFunctorIsoPullback_hom_unit j
  have hu : (restrictUnitIso j).inv ≫ e.hom.app O = (pullbackUnitIso j).inv := by
    apply (cancel_mono (pullbackUnitIso j).hom).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (restrictUnitIso j).inv ≫ f) hu₀).trans
        ((restrictUnitIso j).inv_hom_id.trans (pullbackUnitIso j).inv_hom_id.symm))
  have hn := e.hom.naturality u
  change F.map u ≫ e.hom.app (tilde E) = e.hom.app O ≫ P.map u at hn
  have hs := congrArg (fun f => (restrictUnitIso j).inv ≫ f ≫
    (tildePullbackIso φ).hom.app E) hn
  have ht := congrArg (fun f => f ≫ P.map u ≫ (tildePullbackIso φ).hom.app E) hu
  calc
    _ = (restrictUnitIso j).inv ≫ e.hom.app O ≫ P.map u ≫
        (tildePullbackIso φ).hom.app E := by
      simpa only [Category.assoc] using hs
    _ = (pullbackUnitIso j).inv ≫ P.map u ≫ (tildePullbackIso φ).hom.app E := by
      simpa only [Category.assoc] using ht
    _ = _ := canonicalAffineUnitSection_pullback φ E x

/-- Original affine unit morphisms determine a map out of a tilde module. -/
theorem canonicalAffineTildeUnit_hom_ext {D : CommRingCat.{u}} (E : ModuleCat.{u} D)
    {N : (Spec D).Modules} {f g : tilde E ⟶ N}
    (h : ∀ x : E, canonicalAffineUnitSection E x ≫ f = canonicalAffineUnitSection E x ≫ g) :
    f = g := by
  apply ((tilde.adjunction (R := D)).homEquiv E N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := congrArg (unitHomGlobalSectionsEquiv (Spec D) N) (h x)
  change f.val.app (op ⊤)
      ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec D, ⊤))) =
    g.val.app (op ⊤)
      ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec D, ⊤))) at hx
  rw [canonicalAffineUnitSection_app] at hx
  exact hx

/-- Restrictions of original affine unit morphisms determine a map on an affine open. -/
theorem canonicalOpenAffineTildeUnit_hom_ext {D D' : CommRingCat.{u}}
    (j : Spec D' ⟶ Spec D) [IsOpenImmersion j] (E : ModuleCat.{u} D)
    {N : (Spec D').Modules} {f g : (tilde E).restrict j ⟶ N}
    (h : ∀ x : E, (restrictFunctor j).map (canonicalAffineUnitSection E x) ≫ f =
      (restrictFunctor j).map (canonicalAffineUnitSection E x) ≫ g) : f = g := by
  let adj := restrictAdjunction j
  apply (adj.homEquiv _ _).injective
  apply canonicalAffineTildeUnit_hom_ext E
  intro x
  have hf := adj.homEquiv_naturality_left (canonicalAffineUnitSection E x) f
  have hg := adj.homEquiv_naturality_left (canonicalAffineUnitSection E x) g
  exact hf.symm.trans ((congrArg (adj.homEquiv _ N) (h x)).trans hg)

private theorem mappedUnitIso_conjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O N E : C} {O' P T E' N' : D} (u : O ⟶ E) (a : N ≅ E)
    (v : O' ⟶ F.obj O) (b : F.obj E ⟶ P) (c : P ⟶ T) (k : T ⟶ E')
    (a' : N' ≅ E') (d : F.obj N ⟶ N')
    (hd : d = F.map a.hom ≫ b ≫ c ≫ k ≫ a'.inv) :
    v ≫ F.map (u ≫ a.inv) ≫ d = (v ≫ F.map u ≫ b ≫ c) ≫ k ≫ a'.inv := by
  rw [hd, F.map_comp]
  change v ≫ (F.map u ≫ (F.mapIso a).inv) ≫
      ((F.mapIso a).hom ≫ b ≫ c ≫ k ≫ a'.inv) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem appendTwo_eq {C : Type*} [Category C] {W X Y Z : C}
    {f g : W ⟶ X} (h : f = g) (k : X ⟶ Y) (l : Y ⟶ Z) :
    f ≫ k ≫ l = g ≫ k ≫ l := by
  rw [h]

private theorem appendOne_eq {C : Type*} [Category C] {W X Y : C}
    {f g : W ⟶ X} (h : f = g) (k : X ⟶ Y) : f ≫ k = g ≫ k := by
  rw [h]

private theorem affineUnitSection_open_map
    {A A' : CommRingCat.{u}} (φ : A ⟶ A') [IsOpenImmersion (Spec.map φ)]
    {N : (Spec A).Modules} {N' : (Spec A').Modules}
    {E : ModuleCat.{u} A} {E' : ModuleCat.{u} A'}
    (a : N ≅ tilde E) (a' : N' ≅ tilde E')
    (κ : (ModuleCat.extendScalars φ.hom).obj E ⟶ E')
    (d : N.restrict (Spec.map φ) ⟶ N')
    (hd : d = (restrictFunctor (Spec.map φ)).map a.hom ≫
      (restrictFunctorIsoPullback (Spec.map φ)).hom.app (tilde E) ≫
      (tildePullbackIso φ).hom.app E ≫ (tilde.functor A').map κ ≫ a'.inv) (x : E) :
    (restrictUnitIso (Spec.map φ)).inv ≫
        (restrictFunctor (Spec.map φ)).map (canonicalAffineUnitSection E x ≫ a.inv) ≫ d =
      canonicalAffineUnitSection E' (κ ((1 : A') ⊗ₜ[A,φ.hom] x)) ≫ a'.inv := by
  let j := Spec.map φ
  let F := restrictFunctor j
  have h₀ := mappedUnitIso_conjugation (C := (Spec A).Modules) (D := (Spec A').Modules)
    F (canonicalAffineUnitSection E x) a (restrictUnitIso j).inv
    ((restrictFunctorIsoPullback j).hom.app (tilde E))
    ((tildePullbackIso φ).hom.app E) ((tilde.functor A').map κ) a' d hd
  have h₁ := appendTwo_eq (C := (Spec A').Modules)
    (affineUnitSection_restrictPullback φ E x) ((tilde.functor A').map κ) a'.inv
  have h₂ := congrArg (fun f :
      SheafOfModules.unit (Spec A').ringCatSheaf ⟶ tilde E' => f ≫ a'.inv)
    (affineUnitSection_map κ ((1 : A') ⊗ₜ[A,φ.hom] x))
  exact h₀.trans (h₁.trans h₂)

/-- Original differential unit sections carry their native scalar-adjoint vector through
the actual ambient open differential comparison. -/
theorem canonicalAmbientDifferentialOpenIso_unitSection
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (x : CommRingCat.KaehlerDifferential α) :
    (restrictUnitIso (Spec.map φ)).inv ≫
        (restrictFunctor (Spec.map φ)).map (canonicalDifferentialUnitSection α x) ≫
        (canonicalAmbientDifferentialOpenIso α φ).hom =
      canonicalDifferentialUnitSection (α ≫ φ)
        (canonicalAmbientDifferentialMap α φ ((1 : A') ⊗ₜ[A,φ.hom] x)) := by
  have hg := canonicalAmbientDifferentialMap_geometry α φ (by simp [Spec.map_comp])
  change (canonicalAmbientDifferentialOpenIso α φ).hom = _ at hg
  exact affineUnitSection_open_map φ (relativeDifferentialAffineIso α)
    (relativeDifferentialAffineIso (α ≫ φ)) (canonicalAmbientDifferentialMap α φ)
    (canonicalAmbientDifferentialOpenIso α φ).hom hg x

/-- In particular the actual ambient open comparison preserves the original ring differential. -/
theorem canonicalAmbientDifferentialOpenIso_d_unitSection
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (a : A) :
    (restrictUnitIso (Spec.map φ)).inv ≫
        (restrictFunctor (Spec.map φ)).map
          (canonicalDifferentialUnitSection α (CommRingCat.KaehlerDifferential.d (f := α) a)) ≫
        (canonicalAmbientDifferentialOpenIso α φ).hom =
      canonicalDifferentialUnitSection (α ≫ φ)
        (CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a)) := by
  have h := canonicalAmbientDifferentialOpenIso_unitSection α φ
    (CommRingCat.KaehlerDifferential.d (f := α) a)
  rw [canonicalAmbientDifferentialMap_one_tmul] at h
  exact h

private theorem mixedUnitSection_map
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion j] (H : p ≫ f = q ≫ j)
    {M : Y.Modules} {M' : V.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (v' : SheafOfModules.unit V.ringCatSheaf ⟶ M')
    (a : M.restrict j ⟶ M')
    (ha : (restrictUnitIso j).inv ≫ (restrictFunctor j).map v ≫ a = v') :
    (restrictUnitIso p).inv ≫
        (restrictFunctor p).map ((pullbackUnitIso f).inv ≫ (pullback f).map v) ≫
        ((pullbackOpenSquare p q f j H).hom.app M ≫ (pullback q).map a) =
      (pullbackUnitIso q).inv ≫ (pullback q).map v' := by
  let P := pullback q
  let u := (restrictUnitIso j).inv ≫ (restrictFunctor j).map v
  have hs := canonicalOpenPullbackSquare_section p q f j H v
  have h₀ := appendOne_eq (C := W.Modules) hs (P.map a)
  have h₁ := congrArg (fun z => (pullbackUnitIso q).inv ≫ P.map z) ha
  calc
    _ = ((pullbackUnitIso q).inv ≫ P.map u) ≫ P.map a := by
      simpa only [Category.assoc] using h₀
    _ = (pullbackUnitIso q).inv ≫ P.map (u ≫ a) := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => (pullbackUnitIso q).inv ≫ z) (P.map_comp u a).symm)
    _ = _ := h₁

/-- The actual mixed middle map carries a pulled original vector to the pullback
of its actual scalar-adjoint ambient image. -/
theorem canonicalAmbientConormalMiddleIso_unitSection
    {R A A' B B' : CommRingCat.{u}} (α : R ⟶ A)
    (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ τ = σ ≫ ψ) (x : CommRingCat.KaehlerDifferential α) :
    (restrictUnitIso (Spec.map ψ)).inv ≫
        (restrictFunctor (Spec.map ψ)).map
          ((pullbackUnitIso (Spec.map σ)).inv ≫
            (pullback (Spec.map σ)).map (canonicalDifferentialUnitSection α x)) ≫
        (canonicalAmbientConormalMiddleIso α φ σ τ ψ h).hom =
      (pullbackUnitIso (Spec.map τ)).inv ≫
        (pullback (Spec.map τ)).map (canonicalDifferentialUnitSection (α ≫ φ)
          (canonicalAmbientDifferentialMap α φ ((1 : A') ⊗ₜ[A,φ.hom] x))) := by
  exact mixedUnitSection_map (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ)
    (canonicalAmbientClosedSquare φ σ τ ψ h)
    (canonicalDifferentialUnitSection α x)
    (canonicalDifferentialUnitSection (α ≫ φ)
      (canonicalAmbientDifferentialMap α φ ((1 : A') ⊗ₜ[A,φ.hom] x)))
    (canonicalAmbientDifferentialOpenIso α φ).hom
    (canonicalAmbientDifferentialOpenIso_unitSection α φ x)

end AlgebraicGeometry.Scheme.Modules
