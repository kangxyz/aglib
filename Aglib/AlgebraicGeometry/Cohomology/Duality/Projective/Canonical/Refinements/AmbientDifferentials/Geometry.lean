/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientDifferentials

/-!
# The original affine differential map under ambient open restriction

The original restriction, pullback, tilde and scalar adjunctions identify the
actual open-square differential map by its values on unit tensors of d(a).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem ambientOpenSquare_adjoint_d
    {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ X) [IsOpenImmersion i]
    (g : W ⟶ Z) (j : Z ⟶ Y) [IsOpenImmersion j] (h : i ≫ f = g ≫ j)
    (V : X.Opens) (a : Γ(X, V)) :
    ((restrictAdjunction i).homEquiv _ _
      (relativeDifferentialOpenSquareIso f i g j h).hom).val.app (op V)
        ((relativeDifferentialDerivation f).d a) =
      (relativeDifferentialDerivation g).d (i.app V a) := by
  let v := (relativeDifferentialCongrIso (i ≫ f) h).hom ≫
    (relativeDifferentialBaseOpenIso g j).hom
  have hR : (restrictAdjunction i).homEquiv _ _ (relativeDifferentialRestrictHom f i) =
      relativeDifferentialDesc f _
        (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f))) := by
    unfold relativeDifferentialRestrictHom
    exact Equiv.apply_symm_apply _ _
  have he : (restrictAdjunction i).homEquiv _ _
        (relativeDifferentialOpenSquareIso f i g j h).hom =
      relativeDifferentialDesc f _
          (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f))) ≫
        (pushforward i).map v := by
    change (restrictAdjunction i).homEquiv _ _ (relativeDifferentialRestrictHom f i ≫ v) = _
    rw [Adjunction.homEquiv_naturality_right, hR]
  have hd := ConcreteCategory.congr_hom
    (congrArg (fun k => k.val.app (op V)) he) ((relativeDifferentialDerivation f).d a)
  refine hd.trans ?_
  change (relativeDifferentialBaseOpenIso g j).hom.val.app (op (i ⁻¹ᵁ V))
      ((relativeDifferentialCongrIso (i ≫ f) h).hom.val.app (op (i ⁻¹ᵁ V))
        ((relativeDifferentialDesc f _
          (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f)))).val.app
            (op V) ((relativeDifferentialDerivation f).d a))) = _
  rw [relativeDifferentialDesc_d]
  change (relativeDifferentialBaseOpenIso g j).hom.val.app (op (i ⁻¹ᵁ V))
      ((relativeDifferentialCongrIso (i ≫ f) h).hom.val.app (op (i ⁻¹ᵁ V))
        ((relativeDifferentialDerivation (i ≫ f)).d (i.app V a))) = _
  rw [relativeDifferentialCongrIso_hom_d, relativeDifferentialBaseOpenIso_hom_d]

private theorem ambientRestrictPullback_homEquiv
    {W X : Scheme.{u}} (i : W ⟶ X) [IsOpenImmersion i]
    (M : X.Modules) (N : W.Modules) (k : (pullback i).obj M ⟶ N) :
    (restrictAdjunction i).homEquiv M N ((restrictFunctorIsoPullback i).hom.app M ≫ k) =
      (pullbackPushforwardAdjunction i).homEquiv M N k := by
  rw [restrictFunctorIsoPullback, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem ambientTilde_toOpen {A : CommRingCat.{u}} {M N : ModuleCat.{u} A}
    (κ : M ⟶ N) (V : (Spec A).Opens) (m : M) :
    ((tilde.functor A).map κ).val.app (op V) (tilde.toOpen M V m) =
      tilde.toOpen N V (κ m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app κ V) m

private theorem ambientPushforwardΓ_apply {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    (N : (Spec A').Modules) (z : Γ(N, ⊤)) :
    (pushforwardGlobalSectionsIso φ).hom.app N z = z := by
  rfl

private theorem ambientAffineSection_map {A A' : CommRingCat.{u}} (φ : A ⟶ A') (a : A) :
    (Spec.map φ).appTop (algebraMap A Γ(Spec A, ⊤) a) =
      algebraMap A' Γ(Spec A', ⊤) (φ a) := by
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) =
    (Scheme.ΓSpecIso A').inv (φ a)
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ).symm a

variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
  [IsOpenImmersion (Spec.map φ)]

private theorem canonicalAmbientDifferentialMap_geometry_of_d
    (h : Spec.map φ ≫ Spec.map α = Spec.map (α ≫ φ) ≫ 𝟙 (Spec R))
    (κ : (ModuleCat.extendScalars φ.hom).obj (CommRingCat.KaehlerDifferential α) ⟶
      CommRingCat.KaehlerDifferential (α ≫ φ))
    (hκ : ∀ a : A,
      κ ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a) =
        CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a)) :
    (relativeDifferentialOpenSquareIso (Spec.map α) (Spec.map φ)
      (Spec.map (α ≫ φ)) (𝟙 (Spec R)) h).hom =
      ((restrictFunctor (Spec.map φ)).mapIso (relativeDifferentialAffineIso α)).hom ≫
        (restrictFunctorIsoPullback (Spec.map φ)).hom.app
          (tilde (CommRingCat.KaehlerDifferential α)) ≫
        (tildePullbackIso φ).hom.app (CommRingCat.KaehlerDifferential α) ≫
        (tilde.functor A').map κ ≫ (relativeDifferentialAffineIso (α ≫ φ)).inv := by
  let P := CommRingCat.KaehlerDifferential α
  let N := relativeDifferentialSheaf (Spec.map (α ≫ φ))
  let b := (relativeDifferentialOpenSquareIso (Spec.map α) (Spec.map φ)
    (Spec.map (α ≫ φ)) (𝟙 (Spec R)) h).hom
  let E := (restrictFunctor (Spec.map φ)).mapIso (relativeDifferentialAffineIso α)
  apply (cancel_epi E.inv).mp
  change E.inv ≫ b = E.inv ≫ E.hom ≫
    (restrictFunctorIsoPullback (Spec.map φ)).hom.app (tilde P) ≫
      (tildePullbackIso φ).hom.app P ≫ (tilde.functor A').map κ ≫
        (relativeDifferentialAffineIso (α ≫ φ)).inv
  rw [E.inv_hom_id_assoc]
  dsimp only [E, P]
  apply ((restrictAdjunction (Spec.map φ)).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left]
  apply ((tilde.adjunction (R := A)).homEquiv P _).injective
  apply (cancel_mono ((pushforwardGlobalSectionsIso φ).hom.app N)).mp
  dsimp only [P, N, b]
  conv_rhs =>
    erw [ambientRestrictPullback_homEquiv, tildePullbackIso_homEquiv]
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  conv_rhs => erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  conv_lhs => rw [Adjunction.homEquiv_unit]
  conv_rhs => rw [Adjunction.homEquiv_unit]
  change (pushforwardGlobalSectionsIso φ).hom.app N
      (((restrictAdjunction (Spec.map φ)).homEquiv _ _ b).val.app (op ⊤)
        ((relativeDifferentialAffineIso α).inv.val.app (op ⊤)
          (tilde.toOpen P ⊤ (CommRingCat.KaehlerDifferential.d (f := α) a)))) =
    (relativeDifferentialAffineIso (α ≫ φ)).inv.val.app (op ⊤)
      (((tilde.functor A').map κ).val.app (op ⊤)
        (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj P) ⊤
          ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)))
  have hα := relativeDifferentialAffineIso_inv_d α (1 : A) a
  have hQ := relativeDifferentialAffineIso_inv_d (α ≫ φ) (1 : A') (φ a)
  rw! [PrimeSpectrum.basicOpen_one] at hα hQ
  have hb := ambientOpenSquare_adjoint_d (Spec.map α) (Spec.map φ) (Spec.map (α ≫ φ))
    (𝟙 (Spec R)) h ⊤ (algebraMap A Γ(Spec A, ⊤) a)
  rw [hα, hb, ambientPushforwardΓ_apply]
  have hc := congrArg (relativeDifferentialDerivation (Spec.map (α ≫ φ))).d
    (ambientAffineSection_map φ a)
  have ht := ambientTilde_toOpen κ ⊤
    ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)
  have hk := ht.trans
    (congrArg (tilde.toOpen (CommRingCat.KaehlerDifferential (α ≫ φ)) ⊤) (hκ a))
  have hr := (congrArg
    (fun z => (relativeDifferentialAffineIso (α ≫ φ)).inv.val.app (op ⊤) z) hk).trans hQ
  exact hc.trans hr.symm

/-- The actual ambient-open differential arrow is the original scalar-extended Kähler
map under the native restriction, pullback and affine differential comparisons. -/
theorem canonicalAmbientDifferentialMap_geometry
    (h : Spec.map φ ≫ Spec.map α = Spec.map (α ≫ φ) ≫ 𝟙 (Spec R)) :
    (relativeDifferentialOpenSquareIso (Spec.map α) (Spec.map φ)
      (Spec.map (α ≫ φ)) (𝟙 (Spec R)) h).hom =
      ((restrictFunctor (Spec.map φ)).mapIso (relativeDifferentialAffineIso α)).hom ≫
        (restrictFunctorIsoPullback (Spec.map φ)).hom.app
          (tilde (CommRingCat.KaehlerDifferential α)) ≫
        (tildePullbackIso φ).hom.app (CommRingCat.KaehlerDifferential α) ≫
        (tilde.functor A').map (canonicalAmbientDifferentialMap α φ) ≫
        (relativeDifferentialAffineIso (α ≫ φ)).inv :=
  canonicalAmbientDifferentialMap_geometry_of_d α φ h (canonicalAmbientDifferentialMap α φ)
    (canonicalAmbientDifferentialMap_one_tmul α φ)

end AlgebraicGeometry.Scheme.Modules
