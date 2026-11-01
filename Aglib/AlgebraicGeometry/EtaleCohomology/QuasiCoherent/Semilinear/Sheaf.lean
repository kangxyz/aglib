/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Sections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveTransport
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction

/-!
# Semilinear endomorphisms of the original additive coefficient

The affine-test maps act on the literal restriction of `additiveCoefficient`.
Full faithfulness of that restriction constructs the endomorphism of the same
coefficient sheaf. Only affine-test sections use tensor coordinates.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
  (Φ : (affineΓFunctor X).obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hX]
    (affineΓFunctor X).obj F)

local instance (U : X.AffineEtale) : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
  change IsAffine (Spec U.left.unop)
  infer_instance

local instance (U : X.AffineEtale) :
    IsAffine ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)).left := by
  change IsAffine ((Scheme.AffineEtale.Spec X).obj U).left
  infer_instance

local instance (U : X.AffineEtale) :
    IsAffine ((𝟭 Scheme).obj ((Scheme.AffineEtale.Spec X).obj U).left) := by
  change IsAffine ((Scheme.AffineEtale.Spec X).obj U).left
  infer_instance

local instance (i : Discrete PUnit) : IsAffine ((Functor.fromPUnit X).obj i) := by
  change IsAffine X
  infer_instance

private theorem liftSectionAddHom_square {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (a : A →+ A) (b : B →+ B) (h : f.comp a = b.comp f) :
    liftSectionAddHom f ≫ liftSectionAddHom b =
      liftSectionAddHom a ≫ liftSectionAddHom f := by
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  exact DFunLike.congr_fun h.symm s.down

omit [IsAffine X] in
private theorem affineAdditiveRestriction_map {U V : X.AffineEtaleᵒᵖ} (f : U ⟶ V) :
    ((EtaleAffineBasis.abelianRestriction X).obj (additiveCoefficient X F)).obj.map f =
      liftSectionAddHom (sectionsAddHom X F
        ((Scheme.Etale.forget X).map ((Scheme.AffineEtale.Spec X).map f.unop))) := rfl

/-- The original affine-section maps on the literal affine restriction. -/
def affineRestrictedFrobenius :
    (EtaleAffineBasis.abelianRestriction X).obj (additiveCoefficient X F) ⟶
      (EtaleAffineBasis.abelianRestriction X).obj (additiveCoefficient X F) where
  hom := {
    app U := liftSectionAddHom (affineSectionFrobenius X F p hp hX Φ
      ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U.unop)))
    naturality := by
      intro U V f
      rw [affineAdditiveRestriction_map]
      exact liftSectionAddHom_square _ _ _
        (affineSectionFrobenius_naturality_hom X F p hp hX Φ
          ((Scheme.Etale.forget X).map ((Scheme.AffineEtale.Spec X).map f.unop))) }


/-- The additive sheaf endomorphism on the unchanged quasi-coherent coefficient. -/
def affineGammaFrobenius : additiveCoefficient X F ⟶ additiveCoefficient X F :=
  (EtaleAffineBasis.abelianRestriction X).preimage
    (affineRestrictedFrobenius X F p hp hX Φ)

/-- The defining whole-map equation is actual affine restriction, not a replacement model. -/
theorem affineGammaFrobenius_restrict :
    (EtaleAffineBasis.abelianRestriction X).map (affineGammaFrobenius X F p hp hX Φ) =
      affineRestrictedFrobenius X F p hp hX Φ :=
  Functor.map_preimage _ _

/-- On each affine test the original map is exactly the original section operator. -/
theorem affineGammaFrobenius_apply (U : X.AffineEtale)
    (s : Γ((pullback ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom).obj F, ⊤)) :
    (affineGammaFrobenius X F p hp hX Φ).hom.app
        (op ((Scheme.AffineEtale.Spec X).obj U)) (ULift.up s) =
      ULift.up (affineSectionFrobenius X F p hp hX Φ
        ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)) s) := by
  change ((EtaleAffineBasis.abelianRestriction X).map
    (affineGammaFrobenius X F p hp hX Φ)).hom.app (op U) (ULift.up s) = _
  rw [affineGammaFrobenius_restrict]
  rfl

/-- Original affine section tensors retain the scalar prime-power formula. -/
theorem affineGammaFrobenius_tmul (U : X.AffineEtale)
    (r : Γ(((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)).left, ⊤))
    (s : (affineΓFunctor X).obj F) :
    @Eq Γ((pullback ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)).hom).obj F, ⊤)
      (((affineGammaFrobenius X F p hp hX Φ).hom.app
        (op ((Scheme.AffineEtale.Spec X).obj U))
        (ULift.up ((affinePullbackSectionsIso ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom F).hom
          (r ⊗ₜ[Γ(X, ⊤),((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom.appTop.hom] s)))).down)
      ((affinePullbackSectionsIso ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom F).hom
        ((r ^ p) ⊗ₜ[Γ(X, ⊤),((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom.appTop.hom] Φ s)) := by
  have h := congrArg (β := Γ((pullback ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom).obj F, ⊤))
    ULift.down (affineGammaFrobenius_apply X F p hp hX Φ U
      ((affinePullbackSectionsIso ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom.appTop.hom] s)))
  have ht := affineSectionFrobenius_tmul X F p hp hX Φ
    ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)) r s
  have he := h.trans ht
  exact he

/-- A sheaf endomorphism is determined by its actual affine-section components. -/
theorem affineGammaFrobenius_unique (Ψ : additiveCoefficient X F ⟶ additiveCoefficient X F)
    (hΨ : ∀ (U : X.AffineEtale)
      (s : Γ((pullback ((Scheme.Etale.forget X).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom).obj F, ⊤)),
      (Ψ.hom.app (op ((Scheme.AffineEtale.Spec X).obj U)) (ULift.up s)).down =
        affineSectionFrobenius X F p hp hX Φ
          ((Scheme.Etale.forget X).obj ((Scheme.AffineEtale.Spec X).obj U)) s) :
    Ψ = affineGammaFrobenius X F p hp hX Φ := by
  apply (EtaleAffineBasis.abelianRestriction X).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  exact (hΨ U.unop s.down).trans
    (congrArg ULift.down (affineGammaFrobenius_apply X F p hp hX Φ U.unop s.down)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
