/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenPullback

/-!
# Original conormal differential arrows on an affine open square

The middle map is the original open/pullback square followed by pullback
of the original ambient differential restriction. The tangent map is the
original differential restriction on the source. These are the actual
arrows used in the normal-first determinant comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem affineModule_hom_ext {D : CommRingCat.{u}}
    {M N : (Spec D).Modules} [M.IsQuasicoherent] {f g : M ⟶ N}
    (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := fromTildeΓNatTrans.naturality f
  have hg := fromTildeΓNatTrans.naturality g
  exact hf.symm.trans
    ((congrArg (fun k => (tilde.functor D).map k ≫ N.fromTildeΓ) h).trans hg)

/-- On an affine open, values on the original restriction-unit sections determine
an actual sheaf morphism whose source is quasicoherent. -/
theorem canonicalAffineOpenHom_ext {D D' : CommRingCat.{u}} (δ : D ⟶ D')
    [IsOpenImmersion (Spec.map δ)] {M : (Spec D).Modules} [M.IsQuasicoherent]
    {N : (Spec D').Modules} {f g : M.restrict (Spec.map δ) ⟶ N}
    (h : moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map δ)).unit.app M) ≫
        (pushforwardGlobalSectionsIso δ).hom.app (M.restrict (Spec.map δ)) ≫
          (ModuleCat.restrictScalars δ.hom).map (moduleSpecΓFunctor.map f) =
      moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map δ)).unit.app M) ≫
        (pushforwardGlobalSectionsIso δ).hom.app (M.restrict (Spec.map δ)) ≫
          (ModuleCat.restrictScalars δ.hom).map (moduleSpecΓFunctor.map g)) : f = g := by
  let θ := affineRestrictGlobalSectionsIso δ M
  let adj := ModuleCat.extendRestrictScalarsAdj δ.hom
  have hΓ : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g := by
    apply (cancel_epi θ.hom).mp
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hu := affineRestrictGlobalSectionsIso_unit δ M
    change adj.unit.app (moduleSpecΓFunctor.obj M) ≫
      (ModuleCat.restrictScalars δ.hom).map θ.hom = _ at hu
    simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, hu] using h
  let : (M.restrict (Spec.map δ)).IsQuasicoherent := by infer_instance
  exact affineModule_hom_ext hΓ

variable {R A A' B B' : CommRingCat.{u}} (α : R ⟶ A)
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ τ = σ ≫ ψ)

omit [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)] in
include h in
/-- The original affine ring square gives the same native spectral square. -/
theorem canonicalAmbientClosedSquare :
    Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, h]

/-- The original ambient differential restriction across the actual affine open. -/
def canonicalAmbientDifferentialOpenIso :
    (relativeDifferentialSheaf (Spec.map α)).restrict (Spec.map φ) ≅
      relativeDifferentialSheaf (Spec.map (α ≫ φ)) :=
  relativeDifferentialOpenSquareIso (Spec.map α) (Spec.map φ)
    (Spec.map (α ≫ φ)) (𝟙 (Spec R)) (by simp [Spec.map_comp])

omit [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)] in
include h in
/-- The actual composed relative differential square on the source. -/
theorem canonicalAmbientSourceSquare :
    Spec.map ψ ≫ Spec.map (α ≫ σ) =
      Spec.map ((α ≫ φ) ≫ τ) ≫ 𝟙 (Spec R) := by
  rw [Category.comp_id, ← Spec.map_comp]
  apply congrArg Spec.map
  simpa only [Category.assoc] using congrArg (fun k => α ≫ k) h.symm

/-- The original tangent differential restriction across the source affine open. -/
def canonicalAmbientConormalTangentIso :
    (relativeDifferentialSheaf (Spec.map (α ≫ σ))).restrict (Spec.map ψ) ≅
      relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ τ)) :=
  relativeDifferentialOpenSquareIso (Spec.map (α ≫ σ)) (Spec.map ψ)
    (Spec.map ((α ≫ φ) ≫ τ)) (𝟙 (Spec R))
      (canonicalAmbientSourceSquare α φ σ τ ψ h)

/-- The actual middle map is the original mixed square and the actual ambient differential map. -/
def canonicalAmbientConormalMiddleIso :
    ((pullback (Spec.map σ)).obj (relativeDifferentialSheaf (Spec.map α))).restrict
        (Spec.map ψ) ≅
      (pullback (Spec.map τ)).obj (relativeDifferentialSheaf (Spec.map (α ≫ φ))) :=
  (canonicalPullbackOpenSquareIso (Spec.map σ) (Spec.map τ) (Spec.map ψ) (Spec.map φ)
      (canonicalAmbientClosedSquare φ σ τ ψ h)).app
        (relativeDifferentialSheaf (Spec.map α)) ≪≫
    (pullback (Spec.map τ)).mapIso (canonicalAmbientDifferentialOpenIso α φ)

end AlgebraicGeometry.Scheme.Modules
