/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheaf
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback

/-! # Composition of native affine sheaf maps

The comparison retains the original scheme pullback and scalar-extension
composition isomorphisms and the actual associated-sheaf counits.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {R S T : CommRingCat.{u}}

/-- Explicitly typed associated-sheaf comparisons retain the original pullback and
scalar-extension composition isomorphisms. -/
theorem affineMapOfTilde_comp (σ : R ⟶ S) (τ : S ⟶ T)
    (hστ : Spec.map (σ ≫ τ) = Spec.map τ ≫ Spec.map σ)
    {P : ModuleCat R} {Q : ModuleCat S} {H : ModuleCat T}
    {E : (Spec R).Modules} {F : (Spec S).Modules} {G : (Spec T).Modules}
    (e : (tilde.functor R).obj P ≅ E) (d : (tilde.functor S).obj Q ≅ F)
    (k : (tilde.functor T).obj H ⟶ G)
    (t : (ModuleCat.extendScalars σ.hom).obj P ⟶ Q)
    (v : (ModuleCat.extendScalars τ.hom).obj Q ⟶ H) :
    (pullbackCongr hστ).hom.app E ≫
        (pullbackComp (Spec.map τ) (Spec.map σ)).inv.app E ≫
        (pullback (Spec.map τ)).map (affineMapOfTilde σ e d.hom t) ≫
        affineMapOfTilde τ d k v =
      affineMapOfTilde (σ ≫ τ) e k
        ((ModuleCat.extendScalarsComp σ.hom τ.hom).hom.app P ≫
          (ModuleCat.extendScalars τ.hom).map t ≫ v) := by
  obtain rfl : hστ = Spec.map_comp σ τ := rfl
  exact affineFunctorMap_comp
    (tilde.functor R) (tilde.functor S) (tilde.functor T)
    (ModuleCat.extendScalars σ.hom) (ModuleCat.extendScalars τ.hom)
    (ModuleCat.extendScalars (σ ≫ τ).hom)
    (pullback (Spec.map σ)) (pullback (Spec.map τ)) (pullback (Spec.map (σ ≫ τ)))
    (pullback (Spec.map τ ≫ Spec.map σ))
    (tildePullbackIso σ).hom (tildePullbackIso τ).hom (tildePullbackIso (σ ≫ τ)).hom
    (pullbackCongr (Spec.map_comp σ τ)).hom
    (pullbackComp (Spec.map τ) (Spec.map σ)).inv
    (ModuleCat.extendScalarsComp σ.hom τ.hom).hom e d k t v
    (tildePullbackIso_comp_hom_app σ τ (Spec.map_comp σ τ) P)

/-- The native affine sheaf construction composes through the actual pullback and
scalar-extension composition comparisons. -/
theorem affineMapFromTensor_comp
    (σ : R ⟶ S) (τ : S ⟶ T)
    (E : (Spec R).Modules) (F : (Spec S).Modules) (G : (Spec T).Modules)
    [E.IsQuasicoherent] [F.IsQuasicoherent]
    (t : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E) ⟶
      moduleSpecΓFunctor.obj F)
    (v : (ModuleCat.extendScalars τ.hom).obj (moduleSpecΓFunctor.obj F) ⟶
      moduleSpecΓFunctor.obj G) :
    (pullbackCongr (Spec.map_comp σ τ)).hom.app E ≫
        (pullbackComp (Spec.map τ) (Spec.map σ)).inv.app E ≫
        (pullback (Spec.map τ)).map (affineMapFromTensor σ E F t) ≫
        affineMapFromTensor τ F G v =
      affineMapFromTensor (σ ≫ τ) E G
        ((ModuleCat.extendScalarsComp σ.hom τ.hom).hom.app (moduleSpecΓFunctor.obj E) ≫
          (ModuleCat.extendScalars τ.hom).map t ≫ v) := by
  simp only [affineMapFromTensor_eq]
  exact affineMapOfTilde_comp σ τ (Spec.map_comp σ τ)
    (P := moduleSpecΓFunctor.obj E) (Q := moduleSpecΓFunctor.obj F)
    (H := moduleSpecΓFunctor.obj G)
    (asIso E.fromTildeΓ) (asIso F.fromTildeΓ) G.fromTildeΓ t v

end AlgebraicGeometry.Scheme.Modules.Nonflat
