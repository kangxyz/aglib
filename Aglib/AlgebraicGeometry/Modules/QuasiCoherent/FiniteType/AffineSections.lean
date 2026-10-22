/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections

/-!
# Detecting finite-type quasicoherence on affine sections

The actual restriction section isomorphism is semilinear for the chart's structural ring
isomorphism. Thus finite generation on all affine opens is equivalent to the affine-chart
finite-type predicate, for a known quasicoherent module. No Noetherian hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Finite sections on the image affine open give finite global sections on the
actual spectrum chart, with the canonical scalar maps. -/
theorem finite_chartSections_of_finite_sections
    {X : Scheme.{u}} (M : X.Modules) (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    [Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤)] :
    Module.Finite R (moduleSpecΓFunctor.obj (M.restrict j)) := by
  let σ : Γ(X, j ''ᵁ ⊤) →+* R :=
    ((j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso R).hom).hom
  let f : Γ(M, j ''ᵁ ⊤) →ₛₗ[σ] moduleSpecΓFunctor.obj (M.restrict j) :=
    { toFun := (M.restrictAppIso j ⊤).inv
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by
        intro r m
        have hscalar : (Scheme.ΓSpecIso R).inv (σ r) = (j.appIso ⊤).hom r := by
          change (Scheme.ΓSpecIso R).inv
            ((Scheme.ΓSpecIso R).hom ((j.appIso ⊤).hom r)) = _
          exact (Scheme.ΓSpecIso R).hom_inv_id_apply _
        rw [Scheme.Modules.smul_Spec_def]
        change (M.restrictAppIso j ⊤).inv (r • m) =
          ((Spec R).presheaf.map (𝟙 (Opposite.op ⊤)))
            ((Scheme.ΓSpecIso R).inv (σ r)) • (M.restrictAppIso j ⊤).inv m
        rw [CategoryTheory.Functor.map_id]
        change (M.restrictAppIso j ⊤).inv (r • m) =
          (Scheme.ΓSpecIso R).inv (σ r) • (M.restrictAppIso j ⊤).inv m
        rw [hscalar]
        exact Scheme.Modules.smul_restrictAppIso_inv_apply j M ⊤ r m }
  exact Module.Finite.of_surjective f (ConcreteCategory.bijective_of_isIso
    (M.restrictAppIso j ⊤).inv).surjective

/-- Finite generation on every affine open implies the all-affine-chart finite-type
condition for an independently quasicoherent module. -/
theorem affineLocallyFiniteType_of_finite_affineSections
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U)) :
    affineLocallyFiniteType X M := by
  intro R j _
  have : Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) :=
    hM ⟨j ''ᵁ ⊤, (isAffineOpen_top (Spec R)).image_of_isOpenImmersion j⟩
  exact ⟨inferInstance, finite_chartSections_of_finite_sections M R j⟩

/-- The chart predicate agrees with finite modules of sections on all affine opens. -/
theorem affineLocallyFiniteType_iff_finite_affineSections
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] :
    affineLocallyFiniteType X M ↔
      ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U) :=
  ⟨fun h U => finite_sections_of_affineLocallyFiniteType M h U,
    affineLocallyFiniteType_of_finite_affineSections M⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
