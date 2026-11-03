/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Evaluation of internal-Hom sections on affine opens

The evaluation map uses the original structure-linear Hom sheaf, original
sections and original restriction maps. No new model for the Hom sheaf is
introduced.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- Evaluate an actual internal-Hom section on sections of its source. -/
def sectionEvaluation (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens) :
    Γ(sheaf X M N, U) →ₗ[Γ(X, U)] (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) where
  toFun s := {
    toFun m := s.val.app (op (Over.mk (𝟙 U))) m
    map_add' m n := (s.val.app (op (Over.mk (𝟙 U)))).hom.map_add m n
    map_smul' r m := s.property (op (Over.mk (𝟙 U))) r m }
  map_add' s t := by ext m; rfl
  map_smul' r s := by
    ext m
    change X.presheaf.map (𝟙 U).op r •
      (show Γ(N, U) from s.val.app (op (Over.mk (𝟙 U))) m) =
        r • (show Γ(N, U) from s.val.app (op (Over.mk (𝟙 U))) m)
    simp

/-- The evaluation map retains the literal component of the original Hom section. -/
theorem sectionEvaluation_apply (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (s : Γ(sheaf X M N, U)) (m : Γ(M, U)) :
    sectionEvaluation X M N U s m = s.val.app (op (Over.mk (𝟙 U))) m := rfl

/-- Evaluation commutes with the original sheaf restriction on both modules. -/
theorem sectionEvaluation_restrict (X : Scheme.{u}) (M N : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(sheaf X M N, U)) (m : Γ(M, U)) :
    sectionEvaluation X M N V ((sheaf X M N).val.map i.op s) (M.val.map i.op m) =
      N.val.map i.op (sectionEvaluation X M N U s m) := by
  exact NatTrans.naturality_apply s.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op m

/-- A counit isomorphism at the source identifies morphisms with their right-adjoint images. -/
def counitHomEquiv {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (M N : D)
    [IsIso (adj.counit.app M)] : (M ⟶ N) ≃ (R.obj M ⟶ R.obj N) :=
  (Iso.homCongr (asIso (adj.counit.app M)).symm (Iso.refl N)).trans
    (adj.homEquiv (R.obj M) N)

/-- The counit Hom equivalence is the actual map of the right adjoint. -/
theorem counitHomEquiv_apply {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (M N : D)
    [IsIso (adj.counit.app M)] (f : M ⟶ N) :
    counitHomEquiv adj M N f = R.map f := by
  change adj.homEquiv _ _ (adj.counit.app M ≫ f ≫ 𝟙 N) = _
  rw [Category.comp_id, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, adj.right_triangle_components, Category.id_comp]

/-- On an affine spectrum, actual global sections recover morphisms out of a
quasicoherent source. The target need not be quasicoherent. -/
def affineGlobalHomEquiv (R : CommRingCat.{u}) (M N : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (M ⟶ N) ≃ (moduleSpecΓFunctor.obj M →ₗ[R] moduleSpecΓFunctor.obj N) := by
  letI : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    show IsIso M.fromTildeΓ from inferInstance
  exact (counitHomEquiv (tilde.adjunction (R := R)) M N).trans ModuleCat.homEquiv

/-- The affine Hom comparison is exactly the original global-sections map. -/
theorem affineGlobalHomEquiv_apply (R : CommRingCat.{u}) (M N : (Spec R).Modules)
    [M.IsQuasicoherent] (f : M ⟶ N) :
    affineGlobalHomEquiv R M N f = (moduleSpecΓFunctor.map f).hom := by
  rw [affineGlobalHomEquiv, Equiv.trans_apply, counitHomEquiv_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules.InternalHom
