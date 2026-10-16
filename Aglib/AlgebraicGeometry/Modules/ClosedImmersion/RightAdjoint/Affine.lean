/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Affine sections of the original closed right adjoint

For a closed spectrum map, the sections of the single selected ordinary
right adjoint are naturally coinduced modules. The original tilde/pushforward
comparison identifies the left adjoints; native uniqueness of right adjoints
then supplies the module-valued isomorphism with its original unit and
counit equations. It is linear over the source ring on all module sheaves,
without requiring quasicoherence of the target or an injective term.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]

/-- The original tilde-pushforward adjunction transported through the original
affine comparison, with unchanged right-adjoint and sections functors. -/
def closedImmersionRightAdjointAffineAdjunction :
    ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R ⊣
      closedImmersionRightAdjoint (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) :=
  ((tilde.adjunction (R := S)).comp (closedImmersionRightAdjunction (Spec.map φ))).ofNatIsoLeft
    (tildePushforwardIso φ)

/-- Sections of the actual closed right adjoint are the original coinduced
module, naturally and linearly over S, for arbitrary coefficient sheaves. -/
def closedImmersionRightAdjointAffineIso :
    closedImmersionRightAdjoint (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) ≅
      moduleSpecΓFunctor (R := R) ⋙ ModuleCat.coextendScalars φ.hom :=
  (closedImmersionRightAdjointAffineAdjunction φ).rightAdjointUniq
    ((ModuleCat.restrictCoextendScalarsAdj φ.hom).comp (tilde.adjunction (R := R)))

/-- The affine comparison retains the original composite adjunction units. -/
@[reassoc]
theorem closedImmersionRightAdjointAffineIso_unit (M : ModuleCat S) :
    (closedImmersionRightAdjointAffineAdjunction φ).unit.app M ≫
      (closedImmersionRightAdjointAffineIso φ).hom.app
        ((tilde.functor R).obj ((ModuleCat.restrictScalars φ.hom).obj M)) =
      ((ModuleCat.restrictCoextendScalarsAdj φ.hom).comp
        (tilde.adjunction (R := R))).unit.app M :=
  Adjunction.unit_rightAdjointUniq_hom_app _ _ M

/-- The affine comparison retains the original composite adjunction counits. -/
@[reassoc]
theorem closedImmersionRightAdjointAffineIso_counit (N : (Spec R).Modules) :
    (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R).map
        ((closedImmersionRightAdjointAffineIso φ).hom.app N) ≫
      ((ModuleCat.restrictCoextendScalarsAdj φ.hom).comp
        (tilde.adjunction (R := R))).counit.app N =
      (closedImmersionRightAdjointAffineAdjunction φ).counit.app N :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ N

/-- The comparison identifies the original geometric chain-level Hom adjoint
with scalar coinduction through the original tilde-pushforward comparison. -/
theorem closedImmersionRightAdjointAffineIso_homEquiv (M : ModuleCat S)
    (N : (Spec R).Modules)
    (p : (pushforward (Spec.map φ)).obj ((tilde.functor S).obj M) ⟶ N) :
    ((tilde.adjunction (R := S)).comp
      (closedImmersionRightAdjunction (Spec.map φ))).homEquiv M N p ≫
        (closedImmersionRightAdjointAffineIso φ).hom.app N =
      ((ModuleCat.restrictCoextendScalarsAdj φ.hom).comp
        (tilde.adjunction (R := R))).homEquiv M N
          ((tildePushforwardIso φ).inv.app M ≫ p) := by
  let q := (tildePushforwardIso φ).inv.app M ≫ p
  have h : (closedImmersionRightAdjointAffineAdjunction φ).homEquiv M N q ≫
      (closedImmersionRightAdjointAffineIso φ).hom.app N =
        ((ModuleCat.restrictCoextendScalarsAdj φ.hom).comp
          (tilde.adjunction (R := R))).homEquiv M N q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
      (closedImmersionRightAdjointAffineIso φ).hom.naturality q,
      ← Category.assoc]
    exact congrArg (fun r => r ≫
      (moduleSpecΓFunctor (R := R) ⋙ ModuleCat.coextendScalars φ.hom).map q)
        (closedImmersionRightAdjointAffineIso_unit φ M)
  simpa only [closedImmersionRightAdjointAffineAdjunction,
    Adjunction.homEquiv_ofNatIsoLeft_apply, q, Iso.hom_inv_id_app_assoc] using h

/-- The original affine right-adjoint comparison as a linear Hom formula.
The S-action is the native coinduced action on Hom from S. -/
def closedImmersionRightAdjointSectionsLinearEquiv (N : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := S)).obj ((closedImmersionRightAdjoint (Spec.map φ)).obj N) ≃ₗ[S]
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj N) :=
  ((closedImmersionRightAdjointAffineIso φ).app N).toLinearEquiv.trans
    (ModuleCat.CoextendScalars.equiv φ.hom ((moduleSpecΓFunctor (R := R)).obj N))

/-- The original S-action is the actual coinduced Hom action on the first
argument, rather than a scalar action on a chosen quotient representative. -/
theorem closedImmersionRightAdjointSectionsLinearEquiv_smul_apply
    (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) (b b' : S) :
    closedImmersionRightAdjointSectionsLinearEquiv φ N (b • m) b' =
      closedImmersionRightAdjointSectionsLinearEquiv φ N m (b' * b) := by
  change ModuleCat.CoextendScalars.equiv φ.hom _
      (((closedImmersionRightAdjointAffineIso φ).app N).hom (b • m)) b' = _
  have hscalar : ((closedImmersionRightAdjointAffineIso φ).app N).hom (b • m) =
      b • ((closedImmersionRightAdjointAffineIso φ).app N).hom m :=
    (((closedImmersionRightAdjointAffineIso φ).app N).hom.hom).map_smul b m
  rw [hscalar]
  exact ModuleCat.CoextendScalars.smul_apply _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules
