/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestriction

/-! # Scalar extension along original affine-chart restrictions

The scalar restriction map uses the original affine restriction comparison and
the original chart-rebracketing isomorphism. Its unit tensors are the sections
of the shared native chart restriction, before any chart rings or coefficients
are specialized.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {Z : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (c : Spec R ⟶ Z) (d : Spec S ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d] [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d) (Q : Z.Modules) [Q.IsQuasicoherent]

/-- Scalar extension of sections along the original commuting affine charts. -/
def affineChartScalarRestriction :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj (Q.restrict c)) ⟶
      moduleSpecΓFunctor.obj (Q.restrict d) :=
  (affineRestrictGlobalSectionsIso φ (Q.restrict c)).hom ≫
    moduleSpecΓFunctor.map (affineChartRestrictionIso φ c d hc Q).hom

/-- The scalar restriction carries each unit tensor to the original section
restriction, including its native restriction unit and chart rebracketing. -/
theorem affineChartScalarRestriction_one_tmul
    (x : moduleSpecΓFunctor.obj (Q.restrict c)) :
    affineChartScalarRestriction φ c d hc Q ((1 : S) ⊗ₜ[R,φ.hom] x) =
      affineChartSectionRestriction φ c d hc Q x := by
  have hu := congrArg (fun k => k x)
    (affineRestrictGlobalSectionsIso_unit φ (Q.restrict c))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at hu
  exact congrArg (moduleSpecΓFunctor.map (affineChartRestrictionIso φ c d hc Q).hom) hu

end AlgebraicGeometry.Scheme.Modules
