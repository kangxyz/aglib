/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientNaturality

/-! # Original section comparisons for affine quotient gluing -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {R : CommRingCat.{u}} (Q : (Spec R).Modules) [Q.IsQuasicoherent]
  (N : ModuleCat.{u} R) (e : moduleSpecΓFunctor.obj Q ≅ N)

/-- The affine sheaf comparison induced by a specified original section iso. -/
def affineSheafIsoOfSectionIso : Q ≅ tilde N :=
  (asIso Q.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e

@[reassoc]
theorem affineSheafIsoOfSectionIso_sections :
    moduleSpecΓFunctor.map (affineSheafIsoOfSectionIso Q N e).hom ≫
      (tilde.toTildeΓNatIso.app N).inv = e.hom :=
  affineQuotientFromSections_sections Q N e.hom

/-- A square of original section maps implies the actual local quotient square.
This is the bridge used to descend relation kernels on affine overlaps. -/
@[reassoc]
theorem affineSheafIsoOfSectionIso_quotient
    {M : (Spec R).Modules} [M.IsQuasicoherent]
    (q : M ⟶ Q) (qN : moduleSpecΓFunctor.obj M ⟶ N)
    (h : moduleSpecΓFunctor.map q ≫ e.hom = qN) :
    q ≫ (affineSheafIsoOfSectionIso Q N e).hom =
      affineQuotientFromSections M N qN := by
  change q ≫ affineQuotientFromSections Q N e.hom = _
  have hh := affineQuotientFromSections_naturality qN e.hom q (𝟙 N)
    (by simpa only [Category.comp_id] using h)
  simpa only [tilde.map_id, Category.comp_id] using hh

end AlgebraicGeometry.Scheme.Modules.Coherent
