/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionScalars
public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine

/-! # The actual section pullback unit under over-site restrictions -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- Restriction retains the original global-section pullback unit. -/
theorem sectionsPresheaf_map_unit {T U : Over X} (f : U ⟶ T) (s : Γ(F, ⊤)) :
    (sectionsPresheaf X F).map f.op
        ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) =
      (((pullbackPushforwardAdjunction U.hom).unit.app F).app ⊤) s := by
  rw [sectionsPresheaf_map_eq]
  have h : Scheme.Modules.Hom.app ((pullbackComp f.left T.hom).inv.app F) ⊤
      ((((pullbackPushforwardAdjunction (f.left ≫ T.hom)).unit.app F).app ⊤) s) =
    (((pullbackPushforwardAdjunction f.left).unit.app
      ((pullback T.hom).obj F)).app ⊤)
      ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) :=
    Modules.Differentials.Diagonal.pullbackComp_inv_unit_top f.left T.hom F s
  rw [← h]
  change Scheme.Modules.Hom.app
      ((pullbackComp f.left T.hom).inv.app F ≫
        (pullbackComp f.left T.hom).hom.app F ≫
        (pullbackCongr (Over.w f)).hom.app F) ⊤
      ((((pullbackPushforwardAdjunction (f.left ≫ T.hom)).unit.app F).app ⊤) s) = _
  rw [Iso.inv_hom_id_app_assoc]
  exact Modules.Differentials.Diagonal.pullbackCongr_unit_top (Over.w f) F s

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
