/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiPullbackUnit
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-! # Geometric pullback on original open sections

The full open-section square is proved for every section on the open, using
the already constructed native restriction square and original module unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules)

/-- The original open-section comparison commutes with geometric pullback,
retaining the original native unit on sections of the displayed open. -/
theorem openPullbackSectionsIso_geometric
    (s : Γ((pullback U.ι).obj M, ⊤)) :
    (openPullbackSectionsIso X ((pullback f).obj M) (f ⁻¹ᵁ U)).hom
      (Scheme.Modules.Hom.app
        ((pullbackComp (f ∣_ U) U.ι).hom.app M ≫
          (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
          (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M) ⊤
        (nativeSectionPullback (f ∣_ U) ((pullback U.ι).obj M) s)) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U
        ((openPullbackSectionsIso Y M U).hom s) := by
  let P := (pullback f).obj M
  let η := (pullbackPushforwardAdjunction f).unit.app M
  rw [openPullbackSectionsIso_hom_apply, openPullbackSectionsIso_hom_apply]
  change P.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op
      (Scheme.Modules.Hom.app
        ((pullbackComp (f ∣_ U) U.ι).hom.app M ≫
          (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
          (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M ≫
          (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app P) ⊤
        (nativeSectionPullback (f ∣_ U) ((pullback U.ι).obj M) s)) = _
  rw [openPullbackSection_unit, Pullback.OpenRestriction.restrictedPushforwardMap_app]
  change P.presheaf.map _
      (P.presheaf.map _
        (η.app (U.ι ''ᵁ ⊤)
          (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s))) =
    η.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s))
  have h := ConcreteCategory.congr_hom
    (η.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s)
  change η.app U (M.presheaf.map _ _) = P.presheaf.map _ _ at h
  rw [h]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
