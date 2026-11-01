/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Locality
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModuleNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionAdditive

/-! # Native open-chart normalization of geometric coefficient pullback

The explicit pullback-composition maps are identified with the already proved
native restriction square. The original module adjunction unit, rather than a
chosen section map or a cohomology comparison, controls geometric pullback.
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

/-- The explicit section-coefficient comparison is the original adjunction-defined
local module comparison. No flatness or quasicoherence is required. -/
theorem openPullbackRestrictionSquare :
    (pullbackComp (f ∣_ U) U.ι).hom.app M ≫
        (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
        (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M ≫
        (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app ((pullback f).obj M) =
      (pullback (f ∣_ U)).map ((restrictFunctorIsoPullback U.ι).inv.app M) ≫
        (Pullback.OpenRestriction.localPullbackIso f U).inv.app M := by
  have h := congrArg (fun e => e.hom.app M)
    (BaseChange.Affine.Square.nativeRestrictionSquareIso_eq f U)
  change (pullback (f ∣_ U)).map ((restrictFunctorIsoPullback U.ι).hom.app M) ≫
      (pullbackComp (f ∣_ U) U.ι).hom.app M ≫
      (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
      (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M ≫
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app ((pullback f).obj M) =
    (Pullback.OpenRestriction.localPullbackIso f U).inv.app M at h
  rw [← h]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [(pullback (f ∣_ U)).map_id, Category.id_comp]

/-- On the inverse-image open, literal geometric restriction of a pullback
section agrees with the original native local square. -/
theorem openPullbackSection_restrict
    (s : Γ((pullback U.ι).obj M, ⊤)) :
    Scheme.Modules.Hom.app
        ((pullbackComp (f ∣_ U) U.ι).hom.app M ≫
          (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
          (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M ≫
          (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app ((pullback f).obj M)) ⊤
        (nativeSectionPullback (f ∣_ U) ((pullback U.ι).obj M) s) =
      Scheme.Modules.Hom.app ((Pullback.OpenRestriction.localPullbackIso f U).inv.app M) ⊤
        (nativeSectionPullback (f ∣_ U) (M.restrict U.ι)
          (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s)) := by
  rw [openPullbackRestrictionSquare]
  change Scheme.Modules.Hom.app ((Pullback.OpenRestriction.localPullbackIso f U).inv.app M) ⊤
    (Scheme.Modules.Hom.app ((pullback (f ∣_ U)).map
      ((restrictFunctorIsoPullback U.ι).inv.app M)) ⊤
      (nativeSectionPullback (f ∣_ U) ((pullback U.ι).obj M) s)) = _
  rw [nativeSectionPullback_naturality]

/-- The same local comparison carries every section, not just a restriction of
a global section, to the original module pullback unit on the open chart. -/
theorem openPullbackSection_unit
    (s : Γ((pullback U.ι).obj M, ⊤)) :
    Scheme.Modules.Hom.app
        ((pullbackComp (f ∣_ U) U.ι).hom.app M ≫
          (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
          (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M ≫
          (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app ((pullback f).obj M)) ⊤
        (nativeSectionPullback (f ∣_ U) ((pullback U.ι).obj M) s) =
      Scheme.Modules.Hom.app
        (Pullback.OpenRestriction.restrictedPushforwardMap f U ((pullback f).obj M)) ⊤
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctor U.ι).map
            ((pullbackPushforwardAdjunction f).unit.app M)) ⊤
          (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s)) := by
  rw [openPullbackSection_restrict, nativeSectionPullback_eq_unit]
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app M) ⊤ s))
      (Pullback.OpenRestriction.restrictedUnit f U M)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
