/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum
public import Aglib.AlgebraicGeometry.Modules.Pullback.SectionStalk.Unit

/-!
# Original germs in local-spectrum pullback sections

The existing local-spectrum comparison retains the original pullback unit
and its exact germ values. These proofs are extracted once from proper
formal functions; only the neighbourhood-inclusion proof uses the native
preimage-of-closed-point theorem directly rather than a higher wrapper.
No quasicoherence, properness or finite-type hypothesis is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite IsLocalRing

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

private theorem scalarExtensionIso_mp_unit
    {R S : Type u} [CommRing R] [CommRing S]
    {C : Type v} [Category.{w} C]
    (F : C ⥤ ModuleCat.{u} S) (G : C ⥤ ModuleCat.{u} R)
    (σ τ : R →+* S) (hστ : σ = τ) (E : F ≅ G ⋙ ModuleCat.extendScalars σ)
    (hTypes : (F ≅ G ⋙ ModuleCat.extendScalars σ) =
      (F ≅ G ⋙ ModuleCat.extendScalars τ))
    (M : C) (m : F.obj M) (n : G.obj M)
    (hE : E.hom.app M m = (ModuleCat.extendRestrictScalarsAdj σ).unit.app (G.obj M) n) :
    (Eq.mp hTypes E).hom.app M m =
      (ModuleCat.extendRestrictScalarsAdj τ).unit.app (G.obj M) n := by
  subst τ
  have hh : hTypes = rfl := Subsingleton.elim _ _
  rw [hh]
  exact hE

/-- At the original local-spectrum closed point, the same unit gives the normalized scalar unit. -/
theorem fromSpecStalkPullbackStalkIso_unit_germ
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules)
    (U : Y.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    (fromSpecStalkPullbackStalkIso Y y).hom.app M
      (((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M).presheaf.germ
        ((Y.fromSpecStalk y) ⁻¹ᵁ U) (closedPoint (Y.presheaf.stalk y))
        (by
          change Y.fromSpecStalk y (closedPoint (Y.presheaf.stalk y)) ∈ U
          simpa only [Scheme.fromSpecStalk_closedPoint] using hy)
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m)) =
      (ModuleCat.extendRestrictScalarsAdj
        (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).unit.app
          ((moduleStalk Y y).obj M) (M.presheaf.germ U y hy m) := by
  let j := Y.fromSpecStalk y
  let x := closedPoint (Y.presheaf.stalk y)
  let hx := Scheme.fromSpecStalk_closedPoint (x := y)
  let F := Scheme.Modules.pullback j ⋙ moduleStalk (Spec (Y.presheaf.stalk y)) x
  let G := moduleStalk Y y
  let σ := ((Y.presheaf.stalkCongr (.of_eq hx)).inv ≫ j.stalkMap x).hom
  let τ := (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom
  have hστ : σ = τ := congrArg CommRingCat.Hom.hom
    (fromSpecStalk_normalized_stalkMap Y y)
  let hTypes := congrArg (fun ρ => F ≅ G ⋙ ModuleCat.extendScalars ρ) hστ
  have hE := pullbackModuleStalkAtEqIso_unit_germ j x y hx M U hy m
  dsimp only [fromSpecStalkPullbackStalkIso]
  exact scalarExtensionIso_mp_unit F G σ τ hστ
    (pullbackModuleStalkAtEqIso j x y hx) hTypes M _ _ hE

/-- The original local-section isomorphism cancels to the original scalar-extension unit. -/
theorem stalkFromSpecStalkSectionsIso_cancel
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules) :
    (stalkFromSpecStalkSectionsIso Y y M).hom ≫
      (localSpectrumSectionsStalkIso (Y.presheaf.stalk y)
        ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M)).hom ≫
      (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).map
        ((fromSpecStalkPullbackStalkIso Y y).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj
        (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).unit.app
          ((moduleStalk Y y).obj M) := by
  rw [stalkFromSpecStalkSectionsIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    Iso.app_inv, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The native stalk/local-sections comparison sends each actual germ to its actual
pulled-back neighborhood section restricted to the whole local spectrum. -/
theorem stalkFromSpecStalkSectionsIso_germ
    (Y : Scheme.{u}) (y : Y) (M : Y.Modules)
    (U : Y.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    (stalkFromSpecStalkSectionsIso Y y M).hom (M.presheaf.germ U y hy m) =
      ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M).presheaf.map
        (homOfLE (by
          exact (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y)
            (by simpa only [Scheme.fromSpecStalk_closedPoint] using hy)).ge)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m) := by
  let P := (Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M
  let c :=
    (localSpectrumSectionsStalkIso (Y.presheaf.stalk y) P).hom ≫
      (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).map
        ((fromSpecStalkPullbackStalkIso Y y).hom.app M)
  apply (ConcreteCategory.bijective_of_isIso c).1
  have hleft := ConcreteCategory.congr_hom (stalkFromSpecStalkSectionsIso_cancel Y y M)
    (M.presheaf.germ U y hy m)
  change c ((stalkFromSpecStalkSectionsIso Y y M).hom (M.presheaf.germ U y hy m)) = _ at hleft
  rw [hleft]
  symm
  change (fromSpecStalkPullbackStalkIso Y y).hom.app M
    (P.presheaf.germ ⊤ (closedPoint (Y.presheaf.stalk y)) trivial
      (P.presheaf.map (homOfLE (by
          exact (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y)
            (by simpa only [Scheme.fromSpecStalk_closedPoint] using hy)).ge)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Y.fromSpecStalk y)).unit.app M).app U m))) = _
  rw [P.presheaf.germ_res_apply]
  exact fromSpecStalkPullbackStalkIso_unit_germ Y y M U hy m

end AlgebraicGeometry.Scheme.Modules
