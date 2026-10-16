/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Locality

/-!
# Actual module descent through a closed immersion

The original pullback/pushforward unit is invertible precisely when the
native kernel ideal annihilates the original module sheaf. This describes
the essential image of the ordinary closed pushforward on all modules.
The descent coefficient is the actual ordinary pullback, and its comparison
is the inverse of the original unit. No quasicoherence or finiteness is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- On a point of the closed source, invertibility of the original
geometric unit is the original stalk-kernel annihilation condition. -/
theorem pullbackPushforwardUnit_moduleStalk_isIso_iff (x : X) (M : Y.Modules) :
    IsIso ((moduleStalk Y (f x)).map ((pullbackPushforwardAdjunction f).unit.app M)) ↔
      RingHom.ker (f.stalkMap x).hom ≤
        Module.annihilator (Y.presheaf.stalk (f x)) ((moduleStalk Y (f x)).obj M) := by
  rw [← ModuleCat.extendRestrictScalarsAdj_unit_isIso_iff_ker_le_annihilator
    (f.stalkMap x).hom (f.stalkMap_surjective x) ((moduleStalk Y (f x)).obj M)]
  rw [← pullbackPushforwardUnit_moduleStalk f f.isClosedEmbedding.isInducing x M]
  simp only [isIso_comp_right_iff]

/-- The original geometric unit of a closed immersion is invertible exactly
on the modules annihilated by its native kernel ideal. -/
theorem pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf (M : Y.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) ↔
      killedByIdealSheaf f.ker M := by
  constructor
  · intro h
    let := h
    exact killedByIdealSheaf_of_iso f.ker
      (asIso ((pullbackPushforwardAdjunction f).unit.app M)).symm
      (killedByIdealSheaf_pushforward_ker f ((pullback f).obj M))
  · intro hM
    apply isIso_of_moduleStalk
    intro y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      exact (pullbackPushforwardUnit_moduleStalk_isIso_iff f x M).mpr
        (killedByIdealSheaf_ker_le_annihilator_stalk f f.isClosedEmbedding.isInducing M hM x)
    · have hs : y ∉ f.ker.support := by
        intro hy'
        have hy'' : y ∈ _root_.closure (Set.range f) := by
          rw [← f.support_ker]
          exact hy'
        exact hy (f.isClosedEmbedding.isClosed_range.closure_eq ▸ hy'')
      have hsource := killedByIdealSheaf_isZero_stalk_of_not_mem_support f.ker M hM y hs
      have htarget := isZero_closedImmersion_moduleStalk_of_not_mem f y hy
        ((pullback f).obj M)
      let : Mono ((moduleStalk Y y).map ((pullbackPushforwardAdjunction f).unit.app M)) :=
        hsource.mono _
      let : Epi ((moduleStalk Y y).map ((pullbackPushforwardAdjunction f).unit.app M)) :=
        htarget.epi _
      exact isIso_of_mono_of_epi _

/-- The essential image of the actual ordinary closed pushforward is the
actual kernel-annihilated module property, without quasicoherence. -/
theorem mem_essImage_pushforward_iff_killedByIdealSheaf (M : Y.Modules) :
    (pushforward f).essImage M ↔ killedByIdealSheaf f.ker M := by
  let := (fullyFaithfulPushforwardOfClosedImmersion f).full
  let := (fullyFaithfulPushforwardOfClosedImmersion f).faithful
  exact (pullbackPushforwardAdjunction f).isIso_unit_app_iff_mem_essImage.symm.trans
    (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf f M)

/-- Descent uses the actual ordinary pullback and the inverse of the
original adjunction unit. -/
def closedImmersionDescentIso (M : Y.Modules) (hM : killedByIdealSheaf f.ker M) :
    (pushforward f).obj ((pullback f).obj M) ≅ M := by
  let := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf f M).mpr hM
  exact (asIso ((pullbackPushforwardAdjunction f).unit.app M)).symm

/-- The inverse comparison is literally the original geometric unit. -/
@[simp]
theorem closedImmersionDescentIso_inv (M : Y.Modules) (hM : killedByIdealSheaf f.ker M) :
    (closedImmersionDescentIso f M hM).inv =
      (pullbackPushforwardAdjunction f).unit.app M := rfl

/-- Original coefficient maps commute with the actual descent comparison. -/
@[reassoc]
theorem closedImmersionDescentIso_hom_naturality {M N : Y.Modules}
    (hM : killedByIdealSheaf f.ker M) (hN : killedByIdealSheaf f.ker N) (g : M ⟶ N) :
    (pushforward f).map ((pullback f).map g) ≫ (closedImmersionDescentIso f N hN).hom =
      (closedImmersionDescentIso f M hM).hom ≫ g := by
  apply (cancel_epi (closedImmersionDescentIso f M hM).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have hn : (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map ((pullback f).map g) =
      g ≫ (pullbackPushforwardAdjunction f).unit.app N :=
    ((pullbackPushforwardAdjunction f).unit.naturality g).symm
  rw [closedImmersionDescentIso_inv, ← Category.assoc, hn, Category.assoc]
  change g ≫ (closedImmersionDescentIso f N hN).inv ≫
    (closedImmersionDescentIso f N hN).hom = g
  simp only [Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
