/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Frames

/-!
# Nonvanishing opens of arbitrary line-bundle sections

The open is the union of the basic opens of the actual coefficients in all
local frames. Change-of-frame coefficients are units, so every displayed
frame computes the same geometric open. No globally generating family is
required. Sections may be given on any original open of the scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

namespace Nonvanishing

variable {X : Scheme.{u}}

private theorem module_restrict_comp (M : X.Modules) {U V W : X.Opens}
    (h : U ≤ V) (k : V ≤ W) (s : Γ(M, W)) :
    M.val.map (homOfLE h).op (M.val.map (homOfLE k).op s) =
      M.val.map (homOfLE (h.trans k)).op s := by
  change (M.presheaf.map (homOfLE k).op ≫ M.presheaf.map (homOfLE h).op) s =
    M.presheaf.map ((homOfLE k).op ≫ (homOfLE h).op) s
  rw [Functor.map_comp]

/-- Restricting an actual coefficient restricts its basic open. -/
theorem basicOpen_coefficient_restrict (M : X.Modules) (W : X.Opens)
    (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U V : X.Opens} (h : U ≤ V) (hi : V ≤ W) (s : Γ(M, V)) :
    X.basicOpen (chartSectionEquiv X M W e U (h.trans hi)
      (M.val.map (homOfLE h).op s)) =
      U ⊓ X.basicOpen (chartSectionEquiv X M W e V hi s) := by
  let A : PUnit.{u + 1} → X.Opens := fun _ => W
  let d : ∀ i, M.over (A i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (A i)) :=
    fun _ => e
  have hc := LocalFrames.coefficient_restrict A M d PUnit.unit h hi s
  change chartSectionEquiv X M W e U (h.trans hi)
    (M.val.map (homOfLE h).op s) =
      sectionRestrict X h (chartSectionEquiv X M W e V hi s) at hc
  rw [hc]
  exact X.basicOpen_res _ _

/-- Actual coefficients in two frames have the same basic open on every
common subopen, because the transition coefficient is a unit. -/
theorem basicOpen_coefficient_eq (M : X.Modules) (V W : X.Opens)
    (e : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U : X.Opens} (hi : U ≤ V) (hj : U ≤ W) (s : Γ(M, U)) :
    X.basicOpen (chartSectionEquiv X M V e U hi s) =
      X.basicOpen (chartSectionEquiv X M W d U hj s) := by
  let A : ULift.{u} Bool → X.Opens := fun i => if i.down then W else V
  let q : ∀ i, M.over (A i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (A i)) :=
    fun i => by
      rcases i with ⟨i⟩
      cases i
      · exact e
      · exact d
  change X.basicOpen (LocalFrames.coefficient A M q ⟨false⟩ hi s) =
    X.basicOpen (LocalFrames.coefficient A M q ⟨true⟩ hj s)
  have hu : IsUnit (LocalFrames.coefficient A M q ⟨false⟩ hi
      (LocalFrames.generator A M q ⟨true⟩ hj)) :=
    (LocalFrames.transitionUnitOn A M q ⟨false⟩ ⟨true⟩ hi hj).isUnit
  rw [LocalFrames.coefficient_transition A M q ⟨false⟩ ⟨true⟩ hi hj s,
    X.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.mpr (X.basicOpen_le _)

/-- A module isomorphism retains the literal local coefficient when the
frame is transported by that isomorphism. -/
theorem coefficient_iso {M N : X.Modules} (e : M ≅ N) (W : X.Opens)
    (d : N.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U : X.Opens} (h : U ≤ W) (s : Γ(M, U)) :
    chartSectionEquiv X N W d U h (e.hom.val.app (op U) s) =
      chartSectionEquiv X M W
        ((SheafOfModules.overFunctor X.ringCatSheaf W).mapIso e ≪≫ d) U h s := rfl

end Nonvanishing

variable {X : Scheme.{u}}

/-- The geometric nonvanishing open of an actual section on an original
open, obtained from all actual local frames of the line bundle. -/
def nonvanishingOpenOn (L : LineBundle X) (U : X.Opens) (s : Γ(L.val, U)) : X.Opens :=
  ⨆ (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)),
    X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right
      (L.val.val.map (homOfLE inf_le_left).op s))

/-- The geometric nonvanishing open of an arbitrary global section of the
actual line bundle. No generating-family hypothesis is imposed. -/
def nonvanishingOpen (L : LineBundle X) (s : Γ(L.val, ⊤)) : X.Opens :=
  nonvanishingOpenOn L ⊤ s

theorem nonvanishingOpenOn_le (L : LineBundle X) (U : X.Opens) (s : Γ(L.val, U)) :
    nonvanishingOpenOn L U s ≤ U := by
  apply iSup_le
  intro W
  apply iSup_le
  intro e
  exact (X.basicOpen_le _).trans inf_le_left

@[simp] theorem nonvanishingOpenOn_zero (L : LineBundle X) (U : X.Opens) :
    nonvanishingOpenOn L U 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro W
  apply iSup_le
  intro e
  let M : X.Modules := L.val
  have hz : M.presheaf.map (homOfLE (show U ⊓ W ≤ U from inf_le_left)).op
      (0 : Γ(L.val, U)) = 0 :=
    (M.presheaf.map (homOfLE (show U ⊓ W ≤ U from inf_le_left)).op).hom.map_zero
  change X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right
    (M.presheaf.map (homOfLE inf_le_left).op (0 : Γ(L.val, U)))) ≤ ⊥
  apply le_of_eq
  rw [hz, (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right).map_zero,
    X.basicOpen_zero]

@[simp] theorem nonvanishingOpen_zero (L : LineBundle X) :
    nonvanishingOpen L 0 = ⊥ :=
  nonvanishingOpenOn_zero L ⊤

/-- Every actual local frame computes the original geometric open by its
literal coefficient on the intersection with the section's domain. -/
theorem inter_nonvanishingOpenOn (L : LineBundle X) (U : X.Opens) (s : Γ(L.val, U))
    (V : X.Opens)
    (e : L.val.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    V ⊓ nonvanishingOpenOn L U s =
      X.basicOpen (chartSectionEquiv X L.val V e (U ⊓ V) inf_le_right
        (L.val.val.map (homOfLE inf_le_left).op s)) := by
  ext x
  constructor
  · rintro ⟨hxV, hx⟩
    obtain ⟨W, hx⟩ := Opens.mem_iSup.mp hx
    obtain ⟨d, hx⟩ := Opens.mem_iSup.mp hx
    let Z := V ⊓ (U ⊓ W)
    have hxZ : x ∈ Z := ⟨hxV, X.basicOpen_le _ hx⟩
    have hZU : Z ≤ U := inf_le_right.trans inf_le_left
    have hZV : Z ≤ V := inf_le_left
    have hZW : Z ≤ W := inf_le_right.trans inf_le_right
    have hW := Nonvanishing.basicOpen_coefficient_restrict L.val W d
      (show Z ≤ U ⊓ W from inf_le_right) inf_le_right
      (L.val.val.map (homOfLE inf_le_left).op s)
    rw [Nonvanishing.module_restrict_comp] at hW
    have hxW : x ∈ X.basicOpen (chartSectionEquiv X L.val W d Z hZW
        (L.val.val.map (homOfLE hZU).op s)) := by
      rw [hW]
      exact ⟨hxZ, hx⟩
    have hxV' : x ∈ X.basicOpen (chartSectionEquiv X L.val V e Z hZV
        (L.val.val.map (homOfLE hZU).op s)) := by
      rw [Nonvanishing.basicOpen_coefficient_eq L.val V W e d hZV hZW]
      exact hxW
    have hV := Nonvanishing.basicOpen_coefficient_restrict L.val V e
      (show Z ≤ U ⊓ V from le_inf hZU hZV) inf_le_right
      (L.val.val.map (homOfLE inf_le_left).op s)
    rw [Nonvanishing.module_restrict_comp] at hV
    rw [hV] at hxV'
    exact hxV'.2
  · intro hx
    refine ⟨(X.basicOpen_le _ hx).2, ?_⟩
    exact Opens.mem_iSup.mpr ⟨V, Opens.mem_iSup.mpr ⟨e, hx⟩⟩

/-- The exact local coefficient formula for an arbitrary global section. -/
theorem inter_nonvanishingOpen (L : LineBundle X) (s : Γ(L.val, ⊤)) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    U ⊓ nonvanishingOpen L s =
      X.basicOpen (chartSectionEquiv X L.val U e U le_rfl
        (L.val.val.map (homOfLE le_top).op s)) := by
  change U ⊓ nonvanishingOpenOn L ⊤ s = _
  rw [inter_nonvanishingOpenOn L ⊤ s U e]
  have hc := Nonvanishing.basicOpen_coefficient_restrict L.val U e
    (show (⊤ : X.Opens) ⊓ U ≤ U from inf_le_right) le_rfl
    (L.val.val.map (homOfLE le_top).op s)
  rw [Nonvanishing.module_restrict_comp] at hc
  rw [hc, top_inf_eq, inf_eq_right.mpr (X.basicOpen_le _)]

/-- On any displayed local frame, nonvanishing means that its actual
coefficient has a unit germ at the original point. -/
theorem mem_nonvanishingOpen (L : LineBundle X) (s : Γ(L.val, ⊤)) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) :
    x ∈ nonvanishingOpen L s ↔ IsUnit (X.presheaf.germ U x hx
      (chartSectionEquiv X L.val U e U le_rfl
        (L.val.val.map (homOfLE le_top).op s))) := by
  rw [← X.mem_basicOpen _ x hx, ← inter_nonvanishingOpen L s U e]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- Restricting the original section on the original scheme intersects its
nonvanishing open with the new section domain. -/
theorem nonvanishingOpenOn_restrict (L : LineBundle X) {U V : X.Opens}
    (h : V ≤ U) (s : Γ(L.val, U)) :
    nonvanishingOpenOn L V (L.val.val.map (homOfLE h).op s) =
      V ⊓ nonvanishingOpenOn L U s := by
  simp only [nonvanishingOpenOn, inf_iSup_eq]
  apply iSup_congr
  intro W
  apply iSup_congr
  intro e
  rw [Nonvanishing.module_restrict_comp]
  have hc := Nonvanishing.basicOpen_coefficient_restrict L.val W e
    (inf_le_inf h le_rfl) inf_le_right
    (L.val.val.map (homOfLE inf_le_left).op s)
  rw [Nonvanishing.module_restrict_comp] at hc
  calc
    _ = (V ⊓ W) ⊓ X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W)
        inf_le_right (L.val.val.map (homOfLE inf_le_left).op s)) := hc
    _ = V ⊓ X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W)
        inf_le_right (L.val.val.map (homOfLE inf_le_left).op s)) := by
      rw [inf_assoc, inf_eq_right.mpr ((X.basicOpen_le _).trans inf_le_right)]

/-- The local-section form retains the literal restriction of a global section. -/
theorem nonvanishingOpen_restrict (L : LineBundle X) (s : Γ(L.val, ⊤)) (U : X.Opens) :
    nonvanishingOpenOn L U (L.val.val.map (homOfLE le_top).op s) =
      U ⊓ nonvanishingOpen L s :=
  nonvanishingOpenOn_restrict L le_top s

private theorem nonvanishingOpenOn_iso_le (L N : LineBundle X) (e : L.val ≅ N.val)
    (U : X.Opens) (s : Γ(L.val, U)) :
    nonvanishingOpenOn N U (e.hom.val.app (op U) s) ≤ nonvanishingOpenOn L U s := by
  apply iSup_le
  intro W
  apply iSup_le
  intro d
  rw [← PresheafOfModules.naturality_apply,
    Nonvanishing.coefficient_iso e W d]
  exact le_iSup_of_le W (le_iSup_of_le
    ((SheafOfModules.overFunctor X.ringCatSheaf W).mapIso e ≪≫ d) le_rfl)

/-- Transport by the actual module-sheaf isomorphism preserves the open. -/
theorem nonvanishingOpenOn_iso (L N : LineBundle X) (e : L.val ≅ N.val)
    (U : X.Opens) (s : Γ(L.val, U)) :
    nonvanishingOpenOn N U (e.hom.val.app (op U) s) = nonvanishingOpenOn L U s := by
  apply le_antisymm (nonvanishingOpenOn_iso_le L N e U s)
  have hh := nonvanishingOpenOn_iso_le N L e.symm U (e.hom.val.app (op U) s)
  have hs : e.inv.val.app (op U) (e.hom.val.app (op U) s) = s := by
    change (e.hom ≫ e.inv).val.app (op U) s = s
    rw [e.hom_inv_id]
    exact ModuleCat.id_apply (L.val.val.obj (op U)) s
  simpa only [Iso.symm_hom, hs] using hh

theorem nonvanishingOpen_iso (L N : LineBundle X) (e : L.val ≅ N.val)
    (s : Γ(L.val, ⊤)) :
    nonvanishingOpen N (e.hom.val.app (op ⊤) s) = nonvanishingOpen L s :=
  nonvanishingOpenOn_iso L N e ⊤ s

/-- Multiplying an actual section by an actual function intersects their
geometric nonvanishing opens. -/
theorem nonvanishingOpenOn_smul (L : LineBundle X) (U : X.Opens)
    (f : Γ(X, U)) (s : Γ(L.val, U)) :
    nonvanishingOpenOn L U (f • s) = X.basicOpen f ⊓ nonvanishingOpenOn L U s := by
  simp only [nonvanishingOpenOn, inf_iSup_eq]
  apply iSup_congr
  intro W
  apply iSup_congr
  intro e
  let M : X.Modules := L.val
  change X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right
      (M.presheaf.map (homOfLE inf_le_left).op (f • s))) =
    X.basicOpen f ⊓ X.basicOpen (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right
      (M.presheaf.map (homOfLE inf_le_left).op s))
  rw [Scheme.Modules.map_smul, _root_.map_smul, smul_eq_mul,
    X.basicOpen_mul, X.basicOpen_res]
  calc
    _ = X.basicOpen f ⊓ ((U ⊓ W) ⊓ X.basicOpen
        (chartSectionEquiv X L.val W e (U ⊓ W) inf_le_right
          (M.presheaf.map (homOfLE inf_le_left).op s))) := by ac_rfl
    _ = _ := by rw [inf_eq_right.mpr (X.basicOpen_le _)]

theorem nonvanishingOpen_smul (L : LineBundle X) (f : Γ(X, ⊤))
    (s : Γ(L.val, ⊤)) :
    nonvanishingOpen L (f • s) = X.basicOpen f ⊓ nonvanishingOpen L s :=
  nonvanishingOpenOn_smul L ⊤ f s

end AlgebraicGeometry.Scheme.Modules.Invertible
