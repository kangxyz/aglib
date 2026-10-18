/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian

/-!
# General finite-etale section lifting

Relocated unchanged declarations from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original namespaces and explicit
source and hypothesis boundaries are retained.
-/

@[expose] public section

/-!
# Curves / Cyclic / Covers / SectionLifting

Object-based extraction of the Wangcai checkpoint-27 construction.
Existing qualified declarations and their explicit mathematical premises are retained.
-/

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
universe u
namespace AlgebraicGeometry.Scheme.FiniteEtale.SectionLifting

/-- The finite étale cover of `X` with structure morphism `𝟙 X`. -/
def identityCover (X : Scheme.{u}) : Scheme.FiniteEtale X :=
  ⟨Over.mk (𝟙 X), by change IsFinite (𝟙 X); infer_instance, by change Etale (𝟙 X); infer_instance⟩

/-- The morphism from the pulled-back identity cover to the pulled-back cover `C`
induced by `s`, using the equation `hs : s ≫ C.obj.hom = f`. -/
def restrictedSection {X S : Scheme.{u}} (f : S ⟶ X) (C : Scheme.FiniteEtale X)
    (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    (baseChange f).obj (identityCover X) ⟶ (baseChange f).obj C :=
  ⟨Over.homMk (pullback.lift (pullback.snd (𝟙 X) f ≫ s)
    (pullback.snd (𝟙 X) f) (by simp [Category.assoc,
      _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget, hs])) (by
      exact pullback.lift_snd _ _ _)⟩

/-- The section of `C` obtained as a preimage of `restrictedSection` under the
explicit fullness assumption on `baseChange f`. -/
def liftedSection {X S : Scheme.{u}} (f : S ⟶ X) [(baseChange f).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    X ⟶ C.obj.left :=
  ((baseChange f).preimage (restrictedSection f C s hs)).hom.left

theorem liftedSection_isSection {X S : Scheme.{u}} (f : S ⟶ X) [(baseChange f).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    liftedSection f C s hs ≫ C.obj.hom = 𝟙 X :=
  Over.w ((baseChange f).preimage (restrictedSection f C s hs)).hom

theorem liftedSection_restrict {X S : Scheme.{u}} (f : S ⟶ X) [(baseChange f).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    f ≫ liftedSection f C s hs = s := by
  have h := (baseChange f).map_preimage (restrictedSection f C s hs)
  have h' := congrArg (fun m => m.hom.left ≫ pullback.fst C.obj.hom f) h
  have h'' := congrArg (fun m => pullback.lift f (𝟙 S) (by change f ≫ 𝟙 X = 𝟙 S ≫ f; simp) ≫ m) h'
  simpa [baseChange, restrictedSection, liftedSection, identityCover,
    Category.assoc, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget] using h''

/-- The identity pullback form matches the proper-henselian comparison directly. -/
def liftedSectionViaIdentityPullback {X S : Scheme.{u}} (f : S ⟶ X)
    [(baseChange (pullback.fst (𝟙 X) f)).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) : X ⟶ C.obj.left :=
  liftedSection (pullback.fst (𝟙 X) f) C (pullback.snd (𝟙 X) f ≫ s)
    (by rw [Category.assoc, hs]; simpa using (pullback.condition (f := 𝟙 X) (g := f)).symm)

theorem liftedSectionViaIdentityPullback_isSection {X S : Scheme.{u}} (f : S ⟶ X)
    [(baseChange (pullback.fst (𝟙 X) f)).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    liftedSectionViaIdentityPullback f C s hs ≫ C.obj.hom = 𝟙 X :=
  liftedSection_isSection _ _ _ _

theorem liftedSectionViaIdentityPullback_restrict {X S : Scheme.{u}} (f : S ⟶ X)
    [(baseChange (pullback.fst (𝟙 X) f)).Full]
    (C : Scheme.FiniteEtale X) (s : S ⟶ C.obj.left) (hs : s ≫ C.obj.hom = f) :
    f ≫ liftedSectionViaIdentityPullback f C s hs = s := by
  have h := liftedSection_restrict (pullback.fst (𝟙 X) f) C
    (pullback.snd (𝟙 X) f ≫ s)
    (by rw [Category.assoc, hs]; simpa using (pullback.condition (f := 𝟙 X) (g := f)).symm)
  have h' := congrArg (fun m => pullback.lift f (𝟙 S) (by simp) ≫ m) h
  simpa [liftedSectionViaIdentityPullback, ← Category.assoc] using h'

end AlgebraicGeometry.Scheme.FiniteEtale.SectionLifting

end -- noncomputable section
end
section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.FiniteEtale.SectionLifting
variable (R : Type u) [CommRing R] [HenselianLocalRing R]
local notation "res" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Actual henselian lifting of an arbitrary residue-field section of an actual
finite-etale cover, derived from the universal proper comparison at Spec R. -/
def henselianSection (H : ProperHenselianComparison R)
    (C : Scheme.FiniteEtale (Spec (.of R)))
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res) : Spec (.of R) ⟶ C.obj.left := by
  letI := H (Spec (.of R)) (𝟙 _) (by infer_instance)
  exact liftedSectionViaIdentityPullback res C s hs

theorem henselianSection_isSection (H : ProperHenselianComparison R)
    (C : Scheme.FiniteEtale (Spec (.of R)))
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res) :
    henselianSection R H C s hs ≫ C.obj.hom = 𝟙 _ := by
  let := H (Spec (.of R)) (𝟙 _) (by infer_instance)
  exact liftedSectionViaIdentityPullback_isSection res C s hs

theorem henselianSection_restrict (H : ProperHenselianComparison R)
    (C : Scheme.FiniteEtale (Spec (.of R)))
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res) : res ≫ henselianSection R H C s hs = s := by
  let := H (Spec (.of R)) (𝟙 _) (by infer_instance)
  exact liftedSectionViaIdentityPullback_restrict res C s hs

/-- A chosen residue point above any actual R-section lifts to a section of the
same finite-etale cover, without a specialized origin-lifting premise. -/
def henselianPointAboveSection (H : ProperHenselianComparison R)
    {Y : Scheme.{u}} (C : Scheme.FiniteEtale Y) (e : Spec (.of R) ⟶ Y)
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res ≫ e) : Spec (.of R) ⟶ C.obj.left :=
  henselianSection R H ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.baseChange e).obj C)
    (pullback.lift s res hs) (pullback.lift_snd _ _ _) ≫ pullback.fst C.obj.hom e

theorem henselianPointAboveSection_over (H : ProperHenselianComparison R)
    {Y : Scheme.{u}} (C : Scheme.FiniteEtale Y) (e : Spec (.of R) ⟶ Y)
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res ≫ e) :
    henselianPointAboveSection R H C e s hs ≫ C.obj.hom = e := by
  have h := congrArg (fun m => m ≫ e)
    (henselianSection_isSection R H
      ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.baseChange e).obj C)
      (pullback.lift s res hs) (pullback.lift_snd _ _ _))
  simpa only [henselianPointAboveSection, Category.assoc, pullback.condition,
    Category.id_comp, _root_.AlgebraicGeometry.Scheme.FiniteEtale.baseChange_obj_hom] using h

theorem henselianPointAboveSection_restrict (H : ProperHenselianComparison R)
    {Y : Scheme.{u}} (C : Scheme.FiniteEtale Y) (e : Spec (.of R) ⟶ Y)
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (hs : s ≫ C.obj.hom = res ≫ e) :
    res ≫ henselianPointAboveSection R H C e s hs = s := by
  unfold henselianPointAboveSection
  rw [← Category.assoc, henselianSection_restrict]
  exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.SectionLifting

end -- noncomputable section
end

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fee30341f7d3dace45aeb50564c5ebdf9db0639f9030151439354567a933a830.
Definitions, hypotheses and universes are retained modulo native names. -/
