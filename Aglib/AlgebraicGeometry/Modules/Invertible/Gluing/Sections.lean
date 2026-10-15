/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Matching sections for a rank-one transition cocycle

An actual unit on each pairwise intersection, satisfying the cocycle law under restriction,
defines a module of matching local functions on every open. These modules and their semilinear
restriction maps are the sections used to construct the glued rank-one module sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})

/-- The actual restriction homomorphism between two rings of scheme sections. -/
abbrev sectionRestrict {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
theorem sectionRestrict_refl (V : X.Opens) (s : Γ(X, V)) :
    sectionRestrict X (le_refl V) s = s := by
  change X.presheaf.map (𝟙 (op V)) s = s
  simp

@[simp]
theorem sectionRestrict_comp {U V W : X.Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(X, W)) :
    sectionRestrict X h (sectionRestrict X k s) = sectionRestrict X (h.trans k) s := by
  change (X.presheaf.map (homOfLE k).op ≫ X.presheaf.map (homOfLE h).op) s = _
  rw [← Functor.map_comp]
  rfl

variable {X} {ι : Type u} (U : ι → X.Opens)

/-- A rank-one transition cocycle consists of actual units on pairwise intersections. The
cocycle law is stated after the canonical restrictions to every common subopen. -/
structure UnitCocycle where
  /-- The transition function from the `j` component to the `i` component. -/
  transition (i j : ι) : (Γ(X, U i ⊓ U j))ˣ
  /-- The original units satisfy the cocycle identity on every triple overlap. -/
  cocycle (i j k : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    Units.map (sectionRestrict X (le_inf hi hj)).toMonoidHom (transition i j) *
      Units.map (sectionRestrict X (le_inf hj hk)).toMonoidHom (transition j k) =
      Units.map (sectionRestrict X (le_inf hi hk)).toMonoidHom (transition i k)

namespace UnitCocycle

variable {U} (c : UnitCocycle U)

/-- A transition unit restricted to a displayed common subopen. -/
def transitionOn (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) : (Γ(X, V))ˣ :=
  Units.map (sectionRestrict X (le_inf hi hj)).toMonoidHom (c.transition i j)

theorem transitionOn_cocycle (i j k : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    c.transitionOn i j hi hj * c.transitionOn j k hj hk = c.transitionOn i k hi hk :=
  c.cocycle i j k V hi hj hk

@[simp]
theorem transitionOn_self (i : ι) {V : X.Opens} (hi : V ≤ U i) :
    c.transitionOn i i hi hi = 1 := by
  have h := c.transitionOn_cocycle i i i hi hi hi
  exact mul_right_cancel (h.trans (one_mul _).symm)

@[simp]
theorem sectionRestrict_transitionOn (i j : ι) {V W : X.Opens}
    (h : V ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) :
    sectionRestrict X h (c.transitionOn i j hi hj : Γ(X, W)) =
      (c.transitionOn i j (h.trans hi) (h.trans hj) : Γ(X, V)) := by
  change sectionRestrict X h (sectionRestrict X _ _) = sectionRestrict X _ _
  rw [sectionRestrict_comp]

variable (U)

/-- Local functions on the intersections of an open with all cover charts. -/
def SectionFamily (V : X.Opens) : Type u := ∀ i, Γ(X, V ⊓ U i)

instance (V : X.Opens) : AddCommGroup (SectionFamily U V) :=
  inferInstanceAs (AddCommGroup (∀ i, Γ(X, V ⊓ U i)))

instance (V : X.Opens) : SMul Γ(X, V) (SectionFamily U V) where
  smul r s i := sectionRestrict X inf_le_left r * s i

instance (V : X.Opens) : Module Γ(X, V) (SectionFamily U V) where
  one_smul s := by
    funext i
    change sectionRestrict X _ (1 : Γ(X, V)) * s i = s i
    rw [map_one, one_mul]
  mul_smul r t s := by
    funext i
    change sectionRestrict X _ (r * t) * s i =
      sectionRestrict X _ r * (sectionRestrict X _ t * s i)
    rw [map_mul, mul_assoc]
  smul_add r s t := by funext i; exact mul_add _ _ _
  smul_zero r := by funext i; exact mul_zero _
  add_smul r t s := by
    funext i
    change sectionRestrict X _ (r + t) * s i =
      sectionRestrict X _ r * s i + sectionRestrict X _ t * s i
    rw [map_add, add_mul]
  zero_smul s := by
    funext i
    change sectionRestrict X _ (0 : Γ(X, V)) * s i = 0
    rw [map_zero, zero_mul]

@[simp]
theorem sectionFamily_smul_apply {V : X.Opens} (r : Γ(X, V)) (s : SectionFamily U V) (i : ι) :
    (r • s) i = sectionRestrict X inf_le_left r * s i := rfl

variable {U}

/-- The module of local functions whose restrictions agree via the given transition units. -/
def matchingSubmodule (V : X.Opens) : Submodule Γ(X, V) (SectionFamily U V) where
  carrier s := ∀ (W : X.Opens) (hWV : W ≤ V) (i j : ι) (hi : W ≤ U i) (hj : W ≤ U j),
    sectionRestrict X (le_inf hWV hi) (s i) =
      (c.transitionOn i j hi hj : Γ(X, W)) * sectionRestrict X (le_inf hWV hj) (s j)
  zero_mem' := by
    intro W hWV i j hi hj
    change sectionRestrict X _ 0 = _ * sectionRestrict X _ 0
    rw [map_zero, map_zero, mul_zero]
  add_mem' hs ht := by
    intro W hWV i j hi hj
    change sectionRestrict X _ (_ + _) = _ * sectionRestrict X _ (_ + _)
    rw [map_add, map_add, hs W hWV i j hi hj, ht W hWV i j hi hj, mul_add]
  smul_mem' r s hs := by
    intro W hWV i j hi hj
    simp only [sectionFamily_smul_apply, map_mul, sectionRestrict_comp]
    rw [hs W hWV i j hi hj]
    ring

/-- Matching section families, equipped with their actual section-ring module structure. -/
abbrev Sections (V : X.Opens) := ↥(c.matchingSubmodule V)

/-- Restriction of matching families is semilinear for the actual restriction of scalars. -/
def restrictSections {V W : X.Opens} (h : V ≤ W) :
    c.Sections W →ₛₗ[sectionRestrict X h] c.Sections V where
  toFun s := ⟨fun i => sectionRestrict X (inf_le_inf h le_rfl) (s.val i), by
    intro T hTV i j hi hj
    simp only [sectionRestrict_comp]
    exact s.property T (hTV.trans h) i j hi hj⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _
  map_smul' r s := by
    apply Subtype.ext
    funext i
    change sectionRestrict X _ (sectionRestrict X inf_le_left r * s.val i) =
      sectionRestrict X inf_le_left (sectionRestrict X h r) * sectionRestrict X _ (s.val i)
    rw [map_mul, sectionRestrict_comp, sectionRestrict_comp]

@[simp]
theorem restrictSections_apply {V W : X.Opens} (h : V ≤ W) (s : c.Sections W) (i : ι) :
    (c.restrictSections h s).val i =
      sectionRestrict X (inf_le_inf h le_rfl) (s.val i) := rfl

@[simp]
theorem restrictSections_refl (V : X.Opens) (s : c.Sections V) :
    c.restrictSections (le_refl V) s = s := by
  apply Subtype.ext
  funext i
  exact sectionRestrict_refl X _ _

@[simp]
theorem restrictSections_comp {V W T : X.Opens} (h : V ≤ W) (k : W ≤ T) (s : c.Sections T) :
    c.restrictSections h (c.restrictSections k s) = c.restrictSections (h.trans k) s := by
  apply Subtype.ext
  funext i
  exact sectionRestrict_comp X _ _ _

/-- On an open inside the `j` chart, the `j` component gives an ordinary section. -/
def localProjection (j : ι) {V : X.Opens} (hV : V ≤ U j) : c.Sections V →ₗ[Γ(X, V)] Γ(X, V) where
  toFun s := sectionRestrict X (le_inf le_rfl hV) (s.val j)
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    change sectionRestrict X _ (sectionRestrict X inf_le_left r * s.val j) =
      r * sectionRestrict X _ (s.val j)
    rw [map_mul, sectionRestrict_comp, sectionRestrict_refl]

/-- An ordinary section in one chart determines the matching family by the original transitions. -/
def fromLocal (j : ι) {V : X.Opens} (hV : V ≤ U j) (s : Γ(X, V)) : c.Sections V :=
  ⟨fun i => (c.transitionOn i j inf_le_right (inf_le_left.trans hV) : Γ(X, V ⊓ U i)) *
      sectionRestrict X inf_le_left s, by
    intro W hWV i k hi hk
    simp only [map_mul, sectionRestrict_transitionOn, sectionRestrict_comp]
    rw [← mul_assoc]
    exact congrArg (fun t : Γ(X, W) => t * sectionRestrict X hWV s)
      (congrArg Units.val (c.transitionOn_cocycle i k j hi hk (hWV.trans hV))).symm⟩

@[simp]
theorem fromLocal_apply (j : ι) {V : X.Opens} (hV : V ≤ U j) (s : Γ(X, V)) (i : ι) :
    (c.fromLocal j hV s).val i =
      (c.transitionOn i j inf_le_right (inf_le_left.trans hV) : Γ(X, V ⊓ U i)) *
        sectionRestrict X inf_le_left s := rfl

@[simp]
theorem fromLocal_localProjection (j : ι) {V : X.Opens} (hV : V ≤ U j) (s : c.Sections V) :
    c.fromLocal j hV (c.localProjection j hV s) = s := by
  apply Subtype.ext
  funext i
  have h := s.property (V ⊓ U i) inf_le_left i j inf_le_right (inf_le_left.trans hV)
  simpa only [fromLocal_apply, localProjection, LinearMap.coe_mk, AddHom.coe_mk,
    sectionRestrict_comp, sectionRestrict_refl] using h.symm

@[simp]
theorem localProjection_fromLocal (j : ι) {V : X.Opens} (hV : V ≤ U j) (s : Γ(X, V)) :
    c.localProjection j hV (c.fromLocal j hV s) = s := by
  change sectionRestrict X _ (_ * sectionRestrict X inf_le_left s) = s
  rw [map_mul, sectionRestrict_transitionOn, transitionOn_self, Units.val_one,
    one_mul, sectionRestrict_comp, sectionRestrict_refl]

/-- The local rank-one trivialization is evaluation at the displayed chart component. -/
def localSectionsEquiv (j : ι) {V : X.Opens} (hV : V ≤ U j) :
    c.Sections V ≃ₗ[Γ(X, V)] Γ(X, V) where
  __ := c.localProjection j hV
  invFun := c.fromLocal j hV
  left_inv := c.fromLocal_localProjection j hV
  right_inv := c.localProjection_fromLocal j hV

/-- The local trivialization commutes with the original restriction homomorphisms. -/
theorem localSectionsEquiv_restrict (j : ι) {V W : X.Opens}
    (h : V ≤ W) (hW : W ≤ U j) (s : c.Sections W) :
    c.localSectionsEquiv j (h.trans hW) (c.restrictSections h s) =
      sectionRestrict X h (c.localSectionsEquiv j hW s) := by
  change sectionRestrict X _ (sectionRestrict X _ (s.val j)) =
    sectionRestrict X _ (sectionRestrict X _ (s.val j))
  rw [sectionRestrict_comp, sectionRestrict_comp]

/-- Two local trivializations differ by multiplication by the original transition unit. -/
theorem localSectionsEquiv_transition (i j : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) (s : c.Sections V) :
    c.localSectionsEquiv i hi s =
      (c.transitionOn i j hi hj : Γ(X, V)) * c.localSectionsEquiv j hj s :=
  s.property V le_rfl i j hi hj

end UnitCocycle

end AlgebraicGeometry.Scheme.Modules.Invertible
