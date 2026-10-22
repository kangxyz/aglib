/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# The intrinsic unit cocycle of actual module frames

The change coefficient from an original chart generator to another original
frame is a unit. These units satisfy the actual cocycle equation under
restriction. The native matching-section construction recovers the original
module sheaf, and its forward map is the original frame map on every chart.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace LocalFrames

/-- A frame on an actual open chart gives the corresponding frame on its original open range. -/
def overFrameOfChart {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    M.over j.opensRange ≅ SheafOfModules.unit (X.ringCatSheaf.over j.opensRange) := by
  let eR : M.restrict j.opensRange.ι ≅
      SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf :=
    (restrictFunctorIsoPullback j.opensRange.ι).app M ≪≫
      (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j).symm).app M ≪≫
      ((pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso e.symm ≪≫
      pullbackUnitIso j.isoOpensRange.inv
  exact (overEquiv j.opensRange).functor.preimageIso
    ((overFunctorEquiv j.opensRange).app M ≪≫ eR ≪≫ (overUnitIso j.opensRange).symm)


variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (M : X.Modules)
  (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))

/-- The actual coefficient in the displayed local frame. -/
abbrev coefficient (i : ι) {V : X.Opens} (hi : V ≤ U i) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) := chartSectionEquiv X M (U i) (e i) V hi

/-- The same frame generator on every original subopen. -/
def generator (i : ι) {V : X.Opens} (hi : V ≤ U i) : Γ(M, V) :=
  (coefficient U M e i hi).symm 1

@[simp]
theorem coefficient_generator (i : ι) {V : X.Opens} (hi : V ≤ U i) :
    coefficient U M e i hi (generator U M e i hi) = 1 :=
  (coefficient U M e i hi).apply_symm_apply 1

theorem coefficient_restrict (i : ι) {V W : X.Opens} (h : V ≤ W) (hi : W ≤ U i)
    (s : Γ(M, W)) :
    coefficient U M e i (h.trans hi) (M.val.map (homOfLE h).op s) =
      sectionRestrict X h (coefficient U M e i hi s) := by
  let q : Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi) :=
    Over.homMk (homOfLE h)
  exact PresheafOfModules.naturality_apply (e i).hom.val q.op s

theorem generator_restrict (i : ι) {V W : X.Opens} (h : V ≤ W) (hi : W ≤ U i) :
    M.val.map (homOfLE h).op (generator U M e i hi) = generator U M e i (h.trans hi) := by
  apply (coefficient U M e i (h.trans hi)).injective
  rw [coefficient_restrict U M e i h hi, coefficient_generator, coefficient_generator, map_one]

theorem coefficient_smul_generator (i : ι) {V : X.Opens} (hi : V ≤ U i) (s : Γ(M, V)) :
    coefficient U M e i hi s • generator U M e i hi = s := by
  apply (coefficient U M e i hi).injective
  rw [_root_.map_smul, coefficient_generator, smul_eq_mul, mul_one]

theorem coefficient_transition (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : Γ(M, V)) :
    coefficient U M e i hi s =
      coefficient U M e i hi (generator U M e j hj) * coefficient U M e j hj s := by
  conv_lhs => rw [← coefficient_smul_generator U M e j hj s]
  rw [_root_.map_smul, smul_eq_mul, mul_comm]

/-- The actual change-of-frame unit on a common subopen. -/
def transitionUnitOn (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    Γ(X, V)ˣ where
  val := coefficient U M e i hi (generator U M e j hj)
  inv := coefficient U M e j hj (generator U M e i hi)
  val_inv := by
    have h := coefficient_transition U M e i j hi hj (generator U M e i hi)
    rw [coefficient_generator] at h
    exact h.symm
  inv_val := by
    have h := coefficient_transition U M e j i hj hi (generator U M e j hj)
    rw [coefficient_generator] at h
    exact h.symm

theorem transitionUnitOn_restrict (i j : ι) {V W : X.Opens} (h : V ≤ W)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    Units.map (sectionRestrict X h).toMonoidHom (transitionUnitOn U M e i j hi hj) =
      transitionUnitOn U M e i j (h.trans hi) (h.trans hj) := by
  apply Units.ext
  change sectionRestrict X h (coefficient U M e i hi (generator U M e j hj)) = _
  rw [← coefficient_restrict, generator_restrict]
  rfl

theorem transitionUnitOn_cocycle (i j k : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    transitionUnitOn U M e i j hi hj * transitionUnitOn U M e j k hj hk =
      transitionUnitOn U M e i k hi hk := by
  apply Units.ext
  exact (coefficient_transition U M e i j hi hj (generator U M e k hk)).symm

/-- The original local frames give an actual unit cocycle, rather than a cocycle premise. -/
def cocycle : UnitCocycle U where
  transition i j := transitionUnitOn U M e i j inf_le_left inf_le_right
  cocycle i j k V hi hj hk := by
    rw [transitionUnitOn_restrict, transitionUnitOn_restrict, transitionUnitOn_restrict]
    exact transitionUnitOn_cocycle U M e i j k hi hj hk

theorem cocycle_transitionOn (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    (cocycle U M e).transitionOn i j hi hj = transitionUnitOn U M e i j hi hj :=
  transitionUnitOn_restrict U M e i j (le_inf hi hj) inf_le_left inf_le_right

variable (hU : iSup U = ⊤)

/-- The actual frame generators satisfy the constructed coefficient cocycle. -/
theorem generator_compatible (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    M.val.map (homOfLE hj).op (generator U M e j le_rfl) =
      ((cocycle U M e).transitionOn i j hi hj).val •
        M.val.map (homOfLE hi).op (generator U M e i le_rfl) := by
  rw [generator_restrict, generator_restrict, cocycle_transitionOn]
  exact (coefficient_smul_generator U M e i hi (generator U M e j hj)).symm

/-- The original frame generators define the actual global gluing morphism. -/
def sheafHom : (cocycle U M e).sheaf ⟶ M :=
  (cocycle U M e).homOfLocalSections M hU (fun i => generator U M e i le_rfl)
    (generator_compatible U M e)

/-- The glued map is the exact original frame comparison on each chart. -/
theorem sheafHom_over (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (sheafHom U M e hU) =
      ((cocycle U M e).localIso i).hom ≫ (e i).inv := by
  apply SheafOfModules.hom_ext
  ext V s
  have hs := (cocycle U M e).homOfLocalSections_apply M hU
    (fun k => generator U M e k le_rfl) (generator_compatible U M e)
    i V.unop.left (leOfHom V.unop.hom) s
  change (sheafHom U M e hU).val.app (op V.unop.left) s = _
  refine hs.trans ?_
  rw [generator_restrict U M e i (leOfHom V.unop.hom) le_rfl]
  apply (coefficient U M e i (leOfHom V.unop.hom)).injective
  rw [_root_.map_smul, coefficient_generator, smul_eq_mul, mul_one]
  exact ((coefficient U M e i (leOfHom V.unop.hom)).apply_symm_apply _).symm

instance sheafHomIsIso : IsIso (sheafHom U M e hU) := by
  apply Scheme.Modules.Pullback.OpenRestriction.isIso_of_local_restrict
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
  refine ⟨U i, hi, ?_⟩
  have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map
      (sheafHom U M e hU)) := by
    rw [sheafHom_over]
    infer_instance
  exact (NatIso.isIso_map_iff (overFunctorEquiv (U i)) (sheafHom U M e hU)).mp
    (inferInstanceAs (IsIso ((overEquiv (U i)).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (sheafHom U M e hU)))))

/-- The intrinsic frame cocycle recovers the original module sheaf. -/
def sheafIso : (cocycle U M e).sheaf ≅ M := asIso (sheafHom U M e hU)

/-- The reconstruction isomorphism retains each original local frame morphism. -/
theorem sheafIso_hom_over (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (sheafIso U M e hU).hom =
      ((cocycle U M e).localIso i).hom ≫ (e i).inv :=
  sheafHom_over U M e hU i

end LocalFrames
end AlgebraicGeometry.Scheme.Modules.Invertible
