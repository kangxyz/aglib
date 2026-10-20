/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.PowerNode.Saturated

/-!
Source: `R5Lab.AlgebraicGeometry.Curves.LocalModels.PointedResolution.Rees.Charts`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`11dd3878cab7ac3f34551117fea645045cbad307061a95f0a581a41836c8e8b7`.
The actual localization subalgebras, maps and original domain/UFD/nonzero-scalar
conditions are retained. These algebraic calculations do not supply a global
blowup or a geometric atlas. This leaf has no scheme-level dependency.
-/

@[expose] public section

/-!
# The literal left, right and middle saturated Rees chart equivalences of a power-node blowup.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open Polynomial
open scoped Polynomial
universe u

section LeftReesChart


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

def leftChart (π : R) (m : ℕ) : Subalgebra R (leftLocalization π m) :=
  (Localization.Away.saturatedChart (node π (m+2)) (centerIdeal π (m+2)) (PlaneNode.U
    (π^(m+2)))).restrictScalars R

lemma leftParameter_mem (π : R) (m : ℕ) : leftParameter π m ∈ leftChart π m := by
  have h : algebraMap R (node π (m+2)) π ∈ centerIdeal π (m+2) :=
    Ideal.subset_span (by simp)
  simpa [Localization.Away.fraction, leftParameter, leftChart, ← IsScalarTower.algebraMap_apply R
    (node π (m+2))] using
    Localization.Away.fraction_mem (centerIdeal π (m+2)) (PlaneNode.U (π^(m+2))) (algebraMap R _
      π) h

lemma left_range_eq (π : R) (m : ℕ) : (leftToLocalization π m).range = leftChart π m := by
  apply le_antisymm
  · apply nodeLift_range_le
    · exact (Localization.Away.saturatedChart (node π (m+2)) (centerIdeal π (m+2))
        (PlaneNode.U (π^(m+2)))).algebraMap_mem _
    · exact leftParameter_mem π m
  · apply Localization.Away.saturatedChart_le
    · intro z
      refine ⟨leftBase π m z, ?_⟩
      exact congrArg (fun f : node π (m+2) →ₐ[R] leftLocalization π m => f z)
        (left_base_triangle π m)
    · intro b hb
      rcases hb with rfl | rfl | rfl
      · rw [Localization.Away.fraction_self]; exact (leftToLocalization π m).range.one_mem
      · rw [left_ratio_v]
        exact ⟨algebraMap R _ (π^m) * PlaneNode.V π ^ 2, by simp⟩
      · exact ⟨PlaneNode.V π, by simp [Localization.Away.fraction, ←
        IsScalarTower.algebraMap_apply R (node π (m+2))]⟩

/-- The saturated u-Rees chart is the literal outer node ring, with no quotient torsion. -/
def leftReesEquiv [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) : PlaneNode.Ring π ≃ₐ[R] leftChart π m :=
  (AlgEquiv.ofInjective (leftToLocalization π m) (leftToLocalization_injective π hπ m)).trans
    (Subalgebra.equivOfEq _ _ (left_range_eq π m))

@[simp] lemma leftReesEquiv_coe [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : PlaneNode.Ring π) :
    (leftReesEquiv π hπ m z : leftLocalization π m) = leftToLocalization π m z := rfl

lemma leftReesEquiv_base [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : node π (m + 2)) :
    leftReesEquiv π hπ m (leftBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (PlaneNode.U (π^(m+2)))) z := by
  apply Subtype.ext
  exact congrArg (fun f : node π (m+2) →ₐ[R] leftLocalization π m => f z)
    (left_base_triangle π m)

end PowerNode.Rees

end
end LeftReesChart

section NodeSwap


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

def nodeSwap (c : R) : PlaneNode.Ring c →ₐ[R] PlaneNode.Ring c :=
  PlaneNode.lift c (PlaneNode.V c) (PlaneNode.U c) (by rw [mul_comm, PlaneNode.relation])
@[simp] lemma nodeSwap_u (c : R) : nodeSwap c (PlaneNode.U c) = PlaneNode.V c := by simp [nodeSwap]
@[simp] lemma nodeSwap_v (c : R) : nodeSwap c (PlaneNode.V c) = PlaneNode.U c := by simp [nodeSwap]
lemma nodeSwap_comp (c : R) : (nodeSwap c).comp (nodeSwap c) = AlgHom.id R _ := by
  apply PlaneNode.hom_ext <;> simp
@[simp] lemma nodeSwap_twice (c : R) (z : PlaneNode.Ring c) : nodeSwap c (nodeSwap c z) = z :=
  congrArg (fun f : PlaneNode.Ring c →ₐ[R] PlaneNode.Ring c => f z) (nodeSwap_comp c)

def swapAwayUV (c : R) : Localization.Away (PlaneNode.U c) →ₐ[R] Localization.Away (PlaneNode.V c)
  :=
  IsLocalization.Away.liftAlgHom (PlaneNode.U c)
    (f := (IsScalarTower.toAlgHom R (PlaneNode.Ring c) _).comp (nodeSwap c)) (by
      simpa using (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (PlaneNode.V c)) (PlaneNode.V c)))
def swapAwayVU (c : R) : Localization.Away (PlaneNode.V c) →ₐ[R] Localization.Away (PlaneNode.U c)
  :=
  IsLocalization.Away.liftAlgHom (PlaneNode.V c)
    (f := (IsScalarTower.toAlgHom R (PlaneNode.Ring c) _).comp (nodeSwap c)) (by
      simpa using (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (PlaneNode.U c)) (PlaneNode.U c)))
@[simp] lemma swapAwayUV_base (c : R) (z : PlaneNode.Ring c) :
    swapAwayUV c (algebraMap (PlaneNode.Ring c) _ z) = algebraMap (PlaneNode.Ring c) _ (nodeSwap c
      z) := by
  simp [swapAwayUV]
@[simp] lemma swapAwayVU_base (c : R) (z : PlaneNode.Ring c) :
    swapAwayVU c (algebraMap (PlaneNode.Ring c) _ z) = algebraMap (PlaneNode.Ring c) _ (nodeSwap c
      z) := by
  simp [swapAwayVU]

/-- Exchange the original node coordinates and their actual localization denominators. -/
def nodeSwapAway (c : R) : Localization.Away (PlaneNode.U c) ≃ₐ[R] Localization.Away (PlaneNode.V
  c) :=
  AlgEquiv.ofAlgHom (swapAwayUV c) (swapAwayVU c)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (PlaneNode.V c))
      apply AlgHom.ext
      intro z
      change swapAwayUV c (swapAwayVU c (algebraMap (PlaneNode.Ring c) _ z)) =
        algebraMap (PlaneNode.Ring c) _ z
      simp)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (PlaneNode.U c))
      apply AlgHom.ext
      intro z
      change swapAwayVU c (swapAwayUV c (algebraMap (PlaneNode.Ring c) _ z)) =
        algebraMap (PlaneNode.Ring c) _ z
      simp)

lemma swapAwayUV_inverse (c : R) :
    swapAwayUV c (IsLocalization.Away.invSelf (S := Localization.Away (PlaneNode.U c))
      (PlaneNode.U c)) =
      IsLocalization.Away.invSelf (S := Localization.Away (PlaneNode.V c)) (PlaneNode.V c) := by
  apply Localization.Away.map_invSelf_of_mul
  simp

end PowerNode.Rees

end
end NodeSwap

section RightReesChart


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

abbrev rightLocalization (π : R) (m : ℕ) := Localization.Away (PlaneNode.V (π^(m+2)))
abbrev rightParameter (π : R) (m : ℕ) : rightLocalization π m :=
  algebraMap R _ π * IsLocalization.Away.invSelf (PlaneNode.V (π^(m+2)))

def rightBase (π : R) (m : ℕ) : node π (m+2) →ₐ[R] PlaneNode.Ring π :=
  (leftBase π m).comp (nodeSwap (π^(m+2)))
@[simp] lemma rightBase_u (π : R) (m : ℕ) :
    rightBase π m (PlaneNode.U (π^(m+2))) = algebraMap R _ (π^(m+1)) * PlaneNode.V π := by
  simp [rightBase, leftBase]
@[simp] lemma rightBase_v (π : R) (m : ℕ) :
    rightBase π m (PlaneNode.V (π^(m+2))) = PlaneNode.U π := by simp [rightBase, leftBase]

def rightToLocalization (π : R) (m : ℕ) : PlaneNode.Ring π →ₐ[R] rightLocalization π m :=
  (swapAwayUV (π^(m+2))).comp (leftToLocalization π m)
@[simp] lemma rightToLocalization_u (π : R) (m : ℕ) :
    rightToLocalization π m (PlaneNode.U π) =
      algebraMap (node π (m+2)) _ (PlaneNode.V (π^(m+2))) := by
  simp [rightToLocalization]
@[simp] lemma rightToLocalization_v (π : R) (m : ℕ) :
    rightToLocalization π m (PlaneNode.V π) = rightParameter π m := by
  simp [rightToLocalization, leftParameter, swapAwayUV_inverse]

lemma right_base_triangle (π : R) (m : ℕ) :
    (rightToLocalization π m).comp (rightBase π m) =
      IsScalarTower.toAlgHom R (node π (m+2)) (rightLocalization π m) := by
  apply AlgHom.ext
  intro z
  change swapAwayUV (π^(m+2))
    (((leftToLocalization π m).comp (leftBase π m)) (nodeSwap (π^(m+2)) z)) = _
  rw [left_base_triangle]
  change swapAwayUV (π^(m+2))
    (algebraMap (node π (m+2)) _ (nodeSwap (π^(m+2)) z)) = _
  simp

lemma right_ratio_u (π : R) (m : ℕ) :
    Localization.Away.fraction (PlaneNode.V (π^(m+2))) (PlaneNode.U (π^(m+2))) =
      algebraMap R (rightLocalization π m) (π^m) * rightParameter π m ^ 2 := by
  have h := congrArg (swapAwayUV (π^(m+2))) (left_ratio_v π m)
  simpa [Localization.Away.fraction, swapAwayUV_inverse, leftParameter] using h

lemma rightToLocalization_injective [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) : Function.Injective (rightToLocalization π m) :=
  (nodeSwapAway (π^(m+2))).injective.comp (leftToLocalization_injective π hπ m)

def rightChart (π : R) (m : ℕ) : Subalgebra R (rightLocalization π m) :=
  (Localization.Away.saturatedChart (node π (m+2)) (centerIdeal π (m+2)) (PlaneNode.V
    (π^(m+2)))).restrictScalars R

lemma rightParameter_mem (π : R) (m : ℕ) : rightParameter π m ∈ rightChart π m := by
  have h : algebraMap R (node π (m+2)) π ∈ centerIdeal π (m+2) :=
    Ideal.subset_span (by simp)
  simpa [Localization.Away.fraction, rightParameter, rightChart, ← IsScalarTower.algebraMap_apply
    R (node π (m+2))] using
    Localization.Away.fraction_mem (centerIdeal π (m+2)) (PlaneNode.V (π^(m+2))) (algebraMap R _
      π) h

lemma right_range_eq (π : R) (m : ℕ) : (rightToLocalization π m).range = rightChart π m := by
  have hrep : rightToLocalization π m = PlaneNode.lift π
      (algebraMap (node π (m+2)) _ (PlaneNode.V (π^(m+2))))
      (rightParameter π m) (by
        have h := congrArg (rightToLocalization π m) (PlaneNode.relation π)
        simpa using h) := by
    apply PlaneNode.hom_ext <;> simp
  apply le_antisymm
  · rw [hrep]
    apply nodeLift_range_le
    · exact (Localization.Away.saturatedChart (node π (m+2)) (centerIdeal π (m+2))
        (PlaneNode.V (π^(m+2)))).algebraMap_mem _
    · exact rightParameter_mem π m
  · apply Localization.Away.saturatedChart_le
    · intro z
      refine ⟨rightBase π m z, ?_⟩
      exact congrArg (fun f : node π (m+2) →ₐ[R] rightLocalization π m => f z)
        (right_base_triangle π m)
    · intro b hb
      rcases hb with rfl | rfl | rfl
      · rw [right_ratio_u]
        exact ⟨algebraMap R _ (π^m) * PlaneNode.V π ^ 2, by simp⟩
      · rw [Localization.Away.fraction_self]; exact (rightToLocalization π m).range.one_mem
      · exact ⟨PlaneNode.V π, by simp [Localization.Away.fraction, ←
        IsScalarTower.algebraMap_apply R (node π (m+2))]⟩

/-- The saturated v-Rees chart, with outer variables v and q = pi/v. -/
def rightReesEquiv [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) : PlaneNode.Ring π ≃ₐ[R] rightChart π m :=
  (AlgEquiv.ofInjective (rightToLocalization π m) (rightToLocalization_injective π hπ m)).trans
    (Subalgebra.equivOfEq _ _ (right_range_eq π m))
@[simp] lemma rightReesEquiv_coe [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : PlaneNode.Ring π) :
    (rightReesEquiv π hπ m z : rightLocalization π m) = rightToLocalization π m z := rfl
lemma rightReesEquiv_base [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : node π (m + 2)) :
    rightReesEquiv π hπ m (rightBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (PlaneNode.V (π^(m+2)))) z := by
  apply Subtype.ext
  exact congrArg (fun f : node π (m+2) →ₐ[R] rightLocalization π m => f z)
    (right_base_triangle π m)

end PowerNode.Rees

end
end RightReesChart

section MiddleReesChart


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

abbrev middleDen (π : R) (m : ℕ) : node π (m+2) := algebraMap R _ π
abbrev middleLocalization (π : R) (m : ℕ) := Localization.Away (middleDen π m)
abbrev middleInv (π : R) (m : ℕ) : middleLocalization π m :=
  IsLocalization.Away.invSelf (middleDen π m)
abbrev middleU (π : R) (m : ℕ) : middleLocalization π m :=
  Localization.Away.fraction (middleDen π m) (PlaneNode.U (π^(m+2)))
abbrev middleV (π : R) (m : ℕ) : middleLocalization π m :=
  Localization.Away.fraction (middleDen π m) (PlaneNode.V (π^(m+2)))

lemma middleInv_relation (π : R) (m : ℕ) :
    algebraMap R (middleLocalization π m) π * middleInv π m = 1 := by
  rw [IsScalarTower.algebraMap_apply R (node π (m+2))]
  exact IsLocalization.Away.mul_invSelf (middleDen π m)

lemma middle_relation (π : R) (m : ℕ) :
    middleU π m * middleV π m = algebraMap R _ (π^m) := by
  calc
    _ = algebraMap (node π (m+2)) (middleLocalization π m)
        (PlaneNode.U (π^(m+2)) * PlaneNode.V (π^(m+2))) * middleInv π m ^ 2 := by
          simp only [Localization.Away.fraction, map_mul]; ring
    _ = algebraMap R (middleLocalization π m) (π^(m+2)) * middleInv π m ^ 2 := by
      rw [PlaneNode.relation, ← IsScalarTower.algebraMap_apply R (node π (m+2))]
    _ = algebraMap R _ (π^m) * (algebraMap R _ π * middleInv π m)^2 := by
      have hp : algebraMap R (middleLocalization π m) (π^(m+2)) =
          algebraMap R _ (π^m) * algebraMap R _ π ^ 2 := by
        calc
          _ = algebraMap R _ (π^m * π^2) := congrArg
            (algebraMap R (middleLocalization π m)) (pow_add π m 2)
          _ = algebraMap R _ (π^m) * algebraMap R _ (π^2) := map_mul _ _ _
          _ = _ := congrArg (fun z => algebraMap R (middleLocalization π m) (π^m) * z)
            (map_pow (algebraMap R (middleLocalization π m)) π 2)
      rw [hp]
      ring
    _ = _ := by rw [middleInv_relation]; simp

/-- Literal u/pi and v/pi coordinates inside A[1/pi], including m = 0. -/
def middleToLocalization (π : R) (m : ℕ) : node π m →ₐ[R] middleLocalization π m :=
  PlaneNode.lift (π^m) (middleU π m) (middleV π m) (middle_relation π m)

@[simp] lemma middleToLocalization_u (π : R) (m : ℕ) :
    middleToLocalization π m (PlaneNode.U (π^m)) = middleU π m := by simp [middleToLocalization]
@[simp] lemma middleToLocalization_v (π : R) (m : ℕ) :
    middleToLocalization π m (PlaneNode.V (π^m)) = middleV π m := by simp [middleToLocalization]

lemma middle_base_triangle (π : R) (m : ℕ) :
    (middleToLocalization π m).comp (middleBase π m) =
      IsScalarTower.toAlgHom R (node π (m+2)) (middleLocalization π m) := by
  apply PlaneNode.hom_ext <;>
    simp only [AlgHom.comp_apply, middleBase, PlaneNode.lift_U, PlaneNode.lift_V,
      map_mul, AlgHom.commutes, middleToLocalization_u, middleToLocalization_v,
      Localization.Away.fraction]
  all_goals
    rw [mul_left_comm, middleInv_relation, mul_one]
    rfl

abbrev middleTargetDen (π : R) (m : ℕ) : node π m := algebraMap R _ π
abbrev middleTargetLocalization (π : R) (m : ℕ) := Localization.Away (middleTargetDen π m)

def middleLocalizationBack (π : R) (m : ℕ) :
    middleLocalization π m →ₐ[R] middleTargetLocalization π m :=
  IsLocalization.Away.liftAlgHom (middleDen π m)
    (f := (IsScalarTower.toAlgHom R (node π m) _).comp (middleBase π m)) (by
      change IsUnit (algebraMap (node π m) _
        (middleBase π m (algebraMap R (node π (m+2)) π)))
      rw [AlgHom.commutes]
      exact IsLocalization.Away.algebraMap_isUnit (middleTargetDen π m))

@[simp] lemma middleLocalizationBack_base (π : R) (m : ℕ) (z : node π (m + 2)) :
    middleLocalizationBack π m (algebraMap (node π (m+2)) _ z) =
      algebraMap (node π m) _ (middleBase π m z) := by simp [middleLocalizationBack]

lemma middleLocalizationBack_inverse (π : R) (m : ℕ) :
    middleLocalizationBack π m (middleInv π m) =
      IsLocalization.Away.invSelf (S := middleTargetLocalization π m) (middleTargetDen π m) := by
  apply Localization.Away.map_invSelf_of_mul
  change middleLocalizationBack π m (algebraMap (node π (m+2)) _ (middleDen π m)) *
    IsLocalization.Away.invSelf (middleTargetDen π m) = 1
  rw [middleLocalizationBack_base, AlgHom.commutes]
  exact IsLocalization.Away.mul_invSelf (middleTargetDen π m)

lemma middle_localized_retraction (π : R) (m : ℕ) :
    (middleLocalizationBack π m).comp (middleToLocalization π m) =
      IsScalarTower.toAlgHom R (node π m) (middleTargetLocalization π m) := by
  apply PlaneNode.hom_ext <;>
    simp only [AlgHom.comp_apply, middleToLocalization_u, middleToLocalization_v,
      Localization.Away.fraction, map_mul, middleLocalizationBack_base,
        middleLocalizationBack_inverse,
      middleBase, PlaneNode.lift_U, PlaneNode.lift_V]
  all_goals
    rw [mul_right_comm, IsLocalization.Away.mul_invSelf, one_mul]
    rfl

lemma middleToLocalization_injective [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) : Function.Injective (middleToLocalization π m) := by
  have hden : middleTargetDen π m ≠ 0 :=
    (map_ne_zero_iff _ (node_algebraMap_injective (π^m))).mpr hπ
  have h := node_away_injective (π^m) (pow_ne_zero m hπ) (middleTargetDen π m) hden
  intro x y hxy
  apply h
  have hback := congrArg (middleLocalizationBack π m) hxy
  change ((middleLocalizationBack π m).comp (middleToLocalization π m)) x =
    ((middleLocalizationBack π m).comp (middleToLocalization π m)) y at hback
  rw [middle_localized_retraction] at hback
  exact hback

def middleChart (π : R) (m : ℕ) : Subalgebra R (middleLocalization π m) :=
  (Localization.Away.saturatedChart (node π (m+2)) (centerIdeal π (m+2)) (middleDen π
    m)).restrictScalars R

lemma middle_range_eq (π : R) (m : ℕ) :
    (middleToLocalization π m).range = middleChart π m := by
  apply le_antisymm
  · apply nodeLift_range_le (R := R) (S := middleLocalization π m)
        (c := π^m) (x := middleU π m) (y := middleV π m)
        (h := middle_relation π m) (T := middleChart π m)
    · exact Localization.Away.fraction_mem (centerIdeal π (m+2)) (middleDen π m)
          (PlaneNode.U (π^(m+2))) (Ideal.subset_span (Or.inl rfl))
    · exact Localization.Away.fraction_mem (centerIdeal π (m+2)) (middleDen π m)
          (PlaneNode.V (π^(m+2))) (Ideal.subset_span (Or.inr (Or.inl rfl)))
  · apply Localization.Away.saturatedChart_le (R := R) (A := node π (m+2))
    · intro z
      refine ⟨middleBase π m z, ?_⟩
      exact congrArg (fun f : node π (m+2) →ₐ[R] middleLocalization π m => f z)
        (middle_base_triangle π m)
    · intro b hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨PlaneNode.U (π^m), middleToLocalization_u π m⟩
      · exact ⟨PlaneNode.V (π^m), middleToLocalization_v π m⟩
      · rw [Localization.Away.fraction_self]; exact (middleToLocalization π m).range.one_mem

/-- The saturated middle Rees chart is the node with exponent lowered by two. -/
def middleReesEquiv [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) : node π m ≃ₐ[R] middleChart π m :=
  (AlgEquiv.ofInjective (middleToLocalization π m) (middleToLocalization_injective π hπ m)).trans
    (Subalgebra.equivOfEq _ _ (middle_range_eq π m))

@[simp] lemma middleReesEquiv_coe [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : node π m) :
    (middleReesEquiv π hπ m z : middleLocalization π m) = middleToLocalization π m z := rfl

lemma middleReesEquiv_base [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) (z : node π (m + 2)) :
    middleReesEquiv π hπ m (middleBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (middleDen π m)) z := by
  apply Subtype.ext
  exact congrArg (fun f : node π (m+2) →ₐ[R] middleLocalization π m => f z)
    (middle_base_triangle π m)

end PowerNode.Rees

end
end MiddleReesChart
