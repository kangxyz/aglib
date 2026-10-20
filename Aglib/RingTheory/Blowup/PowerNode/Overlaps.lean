/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.PowerNode.Charts
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
Source: `R5Lab.AlgebraicGeometry.Curves.LocalModels.PointedResolution.Rees.Overlaps`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`2549fb39022285c671b306266bf93a76dde8e3967c40fcdd8ba883afee1248fb`.
The actual localization subalgebras, maps and original domain/UFD/nonzero-scalar
conditions are retained. These algebraic calculations do not supply a global
blowup or a geometric atlas. This leaf has no scheme-level dependency.
-/

@[expose] public section

/-!
# Pairwise and triple transitions of the power-node Rees charts, including the outer overlap and
DVR specializations.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open Polynomial
open scoped Polynomial
universe u

section NodeOverlaps


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

lemma node_awayU_v (c : R) :
    algebraMap (PlaneNode.Ring c) (Localization.Away (PlaneNode.U c)) (PlaneNode.V c) =
      algebraMap R _ c * IsLocalization.Away.invSelf (PlaneNode.U c) := by
  calc
    _ = (algebraMap (PlaneNode.Ring c) _ (PlaneNode.U c) * algebraMap (PlaneNode.Ring c) _
      (PlaneNode.V c)) *
        IsLocalization.Away.invSelf (PlaneNode.U c) := by
          rw [mul_right_comm, IsLocalization.Away.mul_invSelf, one_mul]
    _ = _ := by rw [← map_mul, PlaneNode.relation, ← IsScalarTower.algebraMap_apply R
      (PlaneNode.Ring c)]
lemma node_awayV_u (c : R) :
    algebraMap (PlaneNode.Ring c) (Localization.Away (PlaneNode.V c)) (PlaneNode.U c) =
      algebraMap R _ c * IsLocalization.Away.invSelf (PlaneNode.V c) := by
  have h := congrArg (swapAwayUV c) (node_awayU_v c)
  simpa [swapAwayUV_inverse] using h

abbrev leftOverlap (π : R) := Localization.Away (PlaneNode.V π)
abbrev middleLeftOverlap (π : R) (m : ℕ) := Localization.Away (PlaneNode.U (π^m))

def leftOverlapBase (π : R) (m : ℕ) : PlaneNode.Ring π →ₐ[R] middleLeftOverlap π m :=
  PlaneNode.lift π (algebraMap R _ π * algebraMap (node π m) _ (PlaneNode.U (π^m)))
    (IsLocalization.Away.invSelf (PlaneNode.U (π^m))) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one])

def middleLeftOverlapBase (π : R) (m : ℕ) : node π m →ₐ[R] leftOverlap π :=
  PlaneNode.lift (π^m) (IsLocalization.Away.invSelf (PlaneNode.V π))
    (algebraMap R _ (π^m) * algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (PlaneNode.V π)),
        IsLocalization.Away.mul_invSelf, mul_one])

def leftOverlapForward (π : R) (m : ℕ) : leftOverlap π →ₐ[R] middleLeftOverlap π m :=
  IsLocalization.Away.liftAlgHom (PlaneNode.V π) (f := leftOverlapBase π m) (by
    simp only [leftOverlapBase, PlaneNode.lift_V]
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap (node π m) _ (PlaneNode.U (π^m)),
      by rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩)
def leftOverlapReverse (π : R) (m : ℕ) : middleLeftOverlap π m →ₐ[R] leftOverlap π :=
  IsLocalization.Away.liftAlgHom (PlaneNode.U (π^m)) (f := middleLeftOverlapBase π m) (by
    simp only [middleLeftOverlapBase, PlaneNode.lift_U]
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π),
      by rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩)

@[simp] lemma leftOverlapForward_base (π : R) (m : ℕ) (z : PlaneNode.Ring π) :
    leftOverlapForward π m (algebraMap (PlaneNode.Ring π) _ z) = leftOverlapBase π m z := by
  simp [leftOverlapForward]
@[simp] lemma leftOverlapReverse_base (π : R) (m : ℕ) (z : node π m) :
    leftOverlapReverse π m (algebraMap (node π m) _ z) = middleLeftOverlapBase π m z := by
  simp [leftOverlapReverse]

lemma leftOverlapForward_inverse (π : R) (m : ℕ) :
    leftOverlapForward π m (IsLocalization.Away.invSelf (S := leftOverlap π) (PlaneNode.V π)) =
      algebraMap (node π m) _ (PlaneNode.U (π^m)) := by
  apply Localization.Away.map_invSelf_of_mul
  change leftOverlapForward π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) *
    algebraMap (node π m) _ (PlaneNode.U (π^m)) = 1
  simp only [leftOverlapForward_base, leftOverlapBase, PlaneNode.lift_V]
  rw [mul_comm, IsLocalization.Away.mul_invSelf]
lemma leftOverlapReverse_inverse (π : R) (m : ℕ) :
    leftOverlapReverse π m
      (IsLocalization.Away.invSelf (S := middleLeftOverlap π m) (PlaneNode.U (π^m))) =
      algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π) := by
  apply Localization.Away.map_invSelf_of_mul
  change leftOverlapReverse π m (algebraMap (node π m) _ (PlaneNode.U (π^m))) *
    algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π) = 1
  simp only [leftOverlapReverse_base, middleLeftOverlapBase, PlaneNode.lift_U]
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- The actual overlap D(p) = D(s), with s = p⁻¹ and t = pi^m p. -/
def leftMiddleEquiv (π : R) (m : ℕ) : leftOverlap π ≃ₐ[R] middleLeftOverlap π m :=
  AlgEquiv.ofAlgHom (leftOverlapForward π m) (leftOverlapReverse π m)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (PlaneNode.U (π^m)))
      apply PlaneNode.hom_ext
      · simp [middleLeftOverlapBase, leftOverlapForward_inverse, Algebra.algHom]
      · simpa [middleLeftOverlapBase, leftOverlapBase, Algebra.algHom] using (node_awayU_v
        (π^m)).symm)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (PlaneNode.V π))
      apply PlaneNode.hom_ext
      · simpa [middleLeftOverlapBase, leftOverlapBase, Algebra.algHom] using (node_awayV_u π).symm
      · simp [leftOverlapBase, leftOverlapReverse_inverse, Algebra.algHom])

lemma leftMiddle_base_triangle (π : R) (m : ℕ) :
    (leftOverlapForward π m).comp
        ((IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)).comp (leftBase π m)) =
      (IsScalarTower.toAlgHom R (node π m) (middleLeftOverlap π m)).comp (middleBase π m) := by
  apply PlaneNode.hom_ext
  · simp [leftBase, middleBase, leftOverlapBase, ← IsScalarTower.algebraMap_apply R (node π m)]
  · simp only [AlgHom.comp_apply, leftBase, middleBase, PlaneNode.lift_V,
      IsScalarTower.toAlgHom_apply, map_mul, AlgHom.commutes, leftOverlapForward_base]
    simp only [leftOverlapBase, PlaneNode.lift_V]
    rw [node_awayU_v]
    have hp : algebraMap R (middleLeftOverlap π m) (π^(m+1)) =
        algebraMap R _ (π^m) * algebraMap R _ π := by
      simpa only [map_mul] using congrArg (algebraMap R (middleLeftOverlap π m)) (pow_succ π m)
    rw [hp]
    ring

/-- The other outer/middle overlap is obtained by the literal node-coordinate exchange. -/
def rightMiddleEquiv (π : R) (m : ℕ) :
    leftOverlap π ≃ₐ[R] Localization.Away (PlaneNode.V (π^m)) :=
  (leftMiddleEquiv π m).trans (nodeSwapAway (π^m))


@[simp] lemma leftMiddleEquiv_u (π : R) (m : ℕ) :
    leftMiddleEquiv π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π)) =
      algebraMap R _ π * algebraMap (node π m) _ (PlaneNode.U (π^m)) := by
  change leftOverlapForward π m _ = _
  simp [leftOverlapBase]
@[simp] lemma leftMiddleEquiv_p (π : R) (m : ℕ) :
    leftMiddleEquiv π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) =
      IsLocalization.Away.invSelf (PlaneNode.U (π^m)) := by
  change leftOverlapForward π m _ = _
  simp [leftOverlapBase]
@[simp] lemma leftMiddleEquiv_symm_s (π : R) (m : ℕ) :
    (leftMiddleEquiv π m).symm (algebraMap (node π m) _ (PlaneNode.U (π^m))) =
      IsLocalization.Away.invSelf (PlaneNode.V π) := by
  change leftOverlapReverse π m _ = _
  simp [middleLeftOverlapBase]
@[simp] lemma leftMiddleEquiv_symm_t (π : R) (m : ℕ) :
    (leftMiddleEquiv π m).symm (algebraMap (node π m) _ (PlaneNode.V (π^m))) =
      algebraMap R _ (π^m) * algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π) := by
  change leftOverlapReverse π m _ = _
  simp [middleLeftOverlapBase]

@[simp] lemma rightMiddleEquiv_v (π : R) (m : ℕ) :
    rightMiddleEquiv π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π)) =
      algebraMap R _ π * algebraMap (node π m) _ (PlaneNode.V (π^m)) := by
  change swapAwayUV (π^m) (leftMiddleEquiv π m _) = _
  simp
@[simp] lemma rightMiddleEquiv_q (π : R) (m : ℕ) :
    rightMiddleEquiv π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) =
      IsLocalization.Away.invSelf (PlaneNode.V (π^m)) := by
  change swapAwayUV (π^m) (leftMiddleEquiv π m _) = _
  simp [swapAwayUV_inverse]

lemma rightMiddle_base_triangle (π : R) (m : ℕ) :
    (rightMiddleEquiv π m).toAlgHom.comp
        ((IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)).comp (rightBase π m)) =
      (IsScalarTower.toAlgHom R (node π m) (Localization.Away (PlaneNode.V (π^m)))).comp
        (middleBase π m) := by
  apply PlaneNode.hom_ext
  · simp only [AlgHom.comp_apply, rightBase_u, map_mul, AlgHom.commutes,
      AlgEquiv.toAlgHom_apply, IsScalarTower.toAlgHom_apply, rightMiddleEquiv_q, middleBase,
        PlaneNode.lift_U]
    rw [node_awayV_u]
    have hp : algebraMap R (Localization.Away (PlaneNode.V (π^m))) (π^(m+1)) =
        algebraMap R _ (π^m) * algebraMap R _ π := by
      simpa only [map_mul] using congrArg
        (algebraMap R (Localization.Away (PlaneNode.V (π^m)))) (pow_succ π m)
    rw [hp]
    ring
  · simp [middleBase, ← IsScalarTower.algebraMap_apply R (node π m)]

end PowerNode.Rees

end
end NodeOverlaps

section OuterOverlap


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PowerNode.Rees
variable {R : Type u} [CommRing R]

/-- v/u on the outer u-chart, or u/v on the identically presented v-chart. -/
def outerRatio (π : R) (m : ℕ) : PlaneNode.Ring π := algebraMap R _ (π^m) * PlaneNode.V π ^ 2
abbrev outerOverlap (π : R) (m : ℕ) := Localization.Away (outerRatio π m)
abbrev outerInv (π : R) (m : ℕ) : outerOverlap π m :=
  IsLocalization.Away.invSelf (outerRatio π m)
abbrev outerP (π : R) (m : ℕ) : outerOverlap π m :=
  algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)
abbrev outerQ (π : R) (m : ℕ) : outerOverlap π m := outerP π m * outerInv π m

lemma outerRatio_image (π : R) (m : ℕ) :
    algebraMap (PlaneNode.Ring π) (outerOverlap π m) (outerRatio π m) =
      algebraMap R _ (π^m) * outerP π m ^ 2 := by
  simp [outerRatio, ← IsScalarTower.algebraMap_apply R (PlaneNode.Ring π)]

lemma outer_inverse_relation (π : R) (m : ℕ) :
    algebraMap R (outerOverlap π m) (π^m) * outerP π m ^ 2 * outerInv π m = 1 := by
  rw [← outerRatio_image]
  exact IsLocalization.Away.mul_invSelf (outerRatio π m)

lemma outer_parameter_relation (π : R) (m : ℕ) :
    (algebraMap R (outerOverlap π m) (π^(m+1)) * outerP π m) * outerQ π m =
      algebraMap R _ π := by
  have hp : algebraMap R (outerOverlap π m) (π^(m+1)) =
      algebraMap R _ (π^m) * algebraMap R _ π := by
    simpa only [map_mul] using congrArg (algebraMap R (outerOverlap π m)) (pow_succ π m)
  rw [hp]
  calc
    _ = algebraMap R _ π *
      (algebraMap R _ (π^m) * outerP π m ^ 2 * outerInv π m) := by ring
    _ = _ := by rw [outer_inverse_relation, mul_one]

def outerTransitionBase (π : R) (m : ℕ) : PlaneNode.Ring π →ₐ[R] outerOverlap π m :=
  PlaneNode.lift π (algebraMap R _ (π^(m+1)) * outerP π m)
    (outerQ π m) (outer_parameter_relation π m)

lemma outerTransitionBase_ratio (π : R) (m : ℕ) :
    outerTransitionBase π m (outerRatio π m) = outerInv π m := by
  simp only [outerRatio, map_mul, AlgHom.commutes, map_pow, outerTransitionBase, PlaneNode.lift_V]
  calc
    _ = (algebraMap R _ (π^m) * outerP π m ^ 2 * outerInv π m) * outerInv π m := by
      simp only [map_pow]
      ring
    _ = _ := by rw [outer_inverse_relation, one_mul]

def outerTransition (π : R) (m : ℕ) : outerOverlap π m →ₐ[R] outerOverlap π m :=
  IsLocalization.Away.liftAlgHom (outerRatio π m) (f := outerTransitionBase π m) (by
    rw [outerTransitionBase_ratio]
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap (PlaneNode.Ring π) _ (outerRatio π m),
      by rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩)

@[simp] lemma outerTransition_base (π : R) (m : ℕ) (z : PlaneNode.Ring π) :
    outerTransition π m (algebraMap (PlaneNode.Ring π) _ z) = outerTransitionBase π m z := by
  simp [outerTransition]
lemma outerTransition_inverse (π : R) (m : ℕ) :
    outerTransition π m (outerInv π m) = algebraMap (PlaneNode.Ring π) _ (outerRatio π m) := by
  apply Localization.Away.map_invSelf_of_mul
  change outerTransition π m (algebraMap (PlaneNode.Ring π) _ (outerRatio π m)) *
    algebraMap (PlaneNode.Ring π) _ (outerRatio π m) = 1
  rw [outerTransition_base, outerTransitionBase_ratio, mul_comm, IsLocalization.Away.mul_invSelf]

lemma outer_original_u (π : R) (m : ℕ) :
    algebraMap (PlaneNode.Ring π) (outerOverlap π m) (PlaneNode.U π) =
      algebraMap R _ (π^(m+1)) * outerQ π m := by
  have hp : algebraMap R (outerOverlap π m) (π^(m+1)) =
      algebraMap R _ (π^m) * algebraMap R _ π := by
    simpa only [map_mul] using congrArg (algebraMap R (outerOverlap π m)) (pow_succ π m)
  have hn : algebraMap (PlaneNode.Ring π) (outerOverlap π m) (PlaneNode.U π) * outerP π m =
      algebraMap R _ π := by
    rw [← map_mul, PlaneNode.relation, ← IsScalarTower.algebraMap_apply R (PlaneNode.Ring π)]
  calc
    _ = algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π) *
      (algebraMap R _ (π^m) * outerP π m ^ 2 * outerInv π m) := by
        rw [outer_inverse_relation, mul_one]
    _ = algebraMap R _ (π^m) *
      (algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π) * outerP π m) * outerQ π m := by ring
    _ = _ := by rw [hn, hp]

@[simp] lemma outerTransition_p (π : R) (m : ℕ) :
    outerTransition π m (outerP π m) = outerQ π m := by
  change outerTransition π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) = _
  simp [outerTransitionBase]
@[simp] lemma outerTransition_q (π : R) (m : ℕ) :
    outerTransition π m (outerQ π m) = outerP π m := by
  simp only [outerQ, map_mul, outerTransition_p, outerTransition_inverse]
  rw [mul_assoc, mul_comm (outerInv π m), IsLocalization.Away.mul_invSelf, mul_one]

/-- Literal u/v-chart transition; the two copies have variables (u,p) and (v,q). -/
def outerOverlapEquiv (π : R) (m : ℕ) : outerOverlap π m ≃ₐ[R] outerOverlap π m :=
  AlgEquiv.ofAlgHom (outerTransition π m) (outerTransition π m)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (outerRatio π m))
      apply PlaneNode.hom_ext
      · change outerTransition π m
          (outerTransition π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π))) =
            algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π)
        rw [outerTransition_base]
        simp only [outerTransitionBase, PlaneNode.lift_U, map_mul, AlgHom.commutes,
          outerTransition_p]
        exact (outer_original_u π m).symm
      · change outerTransition π m (outerTransition π m (outerP π m)) = outerP π m
        rw [outerTransition_p, outerTransition_q])
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (outerRatio π m))
      apply PlaneNode.hom_ext
      · change outerTransition π m
          (outerTransition π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π))) =
            algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π)
        rw [outerTransition_base]
        simp only [outerTransitionBase, PlaneNode.lift_U, map_mul, AlgHom.commutes,
          outerTransition_p]
        exact (outer_original_u π m).symm
      · change outerTransition π m (outerTransition π m (outerP π m)) = outerP π m
        rw [outerTransition_p, outerTransition_q])

lemma outer_pq_relation (π : R) (m : ℕ) :
    algebraMap R (outerOverlap π m) (π^m) * outerP π m * outerQ π m = 1 := by
  calc
    _ = algebraMap R _ (π^m) * outerP π m ^ 2 * outerInv π m := by ring
    _ = 1 := outer_inverse_relation π m

/-- The outer overlap lies in D(p), hence in the middle chart. -/
lemma outer_p_isUnit (π : R) (m : ℕ) : IsUnit (outerP π m) := by
  apply IsLocalization.Away.isUnit_of_dvd (x := outerRatio π m)
  refine ⟨algebraMap R _ (π^m) * PlaneNode.V π, ?_⟩
  dsimp [outerRatio]
  ring

def outerOverlapFromLeftMiddle (π : R) (m : ℕ) : leftOverlap π →ₐ[R] outerOverlap π m :=
  IsLocalization.Away.liftAlgHom (PlaneNode.V π)
    (f := IsScalarTower.toAlgHom R (PlaneNode.Ring π) _) (outer_p_isUnit π m)

lemma outer_base_triangle (π : R) (m : ℕ) :
    (outerTransition π m).comp
        ((IsScalarTower.toAlgHom R (PlaneNode.Ring π) (outerOverlap π m)).comp (leftBase π m)) =
      (IsScalarTower.toAlgHom R (PlaneNode.Ring π) (outerOverlap π m)).comp (rightBase π m) := by
  apply PlaneNode.hom_ext
  · simp [leftBase, outerTransitionBase, ← IsScalarTower.algebraMap_apply R (PlaneNode.Ring π)]
  · simp only [AlgHom.comp_apply, leftBase, PlaneNode.lift_V, Algebra.algHom_apply,
      map_mul, AlgHom.commutes, outerTransition_base, outerTransitionBase, rightBase_v]
    exact (outer_original_u π m).symm


/-- The middle coordinates on the actual outer/outer intersection. -/
def middleToOuterOverlap (π : R) (m : ℕ) : node π m →ₐ[R] outerOverlap π m :=
  PlaneNode.lift (π^m) (algebraMap R _ (π^m) * outerQ π m)
    (algebraMap R _ (π^m) * outerP π m) (by
      calc
        _ = algebraMap R _ (π^m) *
          (algebraMap R _ (π^m) * outerP π m * outerQ π m) := by ring
        _ = _ := by rw [outer_pq_relation, mul_one])

@[simp] lemma outerOverlapFromLeftMiddle_base (π : R) (m : ℕ) (z : PlaneNode.Ring π) :
    outerOverlapFromLeftMiddle π m (algebraMap (PlaneNode.Ring π) _ z) =
      algebraMap (PlaneNode.Ring π) _ z := by simp [outerOverlapFromLeftMiddle]

lemma outerOverlapFromLeftMiddle_inverse (π : R) (m : ℕ) :
    outerOverlapFromLeftMiddle π m
      (IsLocalization.Away.invSelf (S := leftOverlap π) (PlaneNode.V π)) =
      algebraMap R _ (π^m) * outerQ π m := by
  apply Localization.Away.map_invSelf_of_mul
  change outerOverlapFromLeftMiddle π m (algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)) *
    (algebraMap R _ (π^m) * outerQ π m) = 1
  rw [outerOverlapFromLeftMiddle_base]
  change outerP π m * (algebraMap R _ (π^m) * outerQ π m) = 1
  rw [← mul_assoc, mul_comm (outerP π m)]
  exact outer_pq_relation π m

/-- The left/middle transition restricts to the displayed middle chart on the outer intersection. -/
lemma outer_middle_restriction (π : R) (m : ℕ) :
    (outerOverlapFromLeftMiddle π m).comp (middleLeftOverlapBase π m) =
      middleToOuterOverlap π m := by
  apply PlaneNode.hom_ext <;>
    simp [middleLeftOverlapBase, middleToOuterOverlap, outerOverlapFromLeftMiddle_inverse]

/-- The two paths through the actual triple overlap agree, including their middle coordinates. -/
lemma outer_triple_triangle (π : R) (m : ℕ) :
    (outerTransition π m).comp (middleToOuterOverlap π m) =
      (middleToOuterOverlap π m).comp (nodeSwap (π^m)) := by
  apply PlaneNode.hom_ext <;> simp [middleToOuterOverlap, outerTransitionBase]

end PowerNode.Rees

end
end OuterOverlap

section DvrPowerNode.Rees


/-!
Literal saturated Rees charts of R[u,v]/(uv - pi^(m+2)) at (u,v,pi).
There are no retained theorem families in this construction. The DVR hypotheses
are used only through domain and unique factorization; the algebraic charts work
for any UFD and nonzero pi. No smoothness, regularity, minimality, resolution,
component count, or discriminant assertion is included.
-/
noncomputable section
namespace PowerNode.Rees
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual u-chart for an arbitrary DVR and its given uniformizer. -/
def dvrLeftReesEquiv (π : R) (hπ : Irreducible π) (m : ℕ) :
    PlaneNode.Ring π ≃ₐ[R] leftChart π m := leftReesEquiv π hπ.ne_zero m
/-- The actual pi-chart, including m = 0 where the relation is st = 1. -/
def dvrMiddleReesEquiv (π : R) (hπ : Irreducible π) (m : ℕ) :
    node π m ≃ₐ[R] middleChart π m := middleReesEquiv π hπ.ne_zero m
/-- The actual v-chart for an arbitrary DVR and its given uniformizer. -/
def dvrRightReesEquiv (π : R) (hπ : Irreducible π) (m : ℕ) :
    PlaneNode.Ring π ≃ₐ[R] rightChart π m := rightReesEquiv π hπ.ne_zero m

lemma dvrLeftReesEquiv_base (π : R) (hπ : Irreducible π) (m : ℕ)
    (z : node π (m + 2)) : dvrLeftReesEquiv π hπ m (leftBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (PlaneNode.U (π^(m+2)))) z := leftReesEquiv_base π hπ.ne_zero m z
lemma dvrMiddleReesEquiv_base (π : R) (hπ : Irreducible π) (m : ℕ)
    (z : node π (m + 2)) : dvrMiddleReesEquiv π hπ m (middleBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (middleDen π m)) z := middleReesEquiv_base π hπ.ne_zero m z
lemma dvrRightReesEquiv_base (π : R) (hπ : Irreducible π) (m : ℕ)
    (z : node π (m + 2)) : dvrRightReesEquiv π hπ m (rightBase π m z) =
      algebraMap (node π (m+2)) (Localization.Away.saturatedChart (node π (m+2))
        (centerIdeal π (m+2)) (PlaneNode.V (π^(m+2)))) z := rightReesEquiv_base π hπ.ne_zero m z

end PowerNode.Rees

end
end DvrPowerNode.Rees
