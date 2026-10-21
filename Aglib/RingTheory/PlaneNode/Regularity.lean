/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.MapInverse
public import Aglib.RingTheory.DiscreteValuationRing.UniformizerResidue
public import Aglib.RingTheory.RegularLocalRing.Localization
public import Aglib.RingTheory.Blowup.PowerNode.Charts
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.Regularity`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`07c33ab8a3a7219f5117bb99ad8a853507d20db7b06cc21ecf79db954b4bd1af`.
Pure Laurent comparison, closed-point prime chain, regularity and DVR flatness of the literal
  PlaneNode.Ring.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Localization and Laurent regularity, the closed node point and uniformizer-node regularity, with
  open-cover locality.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open Polynomial
open scoped Polynomial
universe u

section NodeLaurent


/-!
# Literal node principal opens

For the existing actual algebra `PlaneNode.Ring c = R[U,V]/(UV-c)`, construct mutually
inverse maps identifying D(U) with `R[X,1/X]`. The inverse sends X to U and uses
the literal relation V = c/U. The already-reviewed coordinate exchange gives
the D(V) result. Polynomial regularity and the general localization lemma then
prove regularity of both opens; unit thickness gives regularity of the full node.
No assumptions on c are needed for the Laurent comparison.

This is local algebra for TASKS.md E1, at K2-018#lem:k2018-cycle-cover,
revision e73d98b1b5c1e5abcdebf7d058e436d792b87982, lines 619–663.
It does not construct a proper regular model, resolution, or contraction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace PlaneNode.Regularity
open PlaneNode _root_.PowerNode.Rees
variable {R : Type u} [CommRing R]


/-- The `R`-algebra map from `R[U,V]/(UV-c)` to `R[X,1/X]` sending `U` to `X`
and `V` to `c/X`. -/
def nodeToLaurent (c : R) : PlaneNode.Ring c →ₐ[R] Localization.Away (Polynomial.X : R[X]) :=
  PlaneNode.lift c (algebraMap R[X] _ X)
    (algebraMap R _ c * IsLocalization.Away.invSelf (X : R[X])) (by
      rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one])

@[simp] lemma nodeToLaurent_u (c : R) :
    nodeToLaurent c (PlaneNode.U c) = algebraMap R[X] _ X := by simp [nodeToLaurent]
@[simp] lemma nodeToLaurent_v (c : R) :
    nodeToLaurent c (PlaneNode.V c) =
      algebraMap R _ c * IsLocalization.Away.invSelf (X : R[X]) := by simp [nodeToLaurent]

/-- The extension of `nodeToLaurent` to the localization where `U` is inverted,
with target `R[X,1/X]`. -/
def awayToLaurent (c : R) : Localization.Away (PlaneNode.U c) →ₐ[R] Localization.Away
  (Polynomial.X : R[X]) :=
  IsLocalization.Away.liftAlgHom (PlaneNode.U c) (f := nodeToLaurent c) (by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.X :
      R[X])) (X : R[X]))

@[simp] lemma awayToLaurent_base (c : R) (z : PlaneNode.Ring c) :
    awayToLaurent c (algebraMap (PlaneNode.Ring c) _ z) = nodeToLaurent c z := by
  simp [awayToLaurent]

/-- The `R`-algebra map from `R[X,1/X]` to the node ring localized at `U`,
sending `X` to `U`; it is inverse to `awayToLaurent`. -/
def laurentToAway (c : R) : Localization.Away (Polynomial.X : R[X]) →ₐ[R] Localization.Away
  (PlaneNode.U c) :=
  IsLocalization.Away.liftAlgHom (X : R[X])
    (f := aeval (algebraMap (PlaneNode.Ring c) (Localization.Away (PlaneNode.U c)) (PlaneNode.U
      c))) (by
      simpa using IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (PlaneNode.U c)) (PlaneNode.U c))

@[simp] lemma laurentToAway_X (c : R) :
    laurentToAway c (algebraMap R[X] (Localization.Away (Polynomial.X : R[X])) X) =
      algebraMap (PlaneNode.Ring c) _ (PlaneNode.U c) := by simp [laurentToAway]

lemma laurentToAway_inv (c : R) :
    laurentToAway c (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : R[X])) (X
      : R[X])) =
      IsLocalization.Away.invSelf (PlaneNode.U c) := by
  apply Localization.Away.map_invSelf_of_mul (Polynomial.X : R[X])
    (laurentToAway c).toRingHom
  change laurentToAway c (algebraMap R[X] (Localization.Away (Polynomial.X : R[X])) X) *
    IsLocalization.Away.invSelf (PlaneNode.U c) = 1
  rw [laurentToAway_X, IsLocalization.Away.mul_invSelf]

lemma node_away_v (c : R) :
    algebraMap (PlaneNode.Ring c) (Localization.Away (PlaneNode.U c)) (PlaneNode.V c) =
      algebraMap R _ c * IsLocalization.Away.invSelf (PlaneNode.U c) := by
  calc
    _ = (algebraMap (PlaneNode.Ring c) _ (PlaneNode.U c) * algebraMap (PlaneNode.Ring c) _
      (PlaneNode.V c)) *
        IsLocalization.Away.invSelf (PlaneNode.U c) := by
          rw [mul_right_comm, IsLocalization.Away.mul_invSelf, one_mul]
    _ = _ := by rw [← map_mul, PlaneNode.relation, ← IsScalarTower.algebraMap_apply R
      (PlaneNode.Ring c)]

/-- The literal node chart with U inverted is the Laurent polynomial algebra, for every c. -/
def nodeAwayLaurent (c : R) : Localization.Away (PlaneNode.U c) ≃ₐ[R] Localization.Away
  (Polynomial.X : R[X]) :=
  AlgEquiv.ofAlgHom (awayToLaurent c) (laurentToAway c)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (X : R[X]))
      apply Polynomial.algHom_ext
      change awayToLaurent c (laurentToAway c (algebraMap R[X] (Localization.Away (Polynomial.X :
        R[X])) X)) =
        algebraMap R[X] (Localization.Away (Polynomial.X : R[X])) X
      simp)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (PlaneNode.U c))
      apply PlaneNode.hom_ext
      · change laurentToAway c (awayToLaurent c (algebraMap (PlaneNode.Ring c) _ (PlaneNode.U c))) =
          algebraMap (PlaneNode.Ring c) _ (PlaneNode.U c)
        simp
      · change laurentToAway c (awayToLaurent c (algebraMap (PlaneNode.Ring c) _ (PlaneNode.V c))) =
          algebraMap (PlaneNode.Ring c) _ (PlaneNode.V c)
        simp only [awayToLaurent_base, nodeToLaurent_v, map_mul, AlgHom.commutes, laurentToAway_inv]
        exact (node_away_v c).symm)

lemma nodeAwayU_regular [IsRegularRing R] (c : R) :
    IsRegularRing (Localization.Away (PlaneNode.U c)) := by
  have := IsRegularRing.regular_localization R[X] (Localization.Away (Polynomial.X : R[X]))
    (Submonoid.powers (X : R[X]))
  exact IsRegularRing.of_ringEquiv (nodeAwayLaurent c).symm.toRingEquiv

lemma nodeAwayV_regular [IsRegularRing R] (c : R) :
    IsRegularRing (Localization.Away (PlaneNode.V c)) := by
  have := nodeAwayU_regular c
  exact IsRegularRing.of_ringEquiv (nodeSwapAway c).toRingEquiv

/-- A node with unit thickness is regular over any regular coefficient ring. -/
lemma unitNode_regular [IsRegularRing R] (c : R) (hc : IsUnit c) :
    IsRegularRing (PlaneNode.Ring c) := by
  have hU : IsUnit (PlaneNode.U c) := (IsUnit.mul_iff.mp (show IsUnit (PlaneNode.U c * PlaneNode.V
    c) by
    rw [PlaneNode.relation]
    exact hc.map (algebraMap R (PlaneNode.Ring c)))).1
  have := nodeAwayU_regular c
  apply isRegularRing_iff.mpr
  intro p hp
  apply IsRegularRing.regular_atPrime_of_away (PlaneNode.Ring c) (PlaneNode.U c) p
  intro hu
  exact hp.ne_top (p.eq_top_of_isUnit_mem hu hU)

end PlaneNode.Regularity

end
end NodeLaurent

section NodeClosedPoint


/-!
# The actual closed point of a uniformizer node

Over an arbitrary DVR with actual uniformizer π, evaluate the literal node
coordinates at (0,0) in the actual residue field. Prove that its kernel is exactly
(U,V), is maximal, and is the only prime containing both coordinates. Evaluation
at (0,X) in the residue polynomial ring yields a genuine intermediate prime:
(0) < ker(U ↦ 0, V ↦ X) < (U,V). The first strictness uses the constructed node
domain/coordinate injection; the second uses X ≠ 0. Thus the closed ideal has
height at least two. No assumed classification of node primes is used.

Local algebra for TASKS.md E1, K2-018#lem:k2018-cycle-cover,
e73d98b1b5c1e5abcdebf7d058e436d792b87982, lines 619–663.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsLocalRing
namespace PlaneNode.Regularity
open PlaneNode _root_.PowerNode.Rees
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]


/-- Evaluation of the uniformizer node at `U = V = 0` in the residue field of the DVR. -/
def closedPointMap (π : R) (hπ : Irreducible π) : PlaneNode.Ring π →ₐ[R] ResidueField R :=
  PlaneNode.lift π 0 0 (by simp [ResidueField.algebraMap_eq,
    IsDiscreteValuationRing.uniformizer_residue_zero π hπ])

/-- The `R`-algebra map from the uniformizer node to the residue polynomial ring,
sending `U` to zero and `V` to `X`. -/
def branchMap (π : R) (hπ : Irreducible π) : PlaneNode.Ring π →ₐ[R] (ResidueField R)[X] :=
  PlaneNode.lift π 0 X (by
    rw [zero_mul, IsScalarTower.algebraMap_apply R (ResidueField R),
      ResidueField.algebraMap_eq, IsDiscreteValuationRing.uniformizer_residue_zero π hπ, map_zero])

/-- The kernel of residue-field evaluation at `U = V = 0` in the uniformizer node ring. -/
def closedIdeal (π : R) (hπ : Irreducible π) : Ideal (PlaneNode.Ring π) :=
  RingHom.ker (closedPointMap π hπ).toRingHom

/-- The kernel of `U ↦ 0, V ↦ X` in the residue polynomial ring, defining a branch
prime below the closed-point ideal. -/
def branchIdeal (π : R) (hπ : Irreducible π) : Ideal (PlaneNode.Ring π) :=
  RingHom.ker (branchMap π hπ).toRingHom

lemma closedPointMap_surjective (π : R) (hπ : Irreducible π) :
    Function.Surjective (closedPointMap π hπ) := by
  intro a
  obtain ⟨r, hr⟩ := residue_surjective a
  refine ⟨algebraMap R (PlaneNode.Ring π) r, ?_⟩
  simpa only [AlgHom.commutes, ResidueField.algebraMap_eq] using hr

instance closedIdeal_isMaximal (π : R) (hπ : Irreducible π) :
    (closedIdeal π hπ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (closedPointMap_surjective π hπ)

instance branchIdeal_isPrime (π : R) (hπ : Irreducible π) :
    (branchIdeal π hπ).IsPrime := RingHom.ker_isPrime _

lemma nodeU_mem_closedIdeal (π : R) (hπ : Irreducible π) : PlaneNode.U π ∈ closedIdeal π hπ := by
  simp [closedIdeal, closedPointMap, RingHom.mem_ker]
lemma nodeV_mem_closedIdeal (π : R) (hπ : Irreducible π) : PlaneNode.V π ∈ closedIdeal π hπ := by
  simp [closedIdeal, closedPointMap, RingHom.mem_ker]
lemma nodeU_mem_branchIdeal (π : R) (hπ : Irreducible π) : PlaneNode.U π ∈ branchIdeal π hπ := by
  simp [branchIdeal, branchMap, RingHom.mem_ker]
lemma nodeV_not_mem_branchIdeal (π : R) (hπ : Irreducible π) : PlaneNode.V π ∉ branchIdeal π hπ :=
  by
  simp [branchIdeal, branchMap, RingHom.mem_ker]

lemma branchIdeal_le_closedIdeal (π : R) (hπ : Irreducible π) :
    branchIdeal π hπ ≤ closedIdeal π hπ := by
  have h : ((aeval (0 : ResidueField R)).restrictScalars R).comp (branchMap π hπ) =
      closedPointMap π hπ := by
    apply PlaneNode.hom_ext <;> simp [branchMap, closedPointMap]
  intro z hz
  change closedPointMap π hπ z = 0
  rw [← h, AlgHom.comp_apply]
  change branchMap π hπ z = 0 at hz
  rw [hz, map_zero]

/-- The ideal generated by the literal coordinates `U` and `V` in the node ring. -/
abbrev coordinateIdeal (π : R) : Ideal (PlaneNode.Ring π) := Ideal.span {PlaneNode.U π,
  PlaneNode.V π}

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma coordinateQuotient_u (π : R) :
    algebraMap (PlaneNode.Ring π) (PlaneNode.Ring π ⧸ coordinateIdeal π) (PlaneNode.U π) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma coordinateQuotient_v (π : R) :
    algebraMap (PlaneNode.Ring π) (PlaneNode.Ring π ⧸ coordinateIdeal π) (PlaneNode.V π) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma coordinateQuotient_pi (π : R) :
    algebraMap R (PlaneNode.Ring π ⧸ coordinateIdeal π) π = 0 := by
  rw [IsScalarTower.algebraMap_apply R (PlaneNode.Ring π), ← PlaneNode.relation, map_mul,
    coordinateQuotient_u, zero_mul]

/-- The `R`-algebra map from the residue field to the quotient of the uniformizer
node ring by `(U,V)`, induced by the scalar map; the relation `UV = π` kills `π`. -/
def residueToCoordinateQuotient (π : R) (hπ : Irreducible π) :
    ResidueField R →ₐ[R] PlaneNode.Ring π ⧸ coordinateIdeal π :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) (by
    intro r hr
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    obtain ⟨s, rfl⟩ := hr
    change algebraMap R _ (π * s) = 0
    rw [map_mul, coordinateQuotient_pi, zero_mul])

lemma residueToCoordinateQuotient_comp (π : R) (hπ : Irreducible π) :
    (residueToCoordinateQuotient π hπ).comp (closedPointMap π hπ) =
      Ideal.Quotient.mkₐ R (coordinateIdeal π) := by
  apply PlaneNode.hom_ext
  · change residueToCoordinateQuotient π hπ (closedPointMap π hπ (PlaneNode.U π)) =
      algebraMap (PlaneNode.Ring π) _ (PlaneNode.U π)
    simp only [closedPointMap, PlaneNode.lift_U, map_zero]
    exact (coordinateQuotient_u π).symm
  · change residueToCoordinateQuotient π hπ (closedPointMap π hπ (PlaneNode.V π)) =
      algebraMap (PlaneNode.Ring π) _ (PlaneNode.V π)
    simp only [closedPointMap, PlaneNode.lift_V, map_zero]
    exact (coordinateQuotient_v π).symm

/-- The actual closed point is generated by the two literal node coordinates. -/
lemma closedIdeal_eq_coordinateIdeal (π : R) (hπ : Irreducible π) :
    closedIdeal π hπ = coordinateIdeal π := by
  apply le_antisymm
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ R (coordinateIdeal π)) z = 0
    rw [← residueToCoordinateQuotient_comp π hπ, AlgHom.comp_apply]
    change closedPointMap π hπ z = 0 at hz
    rw [hz, map_zero]
  · apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact nodeU_mem_closedIdeal π hπ
    · exact nodeV_mem_closedIdeal π hπ

lemma prime_eq_closedIdeal_of_coordinates (π : R) (hπ : Irreducible π)
    (p : Ideal (PlaneNode.Ring π)) [p.IsPrime] (hu : PlaneNode.U π ∈ p) (hv : PlaneNode.V π ∈ p) :
    p = closedIdeal π hπ := by
  apply ((closedIdeal_isMaximal π hπ).eq_of_le (inferInstance : p.IsPrime).ne_top ?_).symm
  rw [closedIdeal_eq_coordinateIdeal]
  exact Ideal.span_le.mpr (by intro z hz; rcases hz with rfl | rfl <;> assumption)

/-- The actual prime chain (0) < ker(U ↦ 0,V ↦ X) < (U,V). -/
lemma node_prime_chain (π : R) (hπ : Irreducible π) :
    (⊥ : Ideal (PlaneNode.Ring π)) < branchIdeal π hπ ∧ branchIdeal π hπ < closedIdeal π hπ := by
  constructor
  · refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hu := nodeU_mem_branchIdeal π hπ
    rw [h, Ideal.mem_bot] at hu
    exact nodeU_ne_zero π hu
  · apply lt_of_le_of_ne (branchIdeal_le_closedIdeal π hπ)
    intro h
    exact nodeV_not_mem_branchIdeal π hπ (h.symm ▸ nodeV_mem_closedIdeal π hπ)

lemma closedIdeal_height_ge_two (π : R) (hπ : Irreducible π) :
    2 ≤ (closedIdeal π hπ).height := by
  have := node_isDomain π hπ.ne_zero
  obtain ⟨h0, h1⟩ := node_prime_chain π hπ
  have hbot := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have hbranch := Ideal.height_add_one_le_of_lt_of_isPrime h1
  rw [Ideal.height_bot, zero_add] at hbot
  calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (branchIdeal π hπ).height + 1 := by simpa [add_comm] using add_le_add_right hbot 1
    _ ≤ (closedIdeal π hπ).height := hbranch

end PlaneNode.Regularity

end
end NodeClosedPoint

section UniformizerNodeRegularity


/-!
# Regularity of the literal uniformizer node

Prove `IsRegularRing (PlaneNode.Ring π)` over every DVR when π is an actual uniformizer
(`Irreducible π`). At the unique double-coordinate prime, the maximal ideal of
the localization has two generators and dimension at least two, so the pinned
regular-local-ring criterion applies. Every other prime lies in D(U) or D(V),
whose actual Laurent comparison supplies regularity. Transport to the literal
Spec stalks is explicit. Also prove full DVR flatness for every nonzero thickness,
and regularity after scaling a uniformizer by a unit.

There is no regularity, blowup, resolution, or local-model existence premise.
This is the local regular-chart obligation for TASKS.md E1,
K2-018#lem:k2018-cycle-cover, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, lines 619–663.
Global chart gluing, properness and a complete regular resolution remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsLocalRing
namespace PlaneNode.Regularity
open PlaneNode _root_.PowerNode.Rees
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The local ring of the actual double-coordinate point is regular. -/
lemma uniformizerNode_closed_regular (π : R) (hπ : Irreducible π) :
    IsRegularLocalRing (Localization.AtPrime (closedIdeal π hπ)) := by
  let A := Localization.AtPrime (closedIdeal π hπ)
  have hm : maximalIdeal A = Ideal.span
      {algebraMap (PlaneNode.Ring π) A (PlaneNode.U π), algebraMap (PlaneNode.Ring π) A
        (PlaneNode.V π)} := by
    calc
      _ = (closedIdeal π hπ).map (algebraMap (PlaneNode.Ring π) A) :=
        (Localization.AtPrime.map_eq_maximalIdeal).symm
      _ = (coordinateIdeal π).map (algebraMap (PlaneNode.Ring π) A) :=
        congrArg (Ideal.map (algebraMap (PlaneNode.Ring π) A)) (closedIdeal_eq_coordinateIdeal π hπ)
      _ = _ := by rw [Ideal.map_span, Set.image_pair]
  have hspan : (maximalIdeal A).spanFinrank ≤ 2 := by
    rw [hm]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      (by simpa using (Set.ncard_insert_le (algebraMap (PlaneNode.Ring π) A (PlaneNode.U π))
          {algebraMap (PlaneNode.Ring π) A (PlaneNode.V π)}))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal A).spanFinrank : WithBot ℕ∞) ≤ 2 := by exact_mod_cast hspan
    _ ≤ ringKrullDim A := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height (closedIdeal π hπ)]
      exact WithBot.coe_le_coe.mpr (closedIdeal_height_ge_two π hπ)

/-- The literal surface UV = π is regular over an arbitrary DVR with actual uniformizer π.
No node-regularity or resolution theorem is supplied as a premise. -/
lemma uniformizerNode_regular (π : R) (hπ : Irreducible π) : IsRegularRing (PlaneNode.Ring π) := by
  apply isRegularRing_iff.mpr
  intro p hp
  by_cases hu : PlaneNode.U π ∈ p
  · by_cases hv : PlaneNode.V π ∈ p
    · have heq := prime_eq_closedIdeal_of_coordinates π hπ p hu hv
      subst p
      exact uniformizerNode_closed_regular π hπ
    · have := nodeAwayV_regular π
      exact IsRegularRing.regular_atPrime_of_away (PlaneNode.Ring π) (PlaneNode.V π) p hv
  · have := nodeAwayU_regular π
    exact IsRegularRing.regular_atPrime_of_away (PlaneNode.Ring π) (PlaneNode.U π) p hu

/-- Every nonzero-thickness DVR node is flat over the original DVR. -/
lemma dvrNode_flat (c : R) (hc : c ≠ 0) : Module.Flat R (PlaneNode.Ring c) := by
  have := node_isDomain c hc
  let : Module.IsTorsionFree R (PlaneNode.Ring c) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (node_algebraMap_injective c)
  infer_instance

/-- Actual regular scheme stalks are preserved by scaling the thickness by a unit. -/
lemma unitUniformizerNode_regular (π : R) (hπ : Irreducible π) (a : Rˣ) :
    IsRegularRing (PlaneNode.Ring ((a : R) * π)) := by
  have := uniformizerNode_regular π hπ
  exact IsRegularRing.of_ringEquiv (PlaneNode.unitScale π a).symm.toRingEquiv

end PlaneNode.Regularity

end
end UniformizerNodeRegularity
