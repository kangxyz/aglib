/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc.Iteration
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing
public import Aglib.RingTheory.AdicCompletion.CompleteParameterMap
public import Aglib.RingTheory.AdicCompletion.NormalSurface
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne
public import Aglib.RingTheory.LocalRing.DirectedUnion
public import Aglib.RingTheory.Nagata.FiniteTypeSurface

/-!
# Formal arcs on the same original marked point-blowup path

The input is the given ordinary point-blowup path. Its actual local-ring maps
and original generic-point comparisons put its stalks in the same function
field. Their ranges form the native domination chain used by `DirectedUnion`.
The literal principal completion gives the compatible original path maps and
the actual surjection from the starting-stalk completion. No arc, completion
quotient or desired terminating chain is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Blowup.Arc

/-- The actual target-point stalk map of the original scheme morphism. -/
def pointLocalRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (pointStalkIso Y h).inv ≫ f.stalkMap x

instance pointLocalRingMap_isLocal {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    IsLocalHom (pointLocalRingMap f x y h).hom :=
  RingHom.isLocalHom_comp (f.stalkMap x).hom (pointStalkIso Y h).inv.hom

/-- The canonical original map from an integral scheme stalk to its function field. -/
def stalkToFunctionField (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.presheaf.stalk x ⟶ X.functionField :=
  X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)

theorem stalkToFunctionField_hom (X : Scheme.{u}) [IsIntegral X] (x : X) :
    (stalkToFunctionField X x).hom = algebraMap (X.presheaf.stalk x) X.functionField := rfl

theorem stalkToFunctionField_injective (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Function.Injective (stalkToFunctionField X x).hom :=
  IsFractionRing.injective (X.presheaf.stalk x) X.functionField

/-- Naturality uses the original generic-point and selected-point stalk arrows. -/
theorem stalkMap_functionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) :
    f.stalkMap x ≫ stalkToFunctionField X x =
      stalkToFunctionField Y (f x) ≫ CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  let hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let hy : genericPoint Y ⤳ f x := (genericPoint_spec Y).specializes trivial
  let he : f (genericPoint X) ⤳ genericPoint Y :=
    specializes_of_eq (Scheme.map_genericPoint_of_isDominant X f)
  change f.stalkMap x ≫ X.presheaf.stalkSpecializes hx =
    Y.presheaf.stalkSpecializes hy ≫
      (Y.presheaf.stalkSpecializes he ≫ f.stalkMap (genericPoint X))
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact (f.stalkSpecializes_stalkMap (genericPoint X) x hx).symm

/-- The same naturality square with the original specified target point retained. -/
theorem pointLocalRingMap_functionField {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (x : X) (y : Y) (h : f x = y) :
    pointLocalRingMap f x y h ≫ stalkToFunctionField X x =
      stalkToFunctionField Y y ≫ CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  subst y
  have hid : (pointStalkIso Y (rfl : f x = f x)).inv =
      𝟙 (Y.presheaf.stalk (f x)) := by
    change Y.presheaf.stalkSpecializes (specializes_refl (f x)) = _
    exact TopCat.Presheaf.stalkSpecializes_refl Y.presheaf (f x)
  simpa only [pointLocalRingMap, hid, Category.id_comp] using stalkMap_functionField f x

/-- The actual point-stalk map gives the original scheme factorization. -/
theorem pointLocalRingMap_fromSpecStalk {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Spec.map (pointLocalRingMap f x y h) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst y
  have hid : (pointStalkIso Y (rfl : f x = f x)).inv =
      𝟙 (Y.presheaf.stalk (f x)) := by
    change Y.presheaf.stalkSpecializes (specializes_refl (f x)) = _
    exact TopCat.Presheaf.stalkSpecializes_refl Y.presheaf (f x)
  rw [pointLocalRingMap, hid, Category.id_comp]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

/-- An already given ordinary closed-point path. Its universal properties
concern the literal original schemes and arrows, without an arc as input. -/
structure ClosedPointBlowupPath where
  /-- The original schemes in the given path. -/
  scheme : ℕ → Scheme.{u}
  /-- The selected original point at each stage. -/
  point : (n : ℕ) → scheme n
  /-- The original ordinary point blowdowns. -/
  down : (n : ℕ) → scheme (n + 1) ⟶ scheme n
  point_closed : ∀ n, IsClosed ({point n} : Set (scheme n))
  point_down : ∀ n, down n (point (n + 1)) = point n
  noetherian_zero : IsLocallyNoetherian (scheme 0)
  integral_zero : IsIntegral (scheme 0)
  nongeneric_zero : let _ : IsIntegral (scheme 0) := integral_zero
    point 0 ≠ genericPoint (scheme 0)
  cartier : ∀ n,
    cartierPullback ((scheme n).fromSpecResidueField (point n)).ker (down n)
  universal : ∀ n (T : Scheme.{u}) (f : T ⟶ scheme n),
    cartierPullback ((scheme n).fromSpecResidueField (point n)).ker f →
      ∃! g : T ⟶ scheme (n + 1), g ≫ down n = f

namespace ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- Each given step is an actual ordinary universal point blowup on its original scheme. -/
def datum (n : ℕ) : BlowupDatum ((P.scheme n).fromSpecResidueField (P.point n)).ker where
  Y := P.scheme (n + 1)
  map := P.down n
  cartier := P.cartier n
  universal := P.universal n

private structure IntegralStage (n : ℕ) : Prop where
  integral : IsIntegral (P.scheme n)
  nongeneric : let _ : IsIntegral (P.scheme n) := integral
    P.point n ≠ genericPoint (P.scheme n)

private theorem integralStage (n : ℕ) : IntegralStage P n := by
  induction n with
  | zero => exact ⟨P.integral_zero, P.nongeneric_zero⟩
  | succ n ih =>
    let : IsIntegral (P.scheme n) := ih.integral
    have hn : P.point n ≠ genericPoint (P.scheme n) := ih.nongeneric
    have hcentre := genericPoint_not_mem_pointCentre (P.point n) (P.point_closed n) hn
    have hnext : IsIntegral (P.scheme (n + 1)) :=
      (P.datum n).isIntegral_of_genericPoint_not_mem_support hcentre
    let := hnext
    let : IsDominant (P.down n) :=
      (P.datum n).isDominant_of_genericPoint_not_mem_support hcentre
    refine ⟨hnext, ?_⟩
    change P.point (n + 1) ≠ genericPoint (P.scheme (n + 1))
    intro h
    apply hn
    calc
      P.point n = P.down n (P.point (n + 1)) := (P.point_down n).symm
      _ = P.down n (genericPoint (P.scheme (n + 1))) := congrArg (P.down n) h
      _ = genericPoint (P.scheme n) := Scheme.map_genericPoint_of_isDominant _ _

instance scheme_isIntegral (n : ℕ) : IsIntegral (P.scheme n) := (integralStage P n).integral

theorem point_ne_genericPoint (n : ℕ) : P.point n ≠ genericPoint (P.scheme n) :=
  (integralStage P n).nongeneric

instance down_isDominant (n : ℕ) : IsDominant (P.down n) :=
  (P.datum n).isDominant_of_genericPoint_not_mem_support
    (genericPoint_not_mem_pointCentre (P.point n) (P.point_closed n) (P.point_ne_genericPoint n))

instance scheme_isLocallyNoetherian (n : ℕ) : IsLocallyNoetherian (P.scheme n) := by
  induction n with
  | zero => exact P.noetherian_zero
  | succ n ih =>
    let := ih
    let : IsProper (P.down n) := (P.datum n).isProper_of_isLocallyNoetherian
    exact LocallyOfFiniteType.isLocallyNoetherian (P.down n)

/-- The local rings are the actual original scheme stalks. -/
abbrev localRing (n : ℕ) : CommRingCat.{u} := (P.scheme n).presheaf.stalk (P.point n)

instance localRing_isNoetherianRing (n : ℕ) : IsNoetherianRing (P.localRing n) :=
  inferInstanceAs (IsNoetherianRing ((P.scheme n).presheaf.stalk (P.point n)))

/-- The original local map uses the actual point equality and blowdown stalk map. -/
def transition (n : ℕ) : P.localRing n ⟶ P.localRing (n + 1) :=
  pointLocalRingMap (P.down n) (P.point (n + 1)) (P.point n) (P.point_down n)

instance transition_isLocal (n : ℕ) : IsLocalHom (P.transition n).hom :=
  pointLocalRingMap_isLocal _ _ _ _

/-- The original scalar composites into the actual successive stalks. -/
def scalar : (n : ℕ) → P.localRing 0 ⟶ P.localRing n
  | 0 => 𝟙 _
  | n + 1 => scalar n ≫ P.transition n

/-- The literal maximal-adic completion of the original starting stalk. -/
abbrev initialCompletion : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (P.localRing 0)) (P.localRing 0)

instance initialCompletion_isNoetherianRing : IsNoetherianRing P.initialCompletion :=
  AdicCompletion.isNoetherianRing (P.localRing 0) (IsLocalRing.maximalIdeal (P.localRing 0))

instance scalar_isLocal (n : ℕ) : IsLocalHom (P.scalar n).hom := by
  induction n with
  | zero => exact isLocalHom_id _
  | succ n ih =>
    let := ih
    change IsLocalHom ((P.transition n).hom.comp (P.scalar n).hom)
    exact RingHom.isLocalHom_comp (P.transition n).hom (P.scalar n).hom

/-- The original generic-point map of this actual point blowup is the field equivalence. -/
def stepFunctionFieldEquiv (n : ℕ) :
    (P.scheme n).functionField ≃+* (P.scheme (n + 1)).functionField :=
  (P.datum n).functionFieldEquiv
    (genericPoint_not_mem_pointCentre (P.point n) (P.point_closed n) (P.point_ne_genericPoint n))

theorem stepFunctionFieldEquiv_toRingHom (n : ℕ) :
    (P.stepFunctionFieldEquiv n).toRingHom = Scheme.functionFieldMap (P.down n) :=
  (P.datum n).functionFieldEquiv_toRingHom
    (genericPoint_not_mem_pointCentre (P.point n) (P.point_closed n) (P.point_ne_genericPoint n))

/-- Only the original generic-point equivalences identify all actual function fields. -/
def functionFieldEquiv : (n : ℕ) → (P.scheme 0).functionField ≃+* (P.scheme n).functionField
  | 0 => RingEquiv.refl _
  | n + 1 => (functionFieldEquiv n).trans (P.stepFunctionFieldEquiv n)

/-- The actual stalk embedding into the same original function field. -/
def embedding (n : ℕ) : P.localRing n →+* (P.scheme 0).functionField :=
  (P.functionFieldEquiv n).symm.toRingHom.comp
    (stalkToFunctionField (P.scheme n) (P.point n)).hom

theorem embedding_injective (n : ℕ) : Function.Injective (P.embedding n) :=
  (P.functionFieldEquiv n).symm.injective.comp
    (stalkToFunctionField_injective (P.scheme n) (P.point n))

/-- Compatibility is proved from the original generic/selected stalk naturality square. -/
theorem embedding_comp_transition (n : ℕ) :
    (P.embedding (n + 1)).comp (P.transition n).hom = P.embedding n := by
  apply RingHom.ext
  intro a
  have hcat := pointLocalRingMap_functionField (P.down n) (P.point (n + 1))
    (P.point n) (P.point_down n)
  have hv := congrArg
    (fun f : P.localRing n ⟶ (P.scheme (n + 1)).functionField => f.hom a) hcat
  have hfield : (stalkToFunctionField (P.scheme (n + 1)) (P.point (n + 1))).hom
      ((P.transition n).hom a) = P.stepFunctionFieldEquiv n
        ((stalkToFunctionField (P.scheme n) (P.point n)).hom a) := by
    calc
      _ = Scheme.functionFieldMap (P.down n)
          ((stalkToFunctionField (P.scheme n) (P.point n)).hom a) := hv
      _ = _ := congrArg
        (fun f : (P.scheme n).functionField →+* (P.scheme (n + 1)).functionField =>
          f ((stalkToFunctionField (P.scheme n) (P.point n)).hom a))
        (P.stepFunctionFieldEquiv_toRingHom n).symm
  change (P.functionFieldEquiv n).symm
      ((P.stepFunctionFieldEquiv n).symm
        ((stalkToFunctionField (P.scheme (n + 1)) (P.point (n + 1))).hom
          ((P.transition n).hom a))) =
    (P.functionFieldEquiv n).symm ((stalkToFunctionField (P.scheme n) (P.point n)).hom a)
  rw [hfield, RingEquiv.symm_apply_apply]

theorem embedding_scalar (n : ℕ) (a : P.localRing 0) :
    P.embedding n ((P.scalar n).hom a) = P.embedding 0 a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (RingHom.congr_fun (P.embedding_comp_transition n) ((P.scalar n).hom a)).trans ih

/-- The native local-subring range of the actual original stalk embedding. -/
def rangeChain (n : ℕ) : LocalSubring (P.scheme 0).functionField :=
  LocalSubring.range (P.embedding n)

/-- The original stalk map onto its actual embedded range. -/
def rangeMap (n : ℕ) : P.localRing n →+* (P.rangeChain n).toSubring :=
  (P.embedding n).rangeRestrict

theorem rangeMap_injective (n : ℕ) : Function.Injective (P.rangeMap n) := by
  intro x y h
  exact P.embedding_injective n (congrArg Subtype.val h)

theorem rangeMap_surjective (n : ℕ) : Function.Surjective (P.rangeMap n) := by
  intro x
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp x.2
  exact ⟨a, Subtype.ext ha⟩

instance rangeMap_isLocal (n : ℕ) : IsLocalHom (P.rangeMap n) :=
  IsLocalHom.of_surjective _ (P.rangeMap_surjective n)

/-- The range equivalence retains the literal original embedding on coefficients. -/
def rangeEquiv (n : ℕ) : P.localRing n ≃+* (P.rangeChain n).toSubring :=
  RingEquiv.ofBijective (P.rangeMap n) ⟨P.rangeMap_injective n, P.rangeMap_surjective n⟩

private theorem range_le_succ (n : ℕ) :
    (P.rangeChain n).toSubring ≤ (P.rangeChain (n + 1)).toSubring := by
  intro z hz
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hz
  exact RingHom.mem_range.mpr
    ⟨(P.transition n).hom a, RingHom.congr_fun (P.embedding_comp_transition n) a⟩

private theorem rangeMap_transition (n : ℕ) :
    (P.rangeMap (n + 1)).comp (P.transition n).hom =
      (Subring.inclusion (P.range_le_succ n)).comp (P.rangeMap n) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact RingHom.congr_fun (P.embedding_comp_transition n) a

private theorem range_inclusion_isLocal (n : ℕ) :
    IsLocalHom (Subring.inclusion (P.range_le_succ n)) := by
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := P.rangeMap_surjective n z
  have hu : IsUnit (((P.rangeMap (n + 1)).comp (P.transition n).hom) a) := by
    rw [P.rangeMap_transition n]
    exact hz
  have hau := (isUnit_map_iff ((P.rangeMap (n + 1)).comp (P.transition n).hom) a).mp hu
  exact hau.map (P.rangeMap n)

/-- The actual stalk ranges increase in the native domination order. -/
theorem range_monotone : Monotone P.rangeChain :=
  monotone_nat_of_le_succ fun n => ⟨P.range_le_succ n, P.range_inclusion_isLocal n⟩

/-- The actual range inclusion supplied to the native directed-union consumer. -/
def rangeInclusion (n m : ℕ) (hnm : n ≤ m) :
    (P.rangeChain n).toSubring →+* (P.rangeChain m).toSubring :=
  LocalSubring.DirectedUnion.stageInclusion P.rangeChain P.range_monotone n m hnm

instance rangeInclusion_isLocal (n m : ℕ) (hnm : n ≤ m) :
    IsLocalHom (P.rangeInclusion n m hnm) :=
  LocalSubring.DirectedUnion.stageInclusion_isLocal P.rangeChain P.range_monotone n m hnm

theorem rangeMap_comp_transition (n : ℕ) :
    (P.rangeMap (n + 1)).comp (P.transition n).hom =
      (P.rangeInclusion n (n + 1) (Nat.le_succ n)).comp (P.rangeMap n) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact RingHom.congr_fun (P.embedding_comp_transition n) a

theorem rangeMap_comp_scalar (n : ℕ) :
    (P.rangeMap n).comp (P.scalar n).hom =
      (P.rangeInclusion 0 n (Nat.zero_le n)).comp (P.rangeMap 0) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact P.embedding_scalar n a

theorem rangeMap_residue_bijective (n : ℕ) :
    Function.Bijective (IsLocalRing.ResidueField.map (P.rangeMap n)) := by
  refine ⟨(IsLocalRing.ResidueField.map (P.rangeMap n)).injective, ?_⟩
  intro z
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := (P.rangeChain n).toSubring) z
  obtain ⟨a, rfl⟩ := P.rangeMap_surjective n b
  exact ⟨IsLocalRing.residue (P.localRing n) a,
    IsLocalRing.ResidueField.map_residue (P.rangeMap n) a⟩

/-- The corrected marking uses the same parameter and original residue-field maps. -/
structure Marking where
  /-- The marker in the original starting stalk. -/
  parameter : P.localRing 0
  mem_maximal : parameter ∈ IsLocalRing.maximalIdeal (P.localRing 0)
  not_mem_sq : parameter ∉ IsLocalRing.maximalIdeal (P.localRing 0) ^ 2
  residue : ∀ n, Function.Bijective (IsLocalRing.ResidueField.map (P.transition n).hom)
  exceptional : ∀ n,
    (IsLocalRing.maximalIdeal (P.localRing n)).map (P.transition n).hom =
      Ideal.span {(P.scalar (n + 1)).hom parameter}

/-- The union is the actual original stalk-range union in the same original function field. -/
def union : LocalSubring (P.scheme 0).functionField :=
  LocalSubring.directedUnion P.rangeChain P.range_monotone

/-- The original actual stalk map into this one literal union. -/
def unionMap (n : ℕ) : P.localRing n →+* P.union.toSubring :=
  (LocalSubring.DirectedUnion.inclusion P.rangeChain P.range_monotone n).comp (P.rangeMap n)

instance unionMap_isLocal (n : ℕ) : IsLocalHom (P.unionMap n) :=
  @RingHom.isLocalHom_comp _ _ _ _ _ _
    (LocalSubring.DirectedUnion.inclusion P.rangeChain P.range_monotone n) (P.rangeMap n)
    (LocalSubring.DirectedUnion.inclusion_isLocal P.rangeChain P.range_monotone n)
    (P.rangeMap_isLocal n)

theorem unionMap_comp_transition (n : ℕ) :
    (P.unionMap (n + 1)).comp (P.transition n).hom = P.unionMap n := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact RingHom.congr_fun (P.embedding_comp_transition n) a

namespace Marking

variable {P} (M : P.Marking)

include M in
/-- The original residue-field isomorphisms persist along the actual scalar composite. -/
theorem scalar_residue_bijective (n : ℕ) :
    Function.Bijective (IsLocalRing.ResidueField.map (P.scalar n).hom) := by
  induction n with
  | zero =>
    change Function.Bijective (IsLocalRing.ResidueField.map (RingHom.id (P.localRing 0)))
    rw [IsLocalRing.ResidueField.map_id]
    exact Function.bijective_id
  | succ n ih =>
    change Function.Bijective (IsLocalRing.ResidueField.map
      ((P.transition n).hom.comp (P.scalar n).hom))
    rw [IsLocalRing.ResidueField.map_comp]
    exact (M.residue n).comp ih

include M in
/-- The actual initial-to-range residue map is surjective through its original square. -/
theorem range_residue_surjective (n : ℕ) :
    Function.Surjective
      (IsLocalRing.ResidueField.map (P.rangeInclusion 0 n (Nat.zero_le n))) := by
  have hsquare :
      (IsLocalRing.ResidueField.map (P.rangeMap n)).comp
          (IsLocalRing.ResidueField.map (P.scalar n).hom) =
        (IsLocalRing.ResidueField.map (P.rangeInclusion 0 n (Nat.zero_le n))).comp
          (IsLocalRing.ResidueField.map (P.rangeMap 0)) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    change IsLocalRing.residue (P.rangeChain n).toSubring
        (P.rangeMap n ((P.scalar n).hom a)) =
      IsLocalRing.residue (P.rangeChain n).toSubring
        (P.rangeInclusion 0 n (Nat.zero_le n) (P.rangeMap 0 a))
    exact congrArg (IsLocalRing.residue (P.rangeChain n).toSubring)
      (RingHom.congr_fun (P.rangeMap_comp_scalar n) a)
  have hcomp : Function.Surjective
      ((IsLocalRing.ResidueField.map (P.rangeInclusion 0 n (Nat.zero_le n))).comp
        (IsLocalRing.ResidueField.map (P.rangeMap 0))) := by
    rw [← hsquare]
    exact (P.rangeMap_residue_bijective n).2.comp (M.scalar_residue_bijective n).2
  intro z
  obtain ⟨x, hx⟩ := hcomp z
  exact ⟨IsLocalRing.ResidueField.map (P.rangeMap 0) x, hx⟩

/-- The marker is the actual image of the original starting-stalk parameter. -/
def rangeMarker : (P.rangeChain 0).toSubring := P.rangeMap 0 M.parameter

theorem rangeMarker_mem_maximal :
    M.rangeMarker ∈ IsLocalRing.maximalIdeal (P.rangeChain 0).toSubring :=
  map_nonunit (P.rangeMap 0) M.parameter M.mem_maximal

theorem rangeMarker_ne_zero : M.rangeMarker ≠ 0 := by
  intro h
  have hparam : M.parameter = 0 :=
    P.rangeMap_injective 0 (h.trans (P.rangeMap 0).map_zero.symm)
  apply M.not_mem_sq
  rw [hparam]
  exact Ideal.zero_mem _

theorem rangeMarker_scalar (n : ℕ) :
    P.rangeMap n ((P.scalar n).hom M.parameter) =
      LocalSubring.DirectedUnion.stageMarker P.rangeChain P.range_monotone M.rangeMarker n :=
  RingHom.congr_fun (P.rangeMap_comp_scalar n) M.parameter

/-- The original exceptional-ideal equality transfers through the actual range maps. -/
theorem range_exceptional (n : ℕ) :
    (IsLocalRing.maximalIdeal (P.rangeChain n).toSubring).map
        (P.rangeInclusion n (n + 1) (Nat.le_succ n)) =
      Ideal.span {LocalSubring.DirectedUnion.stageMarker
        P.rangeChain P.range_monotone M.rangeMarker (n + 1)} := by
  calc
    _ = ((IsLocalRing.maximalIdeal (P.localRing n)).map (P.rangeMap n)).map
        (P.rangeInclusion n (n + 1) (Nat.le_succ n)) := by
      rw [IsLocalRing.map_maximalIdeal_of_surjective _ (P.rangeMap_surjective n)]
    _ = (IsLocalRing.maximalIdeal (P.localRing n)).map
        ((P.rangeMap (n + 1)).comp (P.transition n).hom) := by
      rw [Ideal.map_map, ← P.rangeMap_comp_transition n]
    _ = ((IsLocalRing.maximalIdeal (P.localRing n)).map (P.transition n).hom).map
        (P.rangeMap (n + 1)) :=
      (Ideal.map_map (P.transition n).hom (P.rangeMap (n + 1))).symm
    _ = (Ideal.span {(P.scalar (n + 1)).hom M.parameter}).map (P.rangeMap (n + 1)) := by
      rw [M.exceptional n]
    _ = Ideal.span {P.rangeMap (n + 1) ((P.scalar (n + 1)).hom M.parameter)} := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = _ := congrArg (fun a => Ideal.span {a}) (M.rangeMarker_scalar (n + 1))

/-- The actual union's maximal ideal is generated by the same original parameter image. -/
theorem union_maximalIdeal :
    IsLocalRing.maximalIdeal P.union.toSubring = Ideal.span {P.unionMap 0 M.parameter} :=
  LocalSubring.DirectedUnion.maximalIdeal_eq_span P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional

/-- The original union marker is a nonzerodivisor, derived inside the same function field. -/
theorem union_marker_mem_nonZeroDivisors : P.unionMap 0 M.parameter ∈ P.union.toSubring⁰ :=
  LocalSubring.DirectedUnion.marker_mem_nonZeroDivisors P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_ne_zero

include M in
/-- The residue comparison is induced by the original starting-stalk map into the union. -/
theorem union_residue_bijective :
    Function.Bijective (IsLocalRing.ResidueField.map (P.unionMap 0)) := by
  change Function.Bijective (IsLocalRing.ResidueField.map
    ((LocalSubring.DirectedUnion.inclusion P.rangeChain P.range_monotone 0).comp (P.rangeMap 0)))
  rw [IsLocalRing.ResidueField.map_comp]
  exact (LocalSubring.DirectedUnion.residueMap_bijective P.rangeChain P.range_monotone
    M.range_residue_surjective).comp (P.rangeMap_residue_bijective 0)

/-- The one actual principal completion of the original marked path's union. -/
def arcRing : Type u :=
  LocalSubring.DirectedUnion.Completion P.rangeChain P.range_monotone M.rangeMarker

instance arcRingCommRing : CommRing M.arcRing :=
  inferInstanceAs (CommRing
    (LocalSubring.DirectedUnion.Completion P.rangeChain P.range_monotone M.rangeMarker))

instance arcRingIsLocalRing : IsLocalRing M.arcRing :=
  LocalSubring.DirectedUnion.completion_isLocalRing P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional

instance arcRingIsDomain : IsDomain M.arcRing :=
  LocalSubring.DirectedUnion.completion_isDomain P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional M.rangeMarker_ne_zero

instance arcRingIsDiscreteValuationRing : IsDiscreteValuationRing M.arcRing :=
  LocalSubring.DirectedUnion.completion_isDiscreteValuationRing P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional M.rangeMarker_ne_zero

instance arcRingIsAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal M.arcRing) M.arcRing :=
  LocalSubring.DirectedUnion.completion_isAdicComplete P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional

/-- The original stalk map to the same actual complete DVR. -/
def stageMap (n : ℕ) : P.localRing n →+* M.arcRing :=
  (LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker n).comp
    (P.rangeMap n)

instance stageMap_isLocal (n : ℕ) : IsLocalHom (M.stageMap n) :=
  @RingHom.isLocalHom_comp _ _ _ _ _ _
    (LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker n)
    (P.rangeMap n)
    (LocalSubring.DirectedUnion.stageMap_isLocal P.rangeChain P.range_monotone
      M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional n)
    (P.rangeMap_isLocal n)

/-- Compatibility is for the original blowdown stalk maps, with the same DVR target. -/
theorem stageMap_comp_transition (n : ℕ) :
    (M.stageMap (n + 1)).comp (P.transition n).hom = M.stageMap n := by
  apply RingHom.ext
  intro a
  change LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker
      (n + 1) (P.rangeMap (n + 1) ((P.transition n).hom a)) =
    LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker n
      (P.rangeMap n a)
  have h := RingHom.congr_fun (P.rangeMap_comp_transition n) a
  change P.rangeMap (n + 1) ((P.transition n).hom a) =
    P.rangeInclusion n (n + 1) (Nat.le_succ n) (P.rangeMap n a) at h
  rw [h]
  exact RingHom.congr_fun (LocalSubring.DirectedUnion.stageMap_comp P.rangeChain
    P.range_monotone M.rangeMarker n (n + 1) (Nat.le_succ n)) (P.rangeMap n a)

/-- Every transported original marker has the same image in the actual DVR. -/
theorem stageMap_parameter (n : ℕ) :
    M.stageMap n ((P.scalar n).hom M.parameter) = M.stageMap 0 M.parameter := by
  change LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker n
      (P.rangeMap n ((P.scalar n).hom M.parameter)) =
    LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker 0 M.rangeMarker
  rw [M.rangeMarker_scalar n]
  exact LocalSubring.DirectedUnion.stageMap_marker P.rangeChain P.range_monotone M.rangeMarker n

/-- The original marker maps to the uniformizer of that one actual completion. -/
theorem stageMap_parameter_irreducible : Irreducible (M.stageMap 0 M.parameter) :=
  LocalSubring.DirectedUnion.completion_marker_irreducible P.rangeChain P.range_monotone
    M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional M.rangeMarker_ne_zero

/-- The initial-stage residue comparison is induced by the actual stage map to the DVR. -/
theorem stageMap_residue_bijective :
    Function.Bijective (IsLocalRing.ResidueField.map (M.stageMap 0)) := by
  let : IsLocalRing
      (LocalSubring.DirectedUnion.Completion P.rangeChain P.range_monotone M.rangeMarker) :=
    M.arcRingIsLocalRing
  let : IsLocalHom
      (LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker 0) :=
    LocalSubring.DirectedUnion.stageMap_isLocal P.rangeChain P.range_monotone
      M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional 0
  have hcomp := LocalSubring.DirectedUnion.stageMap_residue_bijective P.rangeChain
    P.range_monotone M.rangeMarker M.rangeMarker_mem_maximal M.range_exceptional
    M.range_residue_surjective
  change Function.Bijective (IsLocalRing.ResidueField.map
    ((LocalSubring.DirectedUnion.stageMap P.rangeChain P.range_monotone M.rangeMarker 0).comp
      (P.rangeMap 0)))
  rw [IsLocalRing.ResidueField.map_comp]
  exact hcomp.comp (P.rangeMap_residue_bijective 0)

/-- The same original stage map with the native categorical stalk source fixed. -/
def stageArrow (n : ℕ) : P.localRing n ⟶ CommRingCat.of M.arcRing :=
  CommRingCat.ofHom (M.stageMap n)

/-- The arc at each original scheme is formed from its actual original selected stalk. -/
def arc (n : ℕ) : Spec (.of M.arcRing) ⟶ P.scheme n :=
  Spec.map (M.stageArrow n) ≫ (P.scheme n).fromSpecStalk (P.point n)

theorem arc_closedPoint (n : ℕ) :
    M.arc n (specClosedPoint (.of M.arcRing)) = P.point n := by
  let : IsLocalHom (M.stageArrow n).hom := M.stageMap_isLocal n
  calc
    M.arc n (specClosedPoint (.of M.arcRing)) = (P.scheme n).fromSpecStalk (P.point n)
        (Spec.map (M.stageArrow n) (specClosedPoint (.of M.arcRing))) :=
      Scheme.Hom.comp_apply _ _ _
    _ = (P.scheme n).fromSpecStalk (P.point n) (specClosedPoint (P.localRing n)) :=
      congrArg ((P.scheme n).fromSpecStalk (P.point n)) Spec_closedPoint
    _ = P.point n := Scheme.fromSpecStalk_closedPoint

/-- The original selected points and original blowdowns are the actual arc path. -/
theorem arc_map (n : ℕ) : M.arc (n + 1) ≫ P.down n = M.arc n := by
  have hq : P.transition n ≫ M.stageArrow (n + 1) = M.stageArrow n := by
    apply CommRingCat.hom_ext
    exact M.stageMap_comp_transition n
  exact arc_base_of_scalar ((P.scheme n).fromSpecStalk (P.point n))
    ((P.scheme (n + 1)).fromSpecStalk (P.point (n + 1))) (P.down n)
    (P.transition n) (M.stageArrow n) (M.stageArrow (n + 1))
    (pointLocalRingMap_fromSpecStalk (P.down n) (P.point (n + 1))
      (P.point n) (P.point_down n)).symm hq

private theorem stageArrow_maximalIdeal (n : ℕ) :
    (IsLocalRing.maximalIdeal (P.localRing n)).map (M.stageArrow n).hom =
      Ideal.span {M.stageMap 0 M.parameter} := by
  let : IsLocalHom (M.stageArrow n).hom := M.stageMap_isLocal n
  apply le_antisymm
  · exact (IsLocalRing.map_maximalIdeal_le (M.stageArrow n).hom).trans
      M.stageMap_parameter_irreducible.maximalIdeal_eq.le
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = M.stageMap 0 M.parameter)
    rw [← M.stageMap_parameter n]
    exact Ideal.mem_map_of_mem (M.stageArrow n).hom
      (map_nonunit (P.scalar n).hom M.parameter M.mem_maximal)

/-- The actual inverse-image point ideal is Cartier on the same DVR. -/
theorem arc_cartier (n : ℕ) :
    cartierPullback ((P.scheme n).fromSpecResidueField (P.point n)).ker (M.arc n) := by
  unfold cartierPullback
  rw [arc, Scheme.IdealSheafData.comap_comp,
    RegularPoint.pointCentre_comap_fromSpecStalk (P.scheme n) (P.point n) (P.point_closed n),
    affineCenter_comap_hom, M.stageArrow_maximalIdeal n]
  exact affineCenter_rankOne_of_equiv M.arcRing _
    (principalIdealEquiv (M.stageMap 0 M.parameter) M.stageMap_parameter_irreducible.ne_zero)

/-- These are the original universal blowup lifts, with the Cartier condition proved. -/
theorem arc_eq_universalLift (n : ℕ) :
    M.arc (n + 1) = (P.datum n).lift (M.arc n) (M.arc_cartier n) :=
  (P.datum n).hom_ext (M.arc_cartier n) (M.arc_map n)
    ((P.datum n).lift_map (M.arc n) (M.arc_cartier n))

private theorem initialMap_maximalIdeal :
    (IsLocalRing.maximalIdeal (P.localRing 0)).map (M.stageMap 0) =
      IsLocalRing.maximalIdeal M.arcRing :=
  (M.stageArrow_maximalIdeal 0).trans M.stageMap_parameter_irreducible.maximalIdeal_eq.symm

/-- The original stage-zero image ideal has the actual DVR maximal ideal as its radical. -/
theorem initialMap_radical :
    ((IsLocalRing.maximalIdeal (P.localRing 0)).map (M.stageMap 0)).radical =
      IsLocalRing.maximalIdeal M.arcRing := by
  rw [M.initialMap_maximalIdeal]
  exact Ideal.IsPrime.radical (I := IsLocalRing.maximalIdeal M.arcRing) inferInstance

/-- The original starting-stalk map extends to its actual maximal-adic completion.
The existing complete-parameter-map provider retains every original coefficient. -/
def completionMap : P.initialCompletion →+* M.arcRing :=
  AdicCompletion.localParameterMap (M.stageMap 0) M.initialMap_radical

theorem completionMap_algebraMap (a : P.localRing 0) :
    M.completionMap (algebraMap (P.localRing 0) P.initialCompletion a) = M.stageMap 0 a :=
  AdicCompletion.localParameterMap_algebraMap (M.stageMap 0) M.initialMap_radical a

theorem completionMap_comp_algebraMap :
    M.completionMap.comp (algebraMap (P.localRing 0) P.initialCompletion) = M.stageMap 0 := by
  apply RingHom.ext
  intro a
  exact M.completionMap_algebraMap a

/-- The extended actual maximal ideal is exactly the maximal ideal of the same DVR. -/
theorem completionMap_maximalIdeal :
    (IsLocalRing.maximalIdeal P.initialCompletion).map M.completionMap =
      IsLocalRing.maximalIdeal M.arcRing :=
  (AdicCompletion.map_maximalIdeal_localParameterMap
    (M.stageMap 0) M.initialMap_radical).trans M.initialMap_maximalIdeal

instance completionMap_isLocal : IsLocalHom M.completionMap :=
  AdicCompletion.localParameterMap_isLocalHom (M.stageMap 0) M.initialMap_radical

/-- Surjectivity on the actual residue point follows from the original stage map. -/
theorem completionMap_residue_surjective :
    Function.Surjective ((IsLocalRing.residue M.arcRing).comp M.completionMap) := by
  intro z
  obtain ⟨x, hx⟩ := M.stageMap_residue_bijective.2 z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := P.localRing 0) x
  refine ⟨algebraMap (P.localRing 0) P.initialCompletion a, ?_⟩
  change IsLocalRing.residue M.arcRing
    (M.completionMap (algebraMap (P.localRing 0) P.initialCompletion a)) = z
  rw [M.completionMap_algebraMap]
  exact (IsLocalRing.ResidueField.map_residue (M.stageMap 0) a).symm.trans hx

/-- The map from the original starting-stalk completion is actually surjective.
Completeness and the proved maximal-ideal/residue equations supply the conclusion. -/
theorem completionMap_surjective : Function.Surjective M.completionMap := by
  let : IsHausdorff
      ((IsLocalRing.maximalIdeal P.initialCompletion).map M.completionMap) M.arcRing := by
    rw [M.completionMap_maximalIdeal]
    infer_instance
  have hres : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal M.arcRing)).comp M.completionMap) :=
    M.completionMap_residue_surjective
  apply surjective_of_mk_map_comp_surjective
    (I := IsLocalRing.maximalIdeal P.initialCompletion) M.completionMap
  rw [M.completionMap_maximalIdeal]
  exact hres

/-- The uniformizer lift is still the completion image of the same original marker. -/
theorem completionMap_parameter_irreducible :
    Irreducible (M.completionMap
      (algebraMap (P.localRing 0) P.initialCompletion M.parameter)) := by
  rw [M.completionMap_algebraMap]
  exact M.stageMap_parameter_irreducible

section NormalCompletion

variable [IsDomain P.initialCompletion] [IsIntegrallyClosed P.initialCompletion]

attribute [local instance] RingHom.ker_isPrime

/-- Normality and dimension of the original completion give a DVR at the
actual kernel of the constructed surjection; no generic-regularity input is added. -/
theorem completionKernel_isDiscreteValuationRing
    (hd : ringKrullDim P.initialCompletion = 2) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker M.completionMap)) := by
  let q := RingHom.ker M.completionMap
  let D := Localization.AtPrime q
  let : IsNoetherianRing D := IsLocalization.isNoetherianRing q.primeCompl D inferInstance
  let : IsIntegrallyClosed D :=
    isIntegrallyClosed_of_isLocalization D q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hheight : q.height = 1 :=
    Localization.Away.height_ker_eq_one_of_surface_surjective M.completionMap
      M.completionMap_surjective (algebraMap (P.localRing 0) P.initialCompletion M.parameter)
      M.completionMap_parameter_irreducible hd
  have hqne : q ≠ ⊥ := by
    intro h
    have hz : q.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr h
    exact one_ne_zero (hheight.symm.trans hz)
  have hdim : ringKrullDim D = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q D, hheight]
    rfl
  exact IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one D hdim.le
    (IsLocalization.AtPrime.not_isField P.initialCompletion hqne D)

/-- The initial algebraic state uses the same constructed completion surjection
and the completion image of the original fixed marker. -/
def completedState (hd : ringKrullDim P.initialCompletion = 2) :
    Localization.Away.LocalArcState M.arcRing where
  Ring := P.initialCompletion
  commRing := inferInstance
  localRing := inferInstance
  noetherian := inferInstance
  domain := inferInstance
  quotient := M.completionMap
  surjective := M.completionMap_surjective
  parameter := algebraMap (P.localRing 0) P.initialCompletion M.parameter
  uniformizer := M.completionMap_parameter_irreducible
  genericDVR := M.completionKernel_isDiscreteValuationRing hd

/-- The passed realization starts over the completed base with its identity
local map. No preimmersion assertion is made for the original completion projection. -/
def completedRealization (hd : ringKrullDim P.initialCompletion = 2) :
    Realization (M.completedState hd) := initial (M.completedState hd)

/-- The constructed completed-base arc reaches its actual regular selected
stalk by the passed finite iteration. Original-path comparison is a separate step. -/
theorem exists_regular_completed_iterate (hd : ringKrullDim P.initialCompletion = 2) :
    ∃ n : ℕ, IsRegularLocalRing
      (((M.completedRealization hd).iterate n).X.presheaf.stalk
        (((M.completedRealization hd).iterate n).point)) :=
  (M.completedRealization hd).exists_regular_iterate

end NormalCompletion
end Marking
end ClosedPointBlowupPath
end AlgebraicGeometry.Scheme.Blowup.Arc

namespace AlgebraicGeometry.Scheme.Blowup.Arc

private theorem residueFieldMap_isIso_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨b, rfl⟩ := X.residue_surjective x z
  obtain ⟨a, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨Y.residue (f x) a,
    ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) a⟩

private theorem pointResidue_isPullback_of_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (x : X) :
    IsPullback (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap x))
      f (Y.fromSpecResidueField (f x)) := by
  let : IsIso (f.residueFieldMap x) := residueFieldMap_isIso_of_surjectiveOnStalks f x
  exact IsPullback.of_vert_isIso_mono
    ⟨(Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm⟩

private theorem pointResidue_comp_ker
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (x : X) :
    (X.fromSpecResidueField x ≫ f).ker = (Y.fromSpecResidueField (f x)).ker := by
  let : IsIso (f.residueFieldMap x) := residueFieldMap_isIso_of_surjectiveOnStalks f x
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x,
    Scheme.Hom.ker_comp_of_isIso]

private theorem ker_comap_of_isPullback
    {P X Y S : Scheme.{u}} {i : P ⟶ X} {a : P ⟶ Y} {f : X ⟶ S} {j : Y ⟶ S}
    (H : IsPullback i a f j) [IsClosedImmersion j] : j.ker.comap f = i.ker := by
  calc
    j.ker.comap f = (pullback.fst f j).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j f).symm
    _ = i.ker := by
      simpa only [Scheme.Hom.ker_comp_of_isIso] using
        congrArg Scheme.Hom.ker H.isoPullback_hom_fst

/-- Localization preserves the full actual point-centre ideal. -/
theorem pointCentre_comap_of_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (x : X)
    (hx : IsClosed ({f x} : Set Y)) :
    (Y.fromSpecResidueField (f x)).ker.comap f = (X.fromSpecResidueField x).ker := by
  let : IsClosedImmersion (Y.fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  exact ker_comap_of_isPullback (pointResidue_isPullback_of_preimmersion f x)

private theorem pointCentre_comap_of_residueSquare
    {X Y FX FY : Scheme.{u}} (f : X ⟶ Y)
    (iX : FX ⟶ X) (iY : FY ⟶ Y) [IsPreimmersion iX] [IsPreimmersion iY]
    (e : FX ≅ FY) (H : IsPullback iX e.hom f iY) (x : FX)
    (hx : IsClosed ({iY (e.hom x)} : Set Y)) :
    (Y.fromSpecResidueField (iY (e.hom x))).ker.comap f =
      (X.fromSpecResidueField (iX x)).ker := by
  let : IsClosedImmersion (Y.fromSpecResidueField (iY (e.hom x))) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let : IsIso (iY.residueFieldMap (e.hom x)) :=
    residueFieldMap_isIso_of_surjectiveOnStalks iY (e.hom x)
  let : IsClosedImmersion (FY.fromSpecResidueField (e.hom x) ≫ iY) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField iY (e.hom x)]
    infer_instance
  have Hp := (pointResidue_isPullback_of_preimmersion e.hom x).paste_horiz H
  simpa only [pointResidue_comp_ker] using ker_comap_of_isPullback Hp

private theorem completion_residue_ker_comap
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    (Scheme.LocalRing.residueSpecMap A).ker.comap (Scheme.LocalRing.completionSpecMap A) =
      (Scheme.LocalRing.residueSpecMap
        (AdicCompletion (IsLocalRing.maximalIdeal A) A)).ker := by
  change (affineCenter A (IsLocalRing.maximalIdeal A)).comap
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) =
    affineCenter (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A))
  rw [BaseChange.affineCenter_comap, AdicCompletion.maximalIdeal_eq_map]

private theorem completion_residueSquare
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    IsPullback
      (pullback.fst (pullback.snd f (Scheme.LocalRing.completionSpecMap A))
        (Scheme.LocalRing.residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      (Scheme.LocalRing.completionResidueFiberIso f).hom
      (pullback.fst f (Scheme.LocalRing.completionSpecMap A))
      (pullback.fst f (Scheme.LocalRing.residueSpecMap A)) := by
  apply isPullback_of_isClosedImmersion
  · exact (Scheme.LocalRing.completionResidueFiberIso_hom_fst f).symm
  · rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp, completion_residue_ker_comap,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- Completion preserves the full point centre at an actual closed-fibre point.
The point is represented in the literal completed residue fibre, and the
comparison uses the original completion-induced residue isomorphism. -/
theorem pointCentre_comap_completionResidueFiber
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (y : (pullback (pullback.snd f (Scheme.LocalRing.completionSpecMap A))
      (Scheme.LocalRing.residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
        Scheme.{u}))
    (hy : IsClosed
      ({pullback.fst f (Scheme.LocalRing.residueSpecMap A)
        ((Scheme.LocalRing.completionResidueFiberIso f).hom y)} : Set X)) :
    (X.fromSpecResidueField
      (pullback.fst f (Scheme.LocalRing.residueSpecMap A)
        ((Scheme.LocalRing.completionResidueFiberIso f).hom y))).ker.comap
          (pullback.fst f (Scheme.LocalRing.completionSpecMap A)) =
      ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).fromSpecResidueField
        (pullback.fst (pullback.snd f (Scheme.LocalRing.completionSpecMap A))
          (Scheme.LocalRing.residueSpecMap
            (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y)).ker :=
  pointCentre_comap_of_residueSquare _ _ _
    (Scheme.LocalRing.completionResidueFiberIso f) (completion_residueSquare f) y hy

end AlgebraicGeometry.Scheme.Blowup.Arc

namespace AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- The original composite of the given blowdowns. -/
def originMap : (n : ℕ) → P.scheme n ⟶ P.scheme 0
  | 0 => 𝟙 _
  | n + 1 => P.down n ≫ originMap n

instance down_isProper (n : ℕ) : IsProper (P.down n) :=
  (P.datum n).isProper_of_isLocallyNoetherian

instance originMap_isProper (n : ℕ) : IsProper (P.originMap n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 (P.scheme 0)))
  | succ n ih =>
    let := ih
    change IsProper (P.down n ≫ P.originMap n)
    infer_instance

/-- Localize the original base at its original selected point. -/
def localBaseMap : Spec (P.localRing 0) ⟶ P.scheme 0 :=
  (P.scheme 0).fromSpecStalk (P.point 0)

instance localBaseMap_flat : Flat P.localBaseMap :=
  Scheme.fromSpecStalk_flat (P.scheme 0) (P.point 0)

instance localBaseMap_preimmersion : IsPreimmersion P.localBaseMap :=
  inferInstanceAs (IsPreimmersion ((P.scheme 0).fromSpecStalk (P.point 0)))

/-- The literal first pullback retains the original localization projection. -/
def localBaseChange (n : ℕ) : Scheme.{u} := pullback (P.originMap n) P.localBaseMap

/-- The projection from the localized base change to the original stage scheme. -/
def localProjection (n : ℕ) : P.localBaseChange n ⟶ P.scheme n :=
  pullback.fst (P.originMap n) P.localBaseMap

/-- The structure map of the localized stage over the original starting stalk. -/
def localStructure (n : ℕ) : P.localBaseChange n ⟶ Spec (P.localRing 0) :=
  pullback.snd (P.originMap n) P.localBaseMap

instance localProjection_flat (n : ℕ) : Flat (P.localProjection n) :=
  inferInstanceAs (Flat (pullback.fst (P.originMap n) P.localBaseMap))

instance localProjection_preimmersion (n : ℕ) : IsPreimmersion (P.localProjection n) :=
  inferInstanceAs (IsPreimmersion (pullback.fst (P.originMap n) P.localBaseMap))

instance localStructure_isProper (n : ℕ) : IsProper (P.localStructure n) :=
  inferInstanceAs (IsProper (pullback.snd (P.originMap n) P.localBaseMap))

/-- Complete the same original starting stalk by its actual coefficient map. -/
def completionBaseMap : Spec (.of P.initialCompletion) ⟶ Spec (P.localRing 0) :=
  Scheme.LocalRing.completionSpecMap (P.localRing 0)

instance completionBaseMap_flat : Flat P.completionBaseMap := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The second literal pullback is over the completed localized base. -/
def completedBaseChange (n : ℕ) : Scheme.{u} :=
  pullback (P.localStructure n) P.completionBaseMap

/-- The projection from the completed base change to the localized stage. -/
def completedProjection (n : ℕ) : P.completedBaseChange n ⟶ P.localBaseChange n :=
  pullback.fst (P.localStructure n) P.completionBaseMap

/-- The structure map of the completed stage over the original starting completion. -/
def completedStructure (n : ℕ) : P.completedBaseChange n ⟶ Spec (.of P.initialCompletion) :=
  pullback.snd (P.localStructure n) P.completionBaseMap

instance completedProjection_flat (n : ℕ) : Flat (P.completedProjection n) :=
  inferInstanceAs (Flat (pullback.fst (P.localStructure n) P.completionBaseMap))

/-- C1 and the original localization stalk isomorphism return regularity to the
same original selected point. The completion projection is only flat. -/
theorem regular_original_of_completed (n : ℕ) (y : P.completedBaseChange n)
    (hy : P.localStructure n (P.completedProjection n y) = specClosedPoint (P.localRing 0))
    (hp : P.localProjection n (P.completedProjection n y) = P.point n)
    (hreg : IsRegularLocalRing ((P.completedBaseChange n).presheaf.stalk y)) :
    IsRegularLocalRing (P.localRing n) := by
  have hclosed : IsLocalRing.maximalIdeal (P.localRing 0) ≤
      (show PrimeSpectrum (P.localRing 0) from
        P.localStructure n (P.completedProjection n y)).asIdeal := by
    rw [hy]
    exact le_rfl
  have hlocal : IsRegularLocalRing
      ((P.localBaseChange n).presheaf.stalk (P.completedProjection n y)) :=
    (@Scheme.LocalRing.isRegularLocalRing_completionBaseChange_iff
      (P.localRing 0) _ (P.localRing_isNoetherianRing 0) _
      (P.localBaseChange n) (P.localStructure n) inferInstance y hclosed).mpr hreg
  let := hlocal
  let : IsIso ((P.localProjection n).stalkMap (P.completedProjection n y)) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks (P.localProjection n) _
  let e : P.localRing n ≅
      (P.localBaseChange n).presheaf.stalk (P.completedProjection n y) :=
    (pointStalkIso (P.scheme n) hp).symm ≪≫
      asIso ((P.localProjection n).stalkMap (P.completedProjection n y))
  exact IsRegularLocalRing.of_ringEquiv e.commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath

namespace AlgebraicGeometry.Scheme.Blowup.Arc

/-- The full actual point centre after completion, at any point over the closed base point. -/
theorem pointCentre_comap_completion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))
    (hy : pullback.snd f (Scheme.LocalRing.completionSpecMap A) y =
      specClosedPoint (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    (hx : IsClosed ({pullback.fst f (Scheme.LocalRing.completionSpecMap A) y} : Set X)) :
    (X.fromSpecResidueField (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).ker.comap
        (pullback.fst f (Scheme.LocalRing.completionSpecMap A)) =
      ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).fromSpecResidueField
        y).ker := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue C)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue C))
  have hmem : y ∈ Set.range
      (pullback.fst (pullback.snd f (Scheme.LocalRing.completionSpecMap A))
        (Scheme.LocalRing.residueSpecMap C)) := by
    rw [Scheme.Pullback.range_fst]
    change pullback.snd f (Scheme.LocalRing.completionSpecMap A) y ∈
      Set.range (Scheme.LocalRing.residueSpecMap C)
    rw [hy]
    exact ⟨specClosedPoint (.of (IsLocalRing.ResidueField C)),
      Spec_closedPoint (f := CommRingCat.ofHom (IsLocalRing.residue C))⟩
  obtain ⟨z, rfl⟩ := hmem
  have heq : pullback.fst f (Scheme.LocalRing.residueSpecMap A)
      ((Scheme.LocalRing.completionResidueFiberIso f).hom z) =
      pullback.fst f (Scheme.LocalRing.completionSpecMap A)
        (pullback.fst (pullback.snd f (Scheme.LocalRing.completionSpecMap A))
          (Scheme.LocalRing.residueSpecMap C) z) :=
    congrArg (fun g => g z) (Scheme.LocalRing.completionResidueFiberIso_hom_fst f)
  have hz : IsClosed
      ({pullback.fst f (Scheme.LocalRing.residueSpecMap A)
        ((Scheme.LocalRing.completionResidueFiberIso f).hom z)} : Set X) := by
    rw [heq]
    exact hx
  calc
    _ = (X.fromSpecResidueField (pullback.fst f (Scheme.LocalRing.residueSpecMap A)
        ((Scheme.LocalRing.completionResidueFiberIso f).hom z))).ker.comap
          (pullback.fst f (Scheme.LocalRing.completionSpecMap A)) :=
      congrArg (fun x : X => (X.fromSpecResidueField x).ker.comap
        (pullback.fst f (Scheme.LocalRing.completionSpecMap A))) heq.symm
    _ = _ := pointCentre_comap_completionResidueFiber f z hz

namespace ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- The original completion map followed by the original stalk-spectrum localization. -/
def completedOriginalMap : Spec (.of P.initialCompletion) ⟶ P.scheme 0 :=
  P.completionBaseMap ≫ P.localBaseMap

instance completedOriginalMap_flat : Flat P.completedOriginalMap :=
  inferInstanceAs (Flat (P.completionBaseMap ≫ P.localBaseMap))

/-- A Cartesian comparison identifies its source with the two literal base changes. -/
def completedBaseChangeIso (n : ℕ) {W : Scheme.{u}}
    (f : W ⟶ P.scheme n) (g : W ⟶ Spec (.of P.initialCompletion))
    (H : IsPullback f g (P.originMap n) P.completedOriginalMap) :
    W ≅ P.completedBaseChange n :=
  H.isoPullback ≪≫
    (pullbackLeftPullbackSndIso (P.originMap n) P.localBaseMap P.completionBaseMap).symm

theorem completedBaseChangeIso_projection (n : ℕ) {W : Scheme.{u}}
    (f : W ⟶ P.scheme n) (g : W ⟶ Spec (.of P.initialCompletion))
    (H : IsPullback f g (P.originMap n) P.completedOriginalMap) :
    (P.completedBaseChangeIso n f g H).hom ≫
      P.completedProjection n ≫ P.localProjection n = f := by
  let e := pullbackLeftPullbackSndIso (P.originMap n) P.localBaseMap P.completionBaseMap
  let a : W ⟶ pullback (P.originMap n) (P.completionBaseMap ≫ P.localBaseMap) :=
    H.isoPullback.hom
  exact (Category.assoc a e.inv
    (pullback.fst (pullback.snd (P.originMap n) P.localBaseMap) P.completionBaseMap ≫
      pullback.fst (P.originMap n) P.localBaseMap)).trans
    ((congrArg (fun k => a ≫ k)
      (pullbackLeftPullbackSndIso_inv_fst
        (P.originMap n) P.localBaseMap P.completionBaseMap)).trans H.isoPullback_hom_fst)

theorem completedBaseChangeIso_structure (n : ℕ) {W : Scheme.{u}}
    (f : W ⟶ P.scheme n) (g : W ⟶ Spec (.of P.initialCompletion))
    (H : IsPullback f g (P.originMap n) P.completedOriginalMap) :
    (P.completedBaseChangeIso n f g H).hom ≫ P.completedStructure n = g := by
  let e := pullbackLeftPullbackSndIso (P.originMap n) P.localBaseMap P.completionBaseMap
  let a : W ⟶ pullback (P.originMap n) (P.completionBaseMap ≫ P.localBaseMap) :=
    H.isoPullback.hom
  exact (Category.assoc a e.inv
    (pullback.snd (pullback.snd (P.originMap n) P.localBaseMap) P.completionBaseMap)).trans
    ((congrArg (fun k => a ≫ k)
      (pullbackLeftPullbackSndIso_inv_snd_snd
        (P.originMap n) P.localBaseMap P.completionBaseMap)).trans H.isoPullback_hom_snd)

/-- Both original base changes preserve the full centre at the actual marked point. -/
theorem pointCentre_comap_completedBaseChange (n : ℕ) (y : P.completedBaseChange n)
    (hy : P.completedStructure n y = specClosedPoint (.of P.initialCompletion))
    (hp : P.localProjection n (P.completedProjection n y) = P.point n) :
    ((P.scheme n).fromSpecResidueField (P.point n)).ker.comap
      (P.completedProjection n ≫ P.localProjection n) =
        ((P.completedBaseChange n).fromSpecResidueField y).ker := by
  have hx : IsClosed
      ({P.localProjection n (P.completedProjection n y)} : Set (P.scheme n)) := by
    rw [hp]
    exact P.point_closed n
  have hz : IsClosed ({P.completedProjection n y} : Set (P.localBaseChange n)) := by
    have heq : (P.localProjection n) ⁻¹'
        ({P.localProjection n (P.completedProjection n y)} : Set (P.scheme n)) =
        {P.completedProjection n y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        (P.localProjection n).isEmbedding.injective.eq_iff]
    rw [← heq]
    exact hx.preimage (P.localProjection n).continuous
  have hloc := pointCentre_comap_of_preimmersion
    (P.localProjection n) (P.completedProjection n y) hx
  rw [hp] at hloc
  rw [Scheme.IdealSheafData.comap_comp, hloc]
  exact @pointCentre_comap_completion (P.localRing 0) _ (P.localRing_isNoetherianRing 0) _
    (P.localBaseChange n) (P.localStructure n) y hy hz

private theorem pointCentre_comap_completedComparison (n : ℕ) {W : Scheme.{u}}
    (f : W ⟶ P.scheme n) (g : W ⟶ Spec (.of P.initialCompletion))
    (H : IsPullback f g (P.originMap n) P.completedOriginalMap)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hg : g w = specClosedPoint (.of P.initialCompletion)) (hf : f w = P.point n) :
    ((P.scheme n).fromSpecResidueField (P.point n)).ker.comap f =
      (W.fromSpecResidueField w).ker := by
  let e := P.completedBaseChangeIso n f g H
  have he : e.hom ≫ P.completedProjection n ≫ P.localProjection n = f :=
    P.completedBaseChangeIso_projection n f g H
  have hs : e.hom ≫ P.completedStructure n = g :=
    P.completedBaseChangeIso_structure n f g H
  have hy : P.completedStructure n (e.hom w) = specClosedPoint (.of P.initialCompletion) :=
    (congrArg (fun a => a w) hs).trans hg
  have hp : P.localProjection n (P.completedProjection n (e.hom w)) = P.point n :=
    (congrArg (fun a => a w) he).trans hf
  have hclosed : IsClosed ({e.hom w} : Set (P.completedBaseChange n)) :=
    Arc.isClosed_map_point e.hom e.hom.isClosedEmbedding.isClosedMap w hw
  calc
    _ = ((P.scheme n).fromSpecResidueField (P.point n)).ker.comap
        (e.hom ≫ P.completedProjection n ≫ P.localProjection n) :=
      congrArg (fun a => ((P.scheme n).fromSpecResidueField (P.point n)).ker.comap a) he.symm
    _ = (((P.completedBaseChange n).fromSpecResidueField (e.hom w)).ker).comap e.hom := by
      rw [Scheme.IdealSheafData.comap_comp, P.pointCentre_comap_completedBaseChange n _ hy hp]
    _ = _ := pointCentre_comap_of_preimmersion e.hom w hclosed

namespace Marking

variable {P} (M : P.Marking)
variable [hDomain : IsDomain P.initialCompletion] [hNormal : IsIntegrallyClosed P.initialCompletion]
variable (hd : ringKrullDim P.initialCompletion = 2)

private theorem completedOrigin_point (n : ℕ) :
    (M.completedRealization hd).originMap n ((M.completedRealization hd).iterate n).point =
      specClosedPoint (.of P.initialCompletion) := by
  rw [← ((M.completedRealization hd).iterate n).arc_closedPoint,
    ← Scheme.Hom.comp_apply, Realization.iterate_arc_originMap]
  change (Spec.map (CommRingCat.ofHom M.completionMap) ≫ 𝟙 _)
    (specClosedPoint (.of M.arcRing)) = _
  rw [Category.comp_id]
  let : IsLocalHom (CommRingCat.ofHom M.completionMap).hom := M.completionMap_isLocal
  exact Spec_closedPoint (f := CommRingCat.ofHom M.completionMap)

/-- The original scheme comparison is constructed together with its actual Cartesian square
and its actual arc triangle. It does not form part of the marked-path input. -/
structure OriginalComparison (n : ℕ) where
  /-- The comparison from the completed arc iterate to the original stage scheme. -/
  map : ((M.completedRealization hd).iterate n).X ⟶ P.scheme n
  isPullback : IsPullback map ((M.completedRealization hd).originMap n)
    (P.originMap n) P.completedOriginalMap
  arc : ((M.completedRealization hd).iterate n).arc ≫ map = M.arc n

namespace OriginalComparison

variable {M hd} {n : ℕ} (F : M.OriginalComparison hd n)

instance map_flat : Flat F.map :=
  MorphismProperty.of_isPullback (P := @Flat) F.isPullback.flip P.completedOriginalMap_flat

theorem point : F.map ((M.completedRealization hd).iterate n).point = P.point n := by
  rw [← ((M.completedRealization hd).iterate n).arc_closedPoint,
    ← Scheme.Hom.comp_apply, F.arc]
  exact M.arc_closedPoint n

theorem centre : ((P.scheme n).fromSpecResidueField (P.point n)).ker.comap F.map =
    ((M.completedRealization hd).iterate n).centre :=
  P.pointCentre_comap_completedComparison n F.map _ F.isPullback _
    ((M.completedRealization hd).iterate n).point_isClosed
    (M.completedOrigin_point hd n) F.point

/-- The successor comparison is the original universal blowup comparison. -/
def next : M.OriginalComparison hd (n + 1) where
  map := BaseChange.map F.map F.centre (P.datum n)
    ((M.completedRealization hd).iterate n).nextBlowup
  isPullback := by
    change IsPullback _
      ((M.completedRealization hd).blowdown n ≫ (M.completedRealization hd).originMap n)
      (P.down n ≫ P.originMap n) P.completedOriginalMap
    exact (BaseChange.isPullback_of_flat F.map inferInstance F.centre (P.datum n)
      ((M.completedRealization hd).iterate n).nextBlowup).paste_vert F.isPullback
  arc := by
    apply (P.datum n).hom_ext (M.arc_cartier n) _ (M.arc_map n)
    calc
      _ = (((M.completedRealization hd).iterate (n + 1)).arc ≫
          (M.completedRealization hd).blowdown n) ≫ F.map := by
        let a : Spec (.of M.arcRing) ⟶
            ((M.completedRealization hd).iterate n).nextBlowup.Y :=
          ((M.completedRealization hd).iterate (n + 1)).arc
        let b := BaseChange.map F.map F.centre (P.datum n)
          ((M.completedRealization hd).iterate n).nextBlowup
        have hb := BaseChange.map_triangle F.map F.centre (P.datum n)
          ((M.completedRealization hd).iterate n).nextBlowup
        exact (Category.assoc a b (P.datum n).map).trans
          ((congrArg (fun k => a ≫ k) hb).trans
            (Category.assoc a ((M.completedRealization hd).iterate n).nextBlowup.map F.map).symm)
      _ = ((M.completedRealization hd).iterate n).arc ≫ F.map :=
        congrArg (fun a => a ≫ F.map) ((M.completedRealization hd).iterate_arc_map n)
      _ = M.arc n := F.arc

theorem next_map : F.next.map ≫ P.down n = (M.completedRealization hd).blowdown n ≫ F.map :=
  BaseChange.map_triangle F.map F.centre (P.datum n)
    ((M.completedRealization hd).iterate n).nextBlowup

end OriginalComparison

/-- The initial comparison retains the original completion and stalk maps. -/
def originalComparisonZero : M.OriginalComparison hd 0 where
  map := P.completedOriginalMap
  isPullback := IsPullback.id_vert P.completedOriginalMap
  arc := by
    have hspec : Spec.map (CommRingCat.ofHom M.completionMap) ≫ P.completionBaseMap =
        Spec.map (M.stageArrow 0) := by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext M.completionMap_comp_algebraMap)
    change (Spec.map (CommRingCat.ofHom M.completionMap) ≫ 𝟙 _) ≫
        (P.completionBaseMap ≫ P.localBaseMap) = Spec.map (M.stageArrow 0) ≫ P.localBaseMap
    rw [Category.comp_id, ← Category.assoc, hspec]

/-- The same original path comparison is derived recursively by universal uniqueness. -/
def originalComparison : (n : ℕ) → M.OriginalComparison hd n
  | 0 => M.originalComparisonZero hd
  | n + 1 => (originalComparison n).next

theorem originalComparison_blowdown (n : ℕ) :
    (M.originalComparison hd (n + 1)).map ≫ P.down n =
      (M.completedRealization hd).blowdown n ≫ (M.originalComparison hd n).map :=
  (M.originalComparison hd n).next_map

/-- The literal algebraic iterates are realized on the completed base change of the
same original path, through its canonical Cartesian comparison. -/
def originalCompletedIso (n : ℕ) :
    ((M.completedRealization hd).iterate n).X ≅ P.completedBaseChange n :=
  P.completedBaseChangeIso n (M.originalComparison hd n).map
    ((M.completedRealization hd).originMap n) (M.originalComparison hd n).isPullback

/-- The canonical isomorphism preserves the original arc under both original projections. -/
theorem originalCompletedIso_arc (n : ℕ) :
    ((M.completedRealization hd).iterate n).arc ≫
        (M.originalCompletedIso hd n).hom ≫ P.completedProjection n ≫ P.localProjection n =
      M.arc n := by
  rw [show (M.originalCompletedIso hd n).hom ≫
      P.completedProjection n ≫ P.localProjection n = (M.originalComparison hd n).map from
    P.completedBaseChangeIso_projection n (M.originalComparison hd n).map _
      (M.originalComparison hd n).isPullback]
  exact (M.originalComparison hd n).arc

/-- The actual selected iterate point projects to the same original selected point. -/
theorem originalCompletedIso_point (n : ℕ) :
    P.localProjection n (P.completedProjection n
      ((M.originalCompletedIso hd n).hom ((M.completedRealization hd).iterate n).point)) =
        P.point n := by
  have h := P.completedBaseChangeIso_projection n (M.originalComparison hd n).map
    ((M.completedRealization hd).originMap n) (M.originalComparison hd n).isPullback
  exact (congrArg (fun a => a ((M.completedRealization hd).iterate n).point) h).trans
    (M.originalComparison hd n).point

include M hd hDomain hNormal in
/-- Under normality and dimension two of the original completion, the same marked
ordinary point-blowup path reaches a regular original selected stalk. -/
theorem exists_regular_original_point : ∃ n : ℕ, IsRegularLocalRing (P.localRing n) := by
  obtain ⟨n, hn⟩ := M.exists_regular_completed_iterate hd
  let F := M.originalComparison hd n
  let e := M.originalCompletedIso hd n
  let w := ((M.completedRealization hd).iterate n).point
  have he : e.hom ≫ P.completedProjection n ≫ P.localProjection n = F.map :=
    P.completedBaseChangeIso_projection n F.map _ F.isPullback
  have hs : e.hom ≫ P.completedStructure n = (M.completedRealization hd).originMap n :=
    P.completedBaseChangeIso_structure n F.map _ F.isPullback
  have hyC : P.completedStructure n (e.hom w) = specClosedPoint (.of P.initialCompletion) :=
    (congrArg (fun a => a w) hs).trans (M.completedOrigin_point hd n)
  have hyA : P.localStructure n (P.completedProjection n (e.hom w)) =
      specClosedPoint (P.localRing 0) := by
    have hsq := congrArg (fun a => a (e.hom w))
      (pullback.condition (f := P.localStructure n) (g := P.completionBaseMap))
    change P.localStructure n (P.completedProjection n (e.hom w)) =
      P.completionBaseMap (P.completedStructure n (e.hom w)) at hsq
    rw [hsq, hyC]
    let : IsLocalHom
        (CommRingCat.ofHom (algebraMap (P.localRing 0) P.initialCompletion)).hom :=
      inferInstanceAs (IsLocalHom (algebraMap (P.localRing 0) P.initialCompletion))
    exact Spec_closedPoint
      (f := CommRingCat.ofHom (algebraMap (P.localRing 0) P.initialCompletion))
  have hp : P.localProjection n (P.completedProjection n (e.hom w)) = P.point n :=
    (congrArg (fun a => a w) he).trans F.point
  have hreg : IsRegularLocalRing ((P.completedBaseChange n).presheaf.stalk (e.hom w)) := by
    let : IsRegularLocalRing (((M.completedRealization hd).iterate n).X.presheaf.stalk w) := hn
    let : IsIso (e.hom.stalkMap w) :=
      Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks e.hom w
    exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap w)).commRingCatIsoToRingEquiv.symm
  exact ⟨n, P.regular_original_of_completed n (e.hom w) hyA hp hreg⟩

end Marking
end ClosedPointBlowupPath
end AlgebraicGeometry.Scheme.Blowup.Arc

open IsLocalRing

namespace AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath.Marking

variable {P : ClosedPointBlowupPath.{u}} (M : P.Marking)

include M in
/-- The same marked path terminates from the original complete-base chart conditions.
Normality, domainhood and dimension of the actual starting completion are derived. -/
theorem exists_regular_original_point_of_complete_base
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [IsIntegrallyClosed (P.localRing 0)] [Algebra A (P.localRing 0)]
    [IsLocalHom (algebraMap A (P.localRing 0))]
    [Module.Finite (ResidueField A) (ResidueField (P.localRing 0))]
    (hinj : Function.Injective (algebraMap A (P.localRing 0)))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim (P.localRing 0) = 2)
    (hN : IsNagataRing.{u, 0} (P.localRing 0)) :
    ∃ n : ℕ, IsRegularLocalRing (P.localRing n) := by
  let : IsNoetherianRing (P.localRing 0) := P.localRing_isNoetherianRing 0
  obtain ⟨hdom, hnormal⟩ :=
    AdicCompletion.normalDomain_of_complete_normal_surface A (P.localRing 0) hinj hA hB hN
  let : IsDomain P.initialCompletion := hdom
  let : IsIntegrallyClosed P.initialCompletion := hnormal
  have hd : ringKrullDim P.initialCompletion = 2 :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq (P.localRing 0)).trans hB
  exact M.exists_regular_original_point hd

end AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath.Marking

namespace AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- Essential finite type of the actual transported blowdown stalk map. -/
theorem transition_essFiniteType (n : ℕ) : (P.transition n).hom.EssFiniteType := by
  let e := pointStalkIso (P.scheme n) (P.point_down n)
  have he : e.inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso e.inv).surjective).essFiniteType
  exact he.comp (LocallyOfFiniteType.stalkMap (P.down n) (P.point (n + 1)))

/-- Essential finite type follows along the original finite prefix,
including its point transports. -/
theorem scalar_essFiniteType (n : ℕ) : (P.scalar n).hom.EssFiniteType := by
  induction n with
  | zero =>
    exact (RingHom.FiniteType.of_surjective (RingHom.id (P.localRing 0))
      Function.surjective_id).essFiniteType
  | succ n ih =>
    exact ih.comp (P.transition_essFiniteType n)

/-- Algebraicity is derived from the original embedding into the original initial function field. -/
theorem scalar_isAlgebraic (n : ℕ) :
    let _ : Algebra (P.localRing 0) (P.localRing n) := (P.scalar n).hom.toAlgebra
    Algebra.IsAlgebraic (P.localRing 0) (P.localRing n) := by
  let : Algebra (P.localRing 0) (P.localRing n) := (P.scalar n).hom.toAlgebra
  let : Algebra.IsAlgebraic (P.localRing 0) (P.scheme 0).functionField :=
    IsLocalization.isAlgebraic (P.scheme 0).functionField (nonZeroDivisors (P.localRing 0))
  let j : P.localRing n →ₐ[P.localRing 0] (P.scheme 0).functionField :=
    { P.embedding n with
      commutes' a := P.embedding_scalar n a }
  exact Algebra.IsAlgebraic.of_injective j (P.embedding_injective n)

end AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath

namespace AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- Start at the actual stage r, retaining every original scheme, point and blowdown. -/
def tail (r : ℕ) : ClosedPointBlowupPath.{u} where
  scheme n := P.scheme (r + n)
  point n := P.point (r + n)
  down n := P.down (r + n)
  point_closed n := P.point_closed (r + n)
  point_down n := P.point_down (r + n)
  noetherian_zero := P.scheme_isLocallyNoetherian r
  integral_zero := P.scheme_isIntegral r
  nongeneric_zero := P.point_ne_genericPoint r
  cartier n := P.cartier (r + n)
  universal n := P.universal (r + n)

/-- Injectivity belongs to the original finite prefix scalar, via its original field square. -/
theorem scalar_injective (n : ℕ) : Function.Injective (P.scalar n).hom := by
  intro a b hab
  apply P.embedding_injective 0
  exact (P.embedding_scalar n a).symm.trans
    ((congrArg (P.embedding n) hab).trans (P.embedding_scalar n b))

/-- Original residue-field isomorphisms compose along the actual finite prefix. -/
theorem scalar_residue_bijective_of_transition
    (hres : ∀ n, Function.Bijective (ResidueField.map (P.transition n).hom)) (n : ℕ) :
    Function.Bijective (ResidueField.map (P.scalar n).hom) := by
  induction n with
  | zero =>
    change Function.Bijective (ResidueField.map (RingHom.id (P.localRing 0)))
    rw [ResidueField.map_id]
    exact Function.bijective_id
  | succ n ih =>
    change Function.Bijective
      (ResidueField.map ((P.transition n).hom.comp (P.scalar n).hom))
    rw [ResidueField.map_comp]
    exact (hres n).comp ih

/-- Actual finite residue extensions also compose along the original prefix. -/
theorem scalar_residue_finite_of_transition
    (hres : ∀ n, (ResidueField.map (P.transition n).hom).Finite) (n : ℕ) :
    (ResidueField.map (P.scalar n).hom).Finite := by
  induction n with
  | zero =>
    change (ResidueField.map (RingHom.id (P.localRing 0))).Finite
    rw [ResidueField.map_id]
    exact RingHom.Finite.id _
  | succ n ih =>
    change (ResidueField.map ((P.transition n).hom.comp (P.scalar n).hom)).Finite
    rw [ResidueField.map_comp]
    exact (hres n).comp ih

/-- The original prefix supplies the local injective coefficient map. Residue finiteness
is required for that actual map, while all completion conditions are conclusions. -/
theorem exists_regular_tail_of_complete_base
    (r : ℕ) (M : (P.tail r).Marking)
    [IsAdicComplete (maximalIdeal (P.localRing 0)) (P.localRing 0)]
    [IsIntegrallyClosed (P.localRing r)]
    (hd0 : ringKrullDim (P.localRing 0) = 2) (hdr : ringKrullDim (P.localRing r) = 2)
    (hres : (ResidueField.map (P.scalar r).hom).Finite) :
    ∃ n : ℕ, IsRegularLocalRing (P.localRing (r + n)) := by
  let : IsNoetherianRing (P.localRing 0) := P.localRing_isNoetherianRing 0
  let : IsIntegrallyClosed ((P.tail r).localRing 0) :=
    inferInstanceAs (IsIntegrallyClosed (P.localRing r))
  let : Algebra (P.localRing 0) ((P.tail r).localRing 0) := (P.scalar r).hom.toAlgebra
  let : IsLocalHom (algebraMap (P.localRing 0) ((P.tail r).localRing 0)) :=
    P.scalar_isLocal r
  let : Algebra.EssFiniteType (P.localRing 0) ((P.tail r).localRing 0) :=
    P.scalar_essFiniteType r
  let : Algebra.IsAlgebraic (P.localRing 0) ((P.tail r).localRing 0) :=
    P.scalar_isAlgebraic r
  have hmap : algebraMap (ResidueField (P.localRing 0))
      (ResidueField ((P.tail r).localRing 0)) = ResidueField.map (P.scalar r).hom :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let : Module.Finite (ResidueField (P.localRing 0))
      (ResidueField ((P.tail r).localRing 0)) :=
    RingHom.finite_algebraMap.mp (hmap.symm ▸ hres)
  have hN : IsNagataRing.{u, 0} ((P.tail r).localRing 0) :=
    IsNagataRing.of_essFiniteType_isAlgebraic_of_complete_surface hd0 (P.scalar_injective r)
  exact M.exists_regular_original_point_of_complete_base (P.localRing 0)
    (P.scalar_injective r) hd0 hdr hN

/-- In the specified unchanged-residue path scope, the original prefix's residue
finiteness follows from its actual transition isomorphisms, not from the tail marking. -/
theorem exists_regular_tail_of_complete_base_of_residue_bijective
    (r : ℕ) (M : (P.tail r).Marking)
    [IsAdicComplete (maximalIdeal (P.localRing 0)) (P.localRing 0)]
    [IsIntegrallyClosed (P.localRing r)]
    (hd0 : ringKrullDim (P.localRing 0) = 2) (hdr : ringKrullDim (P.localRing r) = 2)
    (hres : ∀ n, Function.Bijective (ResidueField.map (P.transition n).hom)) :
    ∃ n : ℕ, IsRegularLocalRing (P.localRing (r + n)) :=
  P.exists_regular_tail_of_complete_base r M hd0 hdr
    (RingHom.Finite.of_surjective _
      (P.scalar_residue_bijective_of_transition hres r).surjective)

end AlgebraicGeometry.Scheme.Blowup.Arc.ClosedPointBlowupPath
