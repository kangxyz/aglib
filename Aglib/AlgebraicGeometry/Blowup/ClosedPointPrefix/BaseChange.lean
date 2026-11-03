/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange.ClosedFiber

/-!
# Original singular point prefixes under flat preimmersion base change

The original native point-centre pullback and blowup comparison recursively
identify finite singular prefixes. Every child remains globally closed over
the fixed closed image root. Both actual pullback projections and the native
stalk-arrow comparison are retained; no height or termination is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

/-- The accepted prefix type with its literal singular-point eligibility. -/
abbrev SingularPrefix (X : Scheme.{u}) (x : X) (n : ℕ) : Type u :=
  Prefix (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) X x n

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsPreimmersion j]
    (xU : U) (xX : X) (hpoint : j xU = xX) (hx : IsClosed ({xX} : Set X))

/-- The existing canonical point-blowup comparison for the exact original centre equality. -/
def pointBaseChangeMap :
    (blowupDatum (U.fromSpecResidueField xU).ker).Y ⟶
      (blowupDatum (X.fromSpecResidueField xX).ker).Y :=
  BaseChange.map j (by
    subst xX
    exact Arc.pointCentre_comap_of_preimmersion j xU hx)
    (blowupDatum (X.fromSpecResidueField xX).ker)
    (blowupDatum (U.fromSpecResidueField xU).ker)

/-- The square is the native flat base-change square for the same comparison. -/
theorem pointBaseChangeMap_isPullback [Flat j] :
    IsPullback (pointBaseChangeMap j xU xX hpoint hx)
      (blowupDatum (U.fromSpecResidueField xU).ker).map
      (blowupDatum (X.fromSpecResidueField xX).ker).map j :=
  BaseChange.isPullback_of_flat j inferInstance (by
    subst xX
    exact Arc.pointCentre_comap_of_preimmersion j xU hx) _ _

instance pointBaseChangeMap_flat [Flat j] :
    Flat (pointBaseChangeMap j xU xX hpoint hx) :=
  MorphismProperty.of_isPullback (P := @Flat)
    (pointBaseChangeMap_isPullback j xU xX hpoint hx).flip inferInstance

instance pointBaseChangeMap_isPreimmersion [Flat j] :
    IsPreimmersion (pointBaseChangeMap j xU xX hpoint hx) :=
  MorphismProperty.of_isPullback (P := @IsPreimmersion)
    (pointBaseChangeMap_isPullback j xU xX hpoint hx).flip inferInstance

/-- The same comparison is open whenever the original base map is open. -/
instance pointBaseChangeMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (pointBaseChangeMap j xU xX hpoint hx) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pointBaseChangeMap_isPullback j xU xX hpoint hx).flip inferInstance

/-- Actual globally closed singular children correspond through the native
point-blowup comparison, without an abstract eligibility-invariance premise. -/
def singularChildEquiv [Flat j] :
    Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) U xU ≃
      Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) X xX := by
  subst xX
  let B := blowupDatum (X.fromSpecResidueField (j xU)).ker
  let D := blowupDatum (U.fromSpecResidueField xU).ker
  let eU : Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) U xU ≃
      {y : D.Y // D.map y = xU ∧ IsClosed ({y} : Set D.Y) ∧
        ¬ IsRegularLocalRing (D.Y.presheaf.stalk y)} :=
    Equiv.subtypeEquivRight (fun _ => and_left_comm)
  let eX : Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) X (j xU) ≃
      {y : B.Y // B.map y = j xU ∧ IsClosed ({y} : Set B.Y) ∧
        ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)} :=
    Equiv.subtypeEquivRight (fun _ => and_left_comm)
  exact eU.trans ((closedSingularFiberEquivOfIsPullback
    (pointBaseChangeMap_isPullback j xU (j xU) rfl hx) xU hx).trans eX.symm)

@[simp] theorem singularChildEquiv_apply_val [Flat j]
    (y : Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y)) U xU) :
    (singularChildEquiv j xU xX hpoint hx y).val =
      pointBaseChangeMap j xU xX hpoint hx y.val := by
  subst xX
  rfl

/-- One comparison stage stores only equivalence of the existing prefixes
and actual maps between their existing endpoint schemes. -/
def ComparisonStage (U : Scheme.{u}) (xU : U) (X : Scheme.{u}) (xX : X) (n : ℕ) :=
  Σ E : SingularPrefix U xU n ≃ SingularPrefix X xX n,
    (p : SingularPrefix U xU n) →
      {g : scheme p ⟶ scheme (E p) //
        Flat g ∧ IsPreimmersion g ∧ g (point p) = point (E p)}

/-- Extend the one original comparison by its native child-fibre equivalences. -/
def nextComparison {U X : Scheme.{u}} {xU : U} {xX : X} {n : ℕ}
    (hx : IsClosed ({xX} : Set X)) (S : ComparisonStage U xU X xX n) :
    ComparisonStage U xU X xX (n + 1) := by
  let E : SingularPrefix U xU (n + 1) ≃ SingularPrefix X xX (n + 1) :=
    Equiv.sigmaCongr S.1 (fun p : SingularPrefix U xU n => by
      letI : Flat (S.2 p).val := (S.2 p).property.1
      letI : IsPreimmersion (S.2 p).val := (S.2 p).property.2.1
      exact singularChildEquiv (S.2 p).val (point p)
        (point (S.1 p)) (S.2 p).property.2.2 (point_closed hx (S.1 p)))
  refine ⟨E, fun q => ?_⟩
  let p := parent q
  letI : Flat (S.2 p).val := (S.2 p).property.1
  letI : IsPreimmersion (S.2 p).val := (S.2 p).property.2.1
  refine ⟨pointBaseChangeMap (S.2 p).val (point p) (point (S.1 p))
    (S.2 p).property.2.2 (point_closed hx (S.1 p)), ?_, ?_, ?_⟩
  · exact pointBaseChangeMap_flat (S.2 p).val (point p) (point (S.1 p))
      (S.2 p).property.2.2 (point_closed hx (S.1 p))
  · exact pointBaseChangeMap_isPreimmersion (S.2 p).val (point p) (point (S.1 p))
      (S.2 p).property.2.2 (point_closed hx (S.1 p))
  · exact (singularChildEquiv_apply_val (S.2 p).val (point p) (point (S.1 p))
      (S.2 p).property.2.2 (point_closed hx (S.1 p)) q.2).symm

variable {xU xX hpoint hx}

/-- The unique recursive family of the original native prefix comparisons. -/
def comparisonStages [Flat j] (xU : U) (hx : IsClosed ({j xU} : Set X)) :
    (n : ℕ) → ComparisonStage U xU X (j xU) n := by
  let hflat : Flat j := inferInstance
  let hpre : IsPreimmersion j := inferInstance
  exact fun n => Nat.rec (motive := fun n => ComparisonStage U xU X (j xU) n)
    ⟨Equiv.refl _, fun _ => ⟨j, hflat, hpre, rfl⟩⟩
    (fun _ S => nextComparison hx S) n

/-- Equivalence of the same singular finite-prefix types under actual base change. -/
def singularPrefixEquiv [Flat j] (xU : U) (hx : IsClosed ({j xU} : Set X)) (n : ℕ) :
    SingularPrefix U xU n ≃ SingularPrefix X (j xU) n :=
  (comparisonStages j xU hx n).1

/-- The original endpoint comparison, not an independently supplied map. -/
def singularPrefixMap [Flat j] (xU : U) (hx : IsClosed ({j xU} : Set X))
    {n : ℕ} (p : SingularPrefix U xU n) :
    scheme p ⟶ scheme (singularPrefixEquiv j xU hx n p) :=
  ((comparisonStages j xU hx n).2 p).val

instance singularPrefixMap_flat [Flat j] (xU : U) (hx : IsClosed ({j xU} : Set X))
    {n : ℕ} (p : SingularPrefix U xU n) : Flat (singularPrefixMap j xU hx p) :=
  ((comparisonStages j xU hx n).2 p).property.1

instance singularPrefixMap_isPreimmersion [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ} (p : SingularPrefix U xU n) :
    IsPreimmersion (singularPrefixMap j xU hx p) :=
  ((comparisonStages j xU hx n).2 p).property.2.1

/-- The comparison retains the actual selected endpoint point. -/
theorem singularPrefixMap_point [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ} (p : SingularPrefix U xU n) :
    singularPrefixMap j xU hx p (point p) = point (singularPrefixEquiv j xU hx n p) :=
  ((comparisonStages j xU hx n).2 p).property.2.2

@[simp] theorem singularPrefixEquiv_zero [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) :
    singularPrefixEquiv j xU hx 0 = Equiv.refl _ := rfl

@[simp] theorem singularPrefixMap_zero [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) (p : SingularPrefix U xU 0) :
    singularPrefixMap j xU hx p = j := rfl

/-- Parent truncation is unchanged by the original prefix equivalence. -/
@[simp] theorem singularPrefixEquiv_parent [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    parent (singularPrefixEquiv j xU hx (n + 1) p) =
      singularPrefixEquiv j xU hx n (parent p) := rfl

/-- The successor equivalence uses the same actual child-fibre map. -/
theorem singularPrefixEquiv_snoc [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU n)
    (y : Child (fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
      (scheme p) (point p)) :
    singularPrefixEquiv j xU hx (n + 1) (snoc p y) =
      snoc (singularPrefixEquiv j xU hx n p)
        (singularChildEquiv (singularPrefixMap j xU hx p) (point p)
          (point (singularPrefixEquiv j xU hx n p))
          (singularPrefixMap_point j xU hx p)
          (point_closed hx (singularPrefixEquiv j xU hx n p)) y) := rfl

/-- Every finite truncation commutes with the same prefix equivalence. -/
theorem singularPrefixEquiv_truncate [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {i k : ℕ} (hik : i ≤ k)
    (p : SingularPrefix U xU k) :
    singularPrefixEquiv j xU hx i (truncate hik p) =
      truncate hik (singularPrefixEquiv j xU hx k p) := by
  induction k, hik using Nat.le_induction with
  | base => simp only [truncate_refl]
  | succ k hk ih =>
    rw [truncate_succ hk, truncate_succ hk, singularPrefixEquiv_parent]
    exact ih (parent p)

/-- Each successor endpoint map is literally the native point base-change map. -/
theorem singularPrefixMap_succ [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    singularPrefixMap j xU hx p =
      pointBaseChangeMap (singularPrefixMap j xU hx (parent p)) (point (parent p))
        (point (singularPrefixEquiv j xU hx n (parent p)))
        (singularPrefixMap_point j xU hx (parent p))
        (point_closed hx (singularPrefixEquiv j xU hx n (parent p))) := rfl

/-- The actual successor square is cartesian with its original blowdowns. -/
theorem singularPrefixMap_isPullback [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    IsPullback (singularPrefixMap j xU hx p) (datum (parent p)).map
      (datum (singularPrefixEquiv j xU hx n (parent p))).map
      (singularPrefixMap j xU hx (parent p)) :=
  pointBaseChangeMap_isPullback (singularPrefixMap j xU hx (parent p))
    (point (parent p)) (point (singularPrefixEquiv j xU hx n (parent p)))
    (singularPrefixMap_point j xU hx (parent p))
    (point_closed hx (singularPrefixEquiv j xU hx n (parent p)))

/-- The first native pullback projection is the same endpoint comparison. -/
theorem singularPrefixMap_isoPullback_hom_fst [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    (singularPrefixMap_isPullback j xU hx p).isoPullback.hom ≫
      pullback.fst (datum (singularPrefixEquiv j xU hx n (parent p))).map
        (singularPrefixMap j xU hx (parent p)) = singularPrefixMap j xU hx p :=
  (singularPrefixMap_isPullback j xU hx p).isoPullback_hom_fst

/-- The second native pullback projection is the original source blowdown. -/
theorem singularPrefixMap_isoPullback_hom_snd [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    (singularPrefixMap_isPullback j xU hx p).isoPullback.hom ≫
      pullback.snd (datum (singularPrefixEquiv j xU hx n (parent p))).map
        (singularPrefixMap j xU hx (parent p)) = (datum (parent p)).map :=
  (singularPrefixMap_isPullback j xU hx p).isoPullback_hom_snd

/-- Open base maps give open original endpoint maps at every finite prefix. -/
instance singularPrefixMap_isOpenImmersion [IsOpenImmersion j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ} (p : SingularPrefix U xU n) :
    IsOpenImmersion (singularPrefixMap j xU hx p) := by
  induction n with
  | zero => exact inferInstanceAs (IsOpenImmersion j)
  | succ n ih =>
    let : IsOpenImmersion (singularPrefixMap j xU hx (parent p)) := ih (parent p)
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (singularPrefixMap_isPullback j xU hx p).flip inferInstance

/-- The actual original blowdown stalk arrows are compared by the existing
native flat-preimmersion square, with the selected target point retained. -/
def singularPrefixStalkMapIso [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    Arrow.mk ((datum (singularPrefixEquiv j xU hx n (parent p))).map.stalkMap
      (point (singularPrefixEquiv j xU hx (n + 1) p))) ≅
      Arrow.mk ((datum (parent p)).map.stalkMap (point p)) :=
  Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
    (singularPrefixMap_isPullback j xU hx p) (point p)
    (point (singularPrefixEquiv j xU hx (n + 1) p))
    (singularPrefixMap_point j xU hx p)

/-- The right component of the arrow comparison is the literal original
pointLocalRingMap of the actual endpoint projection. -/
theorem singularPrefixStalkMapIso_right_hom [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X)) {n : ℕ}
    (p : SingularPrefix U xU (n + 1)) :
    (Arrow.rightFunc.mapIso (singularPrefixStalkMapIso j xU hx p)).hom =
      Arc.pointLocalRingMap (singularPrefixMap j xU hx p) (point p)
        (point (singularPrefixEquiv j xU hx (n + 1) p))
        (singularPrefixMap_point j xU hx p) := rfl

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
