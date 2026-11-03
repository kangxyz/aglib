/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc.MarkedPath

/-!
# Finite prefixes of original closed-point blowups

Each extension selects an actual closed point of the existing native point
blowup. Compatible prefixes realize the existing original infinite path,
with its original blowdown and point-local-ring maps. Finiteness is asserted
only from an explicit finite set of eligible actual points.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable (eligible : (Y : Scheme.{u}) → Y → Prop)

/-- An eligible actual closed child above the selected original point. -/
def Child (Y : Scheme.{u}) (p : Y) : Type u :=
  {y : (blowupDatum (Y.fromSpecResidueField p).ker).Y //
    IsClosed ({y} : Set (blowupDatum (Y.fromSpecResidueField p).ker).Y) ∧
      (blowupDatum (Y.fromSpecResidueField p).ker).map y = p ∧
      eligible (blowupDatum (Y.fromSpecResidueField p).ker).Y y}

/-- Computational recursion data for the one actual prefix implementation. -/
abbrev Stage : Type (u + 1) :=
  Σ P : Type u, Σ Y : P → Scheme.{u}, (p : P) → Y p

/-- Extend the same recursion data by the original child construction. -/
def nextStage (S : Stage.{u}) : Stage.{u} :=
  ⟨(p : S.1) × Child eligible (S.2.1 p) (S.2.2 p),
    fun p => (blowupDatum ((S.2.1 p.1).fromSpecResidueField (S.2.2 p.1)).ker).Y,
    fun p => p.2.val⟩

/-- The recursive endpoint data underlying the public finite-prefix type. -/
def stages (X : Scheme.{u}) (x : X) : ℕ → Stage.{u}
  | 0 => ⟨PUnit.{u + 1}, fun _ => X, fun _ => x⟩
  | n + 1 => nextStage eligible (stages X x n)

/-- Finite actual point histories of length `n`, in the point universe. -/
def Prefix (X : Scheme.{u}) (x : X) (n : ℕ) : Type u :=
  (stages eligible X x n).1

variable {eligible} {X : Scheme.{u}} {x : X} {n : ℕ}

/-- The original endpoint scheme of the finite history. -/
def scheme (p : Prefix eligible X x n) : Scheme.{u} :=
  (stages eligible X x n).2.1 p

/-- The selected original endpoint point of the finite history. -/
def point (p : Prefix eligible X x n) : scheme p :=
  (stages eligible X x n).2.2 p

/-- The existing native point blowup at the endpoint, without a new model. -/
def datum (p : Prefix eligible X x n) : BlowupDatum ((scheme p).fromSpecResidueField
    (point p)).ker :=
  blowupDatum ((scheme p).fromSpecResidueField (point p)).ker

/-- Append one actual eligible closed child to the finite history. -/
def snoc (p : Prefix eligible X x n) (y : Child eligible (scheme p) (point p)) :
    Prefix eligible X x (n + 1) := ⟨p, y⟩

/-- Remove the last actual child; this is the original sigma projection. -/
def parent (p : Prefix eligible X x (n + 1)) : Prefix eligible X x n := p.1

@[simp] theorem parent_snoc (p : Prefix eligible X x n)
    (y : Child eligible (scheme p) (point p)) : parent (snoc p y) = p := rfl

@[simp] theorem scheme_snoc (p : Prefix eligible X x n)
    (y : Child eligible (scheme p) (point p)) : scheme (snoc p y) = (datum p).Y := rfl

@[simp] theorem point_snoc (p : Prefix eligible X x n)
    (y : Child eligible (scheme p) (point p)) : point (snoc p y) = y.val := rfl

/-- The actual one-step truncation fibre is exactly its actual child type. -/
def parentFiberEquiv (p : Prefix eligible X x n) :
    {q : Prefix eligible X x (n + 1) // parent q = p} ≃
      Child eligible (scheme p) (point p) where
  toFun q := by
    obtain ⟨⟨p', y⟩, h⟩ := q
    change p' = p at h
    subst p
    exact y
  invFun y := ⟨snoc p y, rfl⟩
  left_inv := by
    rintro ⟨⟨p', y⟩, h⟩
    change p' = p at h
    subst p
    rfl
  right_inv _ := rfl

/-- Finiteness comes from the actual eligible-point set, not from the prefix type. -/
theorem child_finite (Y : Scheme.{u}) (p : Y)
    (hfin : {y : (blowupDatum (Y.fromSpecResidueField p).ker).Y |
      eligible (blowupDatum (Y.fromSpecResidueField p).ker).Y y}.Finite) :
    Finite (Child eligible Y p) := by
  let : Finite {y : (blowupDatum (Y.fromSpecResidueField p).ker).Y //
      eligible (blowupDatum (Y.fromSpecResidueField p).ker).Y y} :=
    Set.finite_coe_iff.mpr hfin
  apply Finite.of_injective
    (fun y : Child eligible Y p => ⟨y.val, y.property.2.2⟩ :
      Child eligible Y p → {y : (blowupDatum (Y.fromSpecResidueField p).ker).Y //
        eligible (blowupDatum (Y.fromSpecResidueField p).ker).Y y})
  intro a b h
  apply Subtype.ext
  exact congrArg (fun y : {y : (blowupDatum (Y.fromSpecResidueField p).ker).Y //
    eligible (blowupDatum (Y.fromSpecResidueField p).ker).Y y} => y.val) h

/-- A finite eligible-point set makes the literal parent fibre finite. -/
theorem parent_fiber_finite (p : Prefix eligible X x n)
    (hfin : {y : (datum p).Y | eligible (datum p).Y y}.Finite) :
    Finite {q : Prefix eligible X x (n + 1) // parent q = p} := by
  let := child_finite (eligible := eligible) (scheme p) (point p) hfin
  exact Finite.of_equiv _ (parentFiberEquiv p).symm

/-- Truncate by iterating the existing one-step projections. -/
def truncate {i j : ℕ} (h : i ≤ j) : Prefix eligible X x j → Prefix eligible X x i :=
  Nat.leRecOn (C := fun k => Prefix eligible X x k → Prefix eligible X x i) h
    (fun f p => f (parent p)) id

@[simp] theorem truncate_refl (p : Prefix eligible X x n) :
    truncate (Nat.le_refl n) p = p := by
  simp only [truncate, Nat.leRecOn_self, id_eq]

theorem truncate_succ {i j : ℕ} (h : i ≤ j) (p : Prefix eligible X x (j + 1)) :
    truncate (Nat.le_succ_of_le h) p = truncate h (parent p) := by
  simp only [truncate, Nat.leRecOn_succ h]

/-- Truncation retains the same original earlier history under composition. -/
theorem truncate_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (p : Prefix eligible X x k) :
    truncate hij (truncate hjk p) = truncate (hij.trans hjk) p := by
  induction k, hjk using Nat.le_induction with
  | base => simp only [truncate_refl]
  | succ k hk ih =>
    rw [truncate_succ hk, truncate_succ (hij.trans hk)]
    exact ih (parent p)

/-- Every selected point is globally closed when the original root is closed. -/
theorem point_closed (hx : IsClosed ({x} : Set X)) (p : Prefix eligible X x n) :
    IsClosed ({point p} : Set (scheme p)) := by
  cases n with
  | zero => exact hx
  | succ n => exact p.2.property.1

/-- Eligibility belongs to the original points of the finite history. -/
theorem point_eligible (hx : eligible X x) (p : Prefix eligible X x n) :
    eligible (scheme p) (point p) := by
  cases n with
  | zero => exact hx
  | succ n => exact p.2.property.2.2

/-- The same original datum map with only the target prefix equality transported. -/
def stepDown (q : Prefix eligible X x (n + 1))
    (p : Prefix eligible X x n) (h : parent q = p) : scheme q ⟶ scheme p := by
  subst p
  exact (datum (parent q)).map

private theorem stepDown_eq (q : Prefix eligible X x (n + 1))
    (p : Prefix eligible X x n) (h : parent q = p) :
    stepDown q p h = (datum (parent q)).map ≫
      eqToHom (congrArg (fun p : Prefix eligible X x n => scheme p) h) := by
  subst p
  simp only [stepDown, eqToHom_refl, Category.comp_id]
  rfl

private theorem stepDown_point (q : Prefix eligible X x (n + 1))
    (p : Prefix eligible X x n) (h : parent q = p) :
    stepDown q p h (point q) = point p := by
  subst p
  exact q.2.property.2.1

private theorem stepDown_cartier (q : Prefix eligible X x (n + 1))
    (p : Prefix eligible X x n) (h : parent q = p) :
    cartierPullback ((scheme p).fromSpecResidueField (point p)).ker (stepDown q p h) := by
  subst p
  exact (datum (parent q)).cartier

private theorem stepDown_universal (q : Prefix eligible X x (n + 1))
    (p : Prefix eligible X x n) (h : parent q = p)
    (T : Scheme.{u}) (f : T ⟶ scheme p)
    (hf : cartierPullback ((scheme p).fromSpecResidueField (point p)).ker f) :
    ∃! g : T ⟶ scheme q, g ≫ stepDown q p h = f := by
  subst p
  exact (datum (parent q)).universal T f hf

variable (b : (n : ℕ) → Prefix eligible X x n)
    (hb : ∀ n, parent (b (n + 1)) = b n)
    (hx : IsClosed ({x} : Set X)) [IsLocallyNoetherian X] [IsIntegral X]
    (hne : x ≠ genericPoint X)

/-- Realize compatible actual prefixes as the existing original point-blowup path. -/
def path : Arc.ClosedPointBlowupPath.{u} where
  scheme n := scheme (b n)
  point n := point (b n)
  down n := stepDown (b (n + 1)) (b n) (hb n)
  point_closed n := point_closed hx (b n)
  point_down n := by exact stepDown_point (b (n + 1)) (b n) (hb n)
  noetherian_zero := inferInstanceAs (IsLocallyNoetherian X)
  integral_zero := inferInstanceAs (IsIntegral X)
  nongeneric_zero := hne
  cartier n := by exact stepDown_cartier (b (n + 1)) (b n) (hb n)
  universal n := by exact stepDown_universal (b (n + 1)) (b n) (hb n)

@[simp] theorem path_scheme (n : ℕ) :
    (path b hb hx hne).scheme n = scheme (b n) := rfl

@[simp] theorem path_point (n : ℕ) :
    (path b hb hx hne).point n = point (b n) := rfl

/-- The original blowdown is the native datum map with only target equality transport. -/
theorem path_down (n : ℕ) :
    (path b hb hx hne).down n = (datum (parent (b (n + 1)))).map ≫
      eqToHom (congrArg (fun p : Prefix eligible X x n => scheme p) (hb n)) :=
  stepDown_eq (b (n + 1)) (b n) (hb n)

/-- The original path's transition is the literal point-local-ring map of that blowdown. -/
theorem path_transition (n : ℕ) :
    (path b hb hx hne).transition n = Arc.pointLocalRingMap
      ((datum (parent (b (n + 1)))).map ≫
        eqToHom (congrArg (fun p : Prefix eligible X x n => scheme p) (hb n)))
      (point (b (n + 1))) (point (b n)) (by
        rw [← stepDown_eq (b (n + 1)) (b n) (hb n)]
        exact stepDown_point (b (n + 1)) (b n) (hb n)) := by
  change Arc.pointLocalRingMap (stepDown (b (n + 1)) (b n) (hb n))
    (point (b (n + 1))) (point (b n)) _ = _
  congr 1
  exact stepDown_eq (b (n + 1)) (b n) (hb n)

/-- Eligibility is proved at every actual point of the realized path. -/
theorem path_eligible (hroot : eligible X x) (n : ℕ) :
    eligible ((path b hb hx hne).scheme n) ((path b hb hx hne).point n) :=
  point_eligible hroot (b n)

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
