/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix
public import Mathlib.Logic.Equiv.Basic

/-!
# Rerooting the same original finite point prefixes

Native sigma reassociation separates the first actual child from the remaining
history. Endpoint equalities retain the same native blowups, blowdowns and
point-local-ring maps. No height or termination assertion is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable (eligible : (Y : Scheme.{u}) → Y → Prop)

private theorem child_cast_endpoint {P Q : (Σ Y : Scheme.{u}, Y)} (h : P = Q)
    (z : Child eligible P.1 P.2) :
    (⟨(blowupDatum (P.1.fromSpecResidueField P.2).ker).Y, z.val⟩ : Σ Y : Scheme.{u}, Y) =
      ⟨(blowupDatum (Q.1.fromSpecResidueField Q.2).ker).Y,
        (Equiv.cast (congrArg (fun R : Σ Y : Scheme.{u}, Y =>
          Child eligible R.1 R.2) h) z).val⟩ := by
  cases h
  rfl

/-- Computational comparison data for the same prefixes, with their original
pointed endpoints. The only recursion is native sigma reassociation. -/
def rerootData (X : Scheme.{u}) (x : X) : (n : ℕ) →
    {E : Prefix eligible X x (n + 1) ≃
      (Σ y : Child eligible X x,
        Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) //
      ∀ p, (⟨scheme p, point p⟩ : Σ Y : Scheme.{u}, Y) =
        ⟨scheme (E p).2, point (E p).2⟩}
  | 0 => ⟨{
      toFun := fun p => ⟨p.2, PUnit.unit⟩
      invFun := fun p => ⟨PUnit.unit, p.1⟩
      left_inv := by rintro ⟨⟨⟩, y⟩; rfl
      right_inv := by rintro ⟨y, ⟨⟩⟩; rfl }, by
        rintro ⟨⟨⟩, y⟩
        rfl⟩
  | n + 1 => by
      let R := rerootData X x n
      let E := (Equiv.sigmaCongr R.1 (fun p =>
        Equiv.cast (congrArg (fun Q : Σ Y : Scheme.{u}, Y =>
          Child eligible Q.1 Q.2) (R.2 p)))).trans
        (Equiv.sigmaAssoc (fun (y : Child eligible X x)
          (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) =>
            Child eligible (scheme q) (point q)))
      refine ⟨E, by
        intro p
        exact child_cast_endpoint eligible (R.2 p.1) p.2⟩

variable {eligible} {X : Scheme.{u}} {x : X} {n : ℕ}

/-- The first actual child and the remaining original history. -/
def rerootEquiv (n : ℕ) : Prefix eligible X x (n + 1) ≃
    (Σ y : Child eligible X x,
      Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :=
  (rerootData eligible X x n).1

/-- Rerooting retains equality of the actual endpoint scheme and point. -/
theorem reroot_endpoint (p : Prefix eligible X x (n + 1)) :
    (⟨scheme p, point p⟩ : Σ Y : Scheme.{u}, Y) =
      ⟨scheme (rerootEquiv n p).2, point (rerootEquiv n p).2⟩ :=
  (rerootData eligible X x n).2 p

/-- The original first selected child. -/
def firstChild (p : Prefix eligible X x (n + 1)) : Child eligible X x :=
  (rerootEquiv n p).1

/-- Prepend the actual first child using the inverse of the same equivalence. -/
def prepend (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :
    Prefix eligible X x (n + 1) :=
  (rerootEquiv n).symm ⟨y, q⟩

@[simp] theorem rerootEquiv_prepend (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :
    rerootEquiv n (prepend y q) = ⟨y, q⟩ :=
  (rerootEquiv n).apply_symm_apply ⟨y, q⟩

@[simp] theorem prepend_rerootEquiv (p : Prefix eligible X x (n + 1)) :
    prepend (rerootEquiv n p).1 (rerootEquiv n p).2 = p :=
  (rerootEquiv n).symm_apply_apply p

@[simp] theorem firstChild_prepend (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :
    firstChild (prepend y q) = y := by
  exact congrArg Sigma.fst (rerootEquiv_prepend y q)

@[simp] theorem prepend_zero (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val 0) :
    prepend y q = snoc (eligible := eligible) (X := X) (x := x) (n := 0) PUnit.unit y := rfl

/-- The first-child fibre uses the native sigma-subtype equivalence. -/
def firstChildFiberEquiv (y : Child eligible X x) (n : ℕ) :
    {p : Prefix eligible X x (n + 1) // firstChild p = y} ≃
      Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n :=
  ((rerootEquiv n).subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype y)

/-- Prepending retains the original pointed endpoint, not just an abstract stalk. -/
theorem prepend_endpoint (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :
    (⟨scheme (prepend y q), point (prepend y q)⟩ : Σ Y : Scheme.{u}, Y) =
      ⟨scheme q, point q⟩ := by
  exact (reroot_endpoint (prepend y q)).trans
    (congrArg (fun r : Σ y : Child eligible X x,
      Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n =>
        (⟨scheme r.2, point r.2⟩ : Σ Y : Scheme.{u}, Y)) (rerootEquiv_prepend y q))

theorem prepend_injective (y : Child eligible X x) (n : ℕ) :
    Function.Injective (prepend y :
      Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n →
        Prefix eligible X x (n + 1)) := by
  intro p q h
  have hs : (⟨y, p⟩ : Σ y : Child eligible X x,
      Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) = ⟨y, q⟩ := by
    simpa only [rerootEquiv_prepend] using congrArg (rerootEquiv n) h
  exact (Sigma.mk.inj_iff.mp hs).2.eq

/-- Dropping the last child commutes with the first-child decomposition. -/
theorem rerootEquiv_parent (p : Prefix eligible X x (n + 2)) :
    (⟨(rerootEquiv (n + 1) p).1, parent (rerootEquiv (n + 1) p).2⟩ :
      Σ y : Child eligible X x,
        Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) =
      rerootEquiv n (parent p) := rfl

@[simp] theorem prepend_parent (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val (n + 1)) :
    parent (prepend y q) = prepend y (parent q) := by
  apply (rerootEquiv n).injective
  rw [rerootEquiv_prepend, ← rerootEquiv_parent, rerootEquiv_prepend]

@[simp] theorem firstChild_parent (p : Prefix eligible X x (n + 2)) :
    firstChild (parent p) = firstChild p :=
  (congrArg Sigma.fst (rerootEquiv_parent p)).symm

/-- Every truncation keeps the original prepended child. -/
theorem prepend_truncate (y : Child eligible X x) {i j : ℕ} (h : i ≤ j)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val j) :
    truncate (Nat.succ_le_succ h) (prepend y q) = prepend y (truncate h q) := by
  induction j, h using Nat.le_induction with
  | base => simp only [truncate_refl]
  | succ j hj ih =>
    rw [truncate_succ (Nat.succ_le_succ hj), truncate_succ hj, prepend_parent]
    exact ih (parent q)

/-- The original length-one truncation is exactly the original first child. -/
theorem truncate_one_eq_firstChild (p : Prefix eligible X x (n + 1)) :
    truncate (Nat.succ_le_succ (Nat.zero_le n)) p =
      snoc (eligible := eligible) (X := X) (x := x) (n := 0) PUnit.unit (firstChild p) := by
  induction n with
  | zero =>
    rcases p with ⟨⟨⟩, y⟩
    rfl
  | succ n ih =>
    rw [truncate_succ (Nat.succ_le_succ (Nat.zero_le n)), ih]
    exact congrArg (fun y : Child eligible X x =>
      snoc (eligible := eligible) (X := X) (x := x) (n := 0) PUnit.unit y)
      (firstChild_parent p)

private theorem datum_square_of_endpoint_eq {P Q : (Σ Y : Scheme.{u}, Y)} (h : P = Q) :
    eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y =>
      (blowupDatum (R.1.fromSpecResidueField R.2).ker).Y) h) ≫
        (blowupDatum (Q.1.fromSpecResidueField Q.2).ker).map =
      (blowupDatum (P.1.fromSpecResidueField P.2).ker).map ≫
        eqToHom (congrArg Sigma.fst h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The endpoint equality compares the same original blowdown maps. -/
theorem prepend_datum_map_square (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) :
    eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y =>
      (blowupDatum (R.1.fromSpecResidueField R.2).ker).Y) (prepend_endpoint y q)) ≫
        (datum q).map = (datum (prepend y q)).map ≫
      eqToHom (congrArg Sigma.fst (prepend_endpoint y q)) :=
  datum_square_of_endpoint_eq (prepend_endpoint y q)

private theorem point_pair_eq {Y Z : Scheme.{u}} (h : Y = Z) (z : Y) :
    (⟨Y, z⟩ : Σ W : Scheme.{u}, W) = ⟨Z, (eqToHom h) z⟩ := by
  cases h
  rfl

private theorem stalk_square_of_endpoint_eq {P Q : (Σ Y : Scheme.{u}, Y)} (h : P = Q)
    (z : (blowupDatum (P.1.fromSpecResidueField P.2).ker).Y)
    (hz : (blowupDatum (P.1.fromSpecResidueField P.2).ker).map z = P.2) :
    let hs := congrArg (fun R : Σ Y : Scheme.{u}, Y =>
      (blowupDatum (R.1.fromSpecResidueField R.2).ker).Y) h
    ∃ hz' : (blowupDatum (Q.1.fromSpecResidueField Q.2).ker).map ((eqToHom hs) z) = Q.2,
      Arc.pointLocalRingMap (blowupDatum (P.1.fromSpecResidueField P.2).ker).map z P.2 hz ≫
        eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y => R.1.presheaf.stalk R.2)
          (point_pair_eq hs z)) =
      eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y => R.1.presheaf.stalk R.2) h) ≫
        Arc.pointLocalRingMap (blowupDatum (Q.1.fromSpecResidueField Q.2).ker).map
          ((eqToHom hs) z) Q.2 hz' := by
  cases h
  refine ⟨hz, ?_⟩
  let f := Arc.pointLocalRingMap (blowupDatum (P.1.fromSpecResidueField P.2).ker).map
    z P.2 hz
  change f ≫ 𝟙 _ = 𝟙 _ ≫ f
  simp only [Category.comp_id, Category.id_comp]

/-- Original local-ring arrows commute with the endpoint equality transports.
The same actual child point and original blowdown are used on both sides. -/
theorem prepend_pointLocalRingMap_square (y : Child eligible X x)
    (q : Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n)
    (z : (datum (prepend y q)).Y) (hz : (datum (prepend y q)).map z = point (prepend y q)) :
    let h := prepend_endpoint y q
    let hs := congrArg (fun R : Σ Y : Scheme.{u}, Y =>
      (blowupDatum (R.1.fromSpecResidueField R.2).ker).Y) h
    ∃ hz' : (datum q).map ((eqToHom hs) z) = point q,
      Arc.pointLocalRingMap (datum (prepend y q)).map z (point (prepend y q)) hz ≫
        eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y => R.1.presheaf.stalk R.2)
          (show (⟨(datum (prepend y q)).Y, z⟩ : Σ W : Scheme.{u}, W) =
            ⟨(datum q).Y, (eqToHom hs) z⟩ from by
              exact Eq.rec (motive := fun Z h =>
                (⟨(datum (prepend y q)).Y, z⟩ : Σ W : Scheme.{u}, W) =
                  ⟨Z, (eqToHom h) z⟩) rfl hs)) =
      eqToHom (congrArg (fun R : Σ Y : Scheme.{u}, Y => R.1.presheaf.stalk R.2) h) ≫
        Arc.pointLocalRingMap (datum q).map ((eqToHom hs) z) (point q) hz' :=
  stalk_square_of_endpoint_eq (prepend_endpoint y q) z hz

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
