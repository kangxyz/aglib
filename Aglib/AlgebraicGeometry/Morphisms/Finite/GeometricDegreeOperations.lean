/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegree
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Actual geometric fibre composition and isomorphism degrees

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.DualIsogeny`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 385–414,611–631.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OverField
universe u
variable {F : Type u} [Field F]

/-- Literal fibres of a composite decompose into the fibres of its two maps. -/
def compositionFibreEquiv {X Y Z T : FScheme F} (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : T ⟶ Z) :
    {x : T ⟶ X // x ≫ (f ≫ g) = z} ≃
      Σ y : {y : T ⟶ Y // y ≫ g = z}, {x : T ⟶ X // x ≫ f = y.1} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype (fun x : T ⟶ X => x ≫ f)
    (p := fun x => x ≫ (f ≫ g) = z) (q := fun y : T ⟶ Y => y ≫ g = z)
    (fun x => by rw [Category.assoc])).symm

/-- The decomposition uses the original intermediate point, literally. -/
@[simp] theorem compositionFibreEquiv_first {X Y Z T : FScheme F}
    (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
    (x : {x : T ⟶ X // x ≫ (f ≫ g) = z}) :
    ((compositionFibreEquiv f g z x).1 : T ⟶ Y) = x.1 ≫ f := rfl

/-- Its source representative is the original point of the first scheme. -/
@[simp] theorem compositionFibreEquiv_second {X Y Z T : FScheme F}
    (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
    (x : {x : T ⟶ X // x ≫ (f ≫ g) = z}) :
    (compositionFibreEquiv f g z x).2.1 = x.1 := rfl

/-- Positive all-geometric-fibre degrees multiply; this is a proved finite
set calculation on the genuine scheme-point fibres. -/
theorem geometricDegree_comp {X Y Z : FScheme F} (f : X ⟶ Y) (g : Y ⟶ Z)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hf : HasGeometricDegree f a) (hg : HasGeometricDegree g b) :
    HasGeometricDegree (f ≫ g) (a * b) := by
  classical
  intro K _ _ s z
  let : Finite {y : Over.mk s ⟶ Y // y ≫ g = z} :=
    Nat.finite_of_card_ne_zero ((hg K s z).trans_ne (Nat.ne_of_gt hb))
  let := Fintype.ofFinite {y : Over.mk s ⟶ Y // y ≫ g = z}
  let (y : {y : Over.mk s ⟶ Y // y ≫ g = z}) :
      Finite {x : Over.mk s ⟶ X // x ≫ f = y.1} :=
    Nat.finite_of_card_ne_zero ((hf K s y.1).trans_ne (Nat.ne_of_gt ha))
  rw [Nat.card_congr (compositionFibreEquiv f g z), Nat.card_sigma]
  simp only [hf K s, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hg K s z]
  exact Nat.mul_comm _ _

/-- An actual scheme isomorphism has exactly one lift of every geometric point. -/
theorem geometricDegree_iso {X Y : FScheme F} (e : X ≅ Y) :
    HasGeometricDegree e.hom 1 := by
  intro K _ _ s y
  let : Unique {x : Over.mk s ⟶ X // x ≫ e.hom = y} := {
    default := ⟨y ≫ e.inv, by simp⟩
    uniq := fun x => Subtype.ext (by
      apply (cancel_mono e.hom).1
      simpa using x.2) }
  simp

/-- Geometric degree is unchanged under an actual original-field conjugacy. -/
theorem geometricDegree_conjugate {X Y : FScheme F} (e : X ≅ Y) (f : Y ⟶ Y)
    {d : ℕ} (hd : 0 < d) (hf : HasGeometricDegree f d) :
    HasGeometricDegree (e.hom ≫ f ≫ e.inv) d := by
  have h := geometricDegree_comp e.hom (f ≫ e.inv) (by omega) (by simpa using hd)
    (geometricDegree_iso e)
    (geometricDegree_comp f e.inv hd (by omega) hf (geometricDegree_iso e.symm))
  simpa using h


end AlgebraicGeometry.Scheme.OverField
