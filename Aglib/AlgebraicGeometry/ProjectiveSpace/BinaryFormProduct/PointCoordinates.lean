/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.FieldAlgebra
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.FieldPoints

/-!
# Finite-or-infinite coordinates of the original projective-line factors

The vectors `(1,a)` and `(0,1)` define points of the original native
projective line through its existing lifted-coordinate isomorphism.
Every relative field-valued point is one of these same scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

variable {R K : Type u} [CommRing R] [Field K]

/-- The original two-coordinate vector for a finite or infinite field parameter. -/
def factorVector (a : Option K) (j : ULift.{u} (Fin 2)) : K :=
  if j.down = 0 then first a else second a

/-- A coordinate that is literally one in the original normalized factor vector. -/
def factorCoordinate : Option K → ULift.{u} (Fin 2)
  | none => ULift.up 1
  | some _ => ULift.up 0

@[simp]
theorem factorVector_zero (a : Option K) : factorVector a (ULift.up 0) = first a := by
  simp [factorVector]

@[simp]
theorem factorVector_one (a : Option K) : factorVector a (ULift.up 1) = second a := by
  simp [factorVector]

@[simp]
theorem factorVector_selected (a : Option K) : factorVector a (factorCoordinate a) = 1 := by
  cases a <;> simp [factorCoordinate, first, second]

/-- An arbitrary nonzero original two-coordinate vector has a normalized
finite-or-infinite vector with a nonzero original scalar. -/
theorem exists_factorVector (v : ULift.{u} (Fin 2) → K) (hv : ∃ j, v j ≠ 0) :
    ∃ (a : Option K) (c : K), c ≠ 0 ∧ ∀ j, v j = c * factorVector a j := by
  classical
  by_cases hx : v (ULift.up 0) = 0
  · have hy : v (ULift.up 1) ≠ 0 := by
      intro hz
      obtain ⟨j, hj⟩ := hv
      have hall : ∀ i : Fin 2, v (ULift.up i) = 0 := Fin.forall_fin_two.mpr ⟨hx, hz⟩
      exact hj (by simpa only [ULift.up_down] using hall j.down)
    refine ⟨none, v (ULift.up 1), hy, ?_⟩
    intro j
    rcases j with ⟨j⟩
    fin_cases j <;> simp [factorVector, first, second, hx]
  · refine ⟨some (v (ULift.up 1) / v (ULift.up 0)), v (ULift.up 0), hx, ?_⟩
    intro j
    rcases j with ⟨j⟩
    fin_cases j
    · simp [factorVector, first]
    · exact (mul_div_cancel₀ (v (ULift.up 1)) hx).symm

/-- The original normalized point, in the lifted original two-coordinate space. -/
def liftedLinePoint (β : R →+* K) (a : Option K) :
    Spec (.of K) ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  point β (factorVector a) (factorCoordinate a)
    (by rw [factorVector_selected]; exact one_ne_zero)

/-- The same original normalized point of the unchanged native projective line. -/
def linePoint (β : R →+* K) (a : Option K) :
    Spec (.of K) ⟶ Scheme.ProjectiveLine.projectiveP1 R :=
  liftedLinePoint β a ≫ (finUliftIso R 2).inv

@[reassoc (attr := simp)]
theorem linePoint_over (β : R →+* K) (a : Option K) :
    linePoint β a ≫ Scheme.ProjectiveLine.structureMap R =
      Spec.map (CommRingCat.ofHom β) := by
  have h : (finUliftIso R 2).inv ≫ Scheme.ProjectiveLine.structureMap R =
      toSpec R (ULift.{u} (Fin 2)) := (finUliftOverIso R 2).inv.w
  rw [linePoint, Category.assoc, h]
  exact point_over β (factorVector a) (factorCoordinate a) _

@[reassoc (attr := simp)]
theorem linePoint_lifted (β : R →+* K) (a : Option K) :
    linePoint β a ≫ (finUliftIso R 2).hom = liftedLinePoint β a := by
  rw [linePoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every actual field-valued point of the original native line is one of
the same normalized finite-or-infinite relative scheme morphisms. -/
theorem exists_linePoint (β : R →+* K)
    (s : Spec (.of K) ⟶ Scheme.ProjectiveLine.projectiveP1 R)
    (hs : s ≫ Scheme.ProjectiveLine.structureMap R = Spec.map (CommRingCat.ofHom β)) :
    ∃ a : Option K, linePoint β a = s := by
  let g := s ≫ (finUliftIso R 2).hom
  have hg : g ≫ toSpec R (ULift.{u} (Fin 2)) = Spec.map (CommRingCat.ofHom β) := by
    dsimp only [g]
    rw [Category.assoc, finUliftIso_hom_toSpec]
    exact hs
  obtain ⟨v, j₀, hj, hv⟩ := exists_point β g hg
  obtain ⟨a, c, hc, ha⟩ := exists_factorVector v ⟨j₀, hj⟩
  have he : liftedLinePoint β a = g :=
    (point_eq_of_scale β (factorVector a) v (factorCoordinate a) j₀
      (by rw [factorVector_selected]; exact one_ne_zero) hj c hc ha).trans hv
  refine ⟨a, ?_⟩
  rw [linePoint, he]
  simp only [g, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field
