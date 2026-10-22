/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Basic
public import Mathlib.RingTheory.Extension.Generators

/-! # Coordinates generate the translated Néron modification

When the centre has already been translated to coordinates from the base ring, the new
coordinates generate the actual torsion-free modification over that same base. This does
not perform residue-field extension or the reduction of a general centre to this case.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.NeronModification

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
/-- The old generators equal their base-ring centres plus the scaled new coordinates. -/
theorem of_generator_eq_center_add (P : Algebra.Generators R B ι) (p : R) (a : ι → R)
    (i : ι) :
    of (algebraMap R B p) (fun j => P.val j - algebraMap R B (a j)) (P.val i) =
      algebraMap R _ (a i) + algebraMap R _ p *
        coordinate (algebraMap R B p) (fun j => P.val j - algebraMap R B (a j)) i := by
  let g := fun j => P.val j - algebraMap R B (a j)
  let M := Modification (algebraMap R B p) g
  have hbase (r : R) : of (algebraMap R B p) g (algebraMap R B r) =
      algebraMap R M r := by
    change algebraMap B M (algebraMap R B r) = algebraMap R M r
    exact (IsScalarTower.algebraMap_apply R B M r).symm
  have h := of_mul_coordinate (algebraMap R B p) g i
  change of (algebraMap R B p) g (algebraMap R B p) *
    coordinate (algebraMap R B p) g i =
      of (algebraMap R B p) g (P.val i - algebraMap R B (a i)) at h
  rw [map_sub, hbase, hbase] at h
  exact (eq_sub_iff_add_eq.mp h).symm.trans (add_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The new coordinates alone generate the actual modification over the original base ring. -/
theorem aeval_coordinate_surjective (P : Algebra.Generators R B ι) (p : R) (a : ι → R) :
    Function.Surjective (MvPolynomial.aeval (R := R)
      (coordinate (algebraMap R B p) (fun j => P.val j - algebraMap R B (a j)))) := by
  let g := fun j => P.val j - algebraMap R B (a j)
  let M := Modification (algebraMap R B p) g
  let z := coordinate (algebraMap R B p) g
  let S : Subalgebra R M := (MvPolynomial.aeval (R := R) z).range
  have hz (i : ι) : z i ∈ S := ⟨X i, aeval_X z i⟩
  have hbase (r : R) : of (algebraMap R B p) g (algebraMap R B r) =
      algebraMap R M r := by
    change algebraMap B M (algebraMap R B r) = algebraMap R M r
    exact (IsScalarTower.algebraMap_apply R B M r).symm
  have hold (i : ι) : of (algebraMap R B p) g (P.val i) ∈ S := by
    rw [of_generator_eq_center_add P p a i]
    exact S.add_mem (S.algebraMap_mem (a i)) (S.mul_mem (S.algebraMap_mem p) (hz i))
  have hb (b : B) : of (algebraMap R B p) g b ∈ S := by
    have hpoly (f : MvPolynomial ι R) :
        of (algebraMap R B p) g (MvPolynomial.aeval P.val f) ∈ S := by
      induction f using MvPolynomial.induction_on with
      | C r =>
        rw [aeval_C, hbase]
        exact S.algebraMap_mem r
      | add f₁ f₂ h₁ h₂ =>
        simpa only [map_add] using S.add_mem h₁ h₂
      | mul_X f i hf =>
        simpa only [map_mul, aeval_X] using S.mul_mem hf (hold i)
    simpa only [P.aeval_val_σ b] using hpoly (P.σ b)
  let q : MvPolynomial ι B →+* M :=
    (quotientMap (algebraMap R B p) g).comp
      (Ideal.Quotient.mk (relations (algebraMap R B p) g))
  have hq (f : MvPolynomial ι B) : q f ∈ S := by
    induction f using MvPolynomial.induction_on with
    | C b => exact hb b
    | add f₁ f₂ h₁ h₂ =>
      simpa only [map_add] using S.add_mem h₁ h₂
    | mul_X f i hf =>
      rw [map_mul]
      change q f * z i ∈ S
      exact S.mul_mem hf (hz i)
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact hq f

set_option backward.isDefEq.respectTransparency false in
/-- The actual base-ring generating family by the unchanged index of new coordinates. -/
def coordinateGenerators (P : Algebra.Generators R B ι) (p : R) (a : ι → R) :
    Algebra.Generators R
      (Modification (algebraMap R B p) (fun j => P.val j - algebraMap R B (a j))) ι :=
  Algebra.Generators.ofSurjective _ (aeval_coordinate_surjective P p a)

end Algebra.NeronModification
