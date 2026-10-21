/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationDegree
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel
public import Aglib.GroupTheory.Torsion.RankTwo

/-!
# Rank-two coordinates on the actual geometric torsion points

The cardinalities are obtained from the proved geometric degree of literal
multiplication. The carrier remains `MultiplicationKernel.finiteTorsionPoints`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F : Type u} [Field F]
variable (E : Grp (FScheme F)) [IsCommMonObj E.X]

/-- The canonical cyclic-coefficient action on the literal multiplication kernel. -/
instance torsionModule (n : ℕ) : Module (ZMod n) (finiteTorsionPoints E n) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext (torsion_killed E n x))

/-- The native integer torsion subgroup and the existing geometric kernel have
exactly the same underlying point. -/
def torsionByEquiv (n : ℕ) : finiteTorsionPoints E n ≃+
    AddSubgroup.torsionBy (geometricPoints E) (n : ℤ) where
  toFun x := ⟨x.val, AddSubgroup.torsionBy.nsmul_iff.mpr x.property⟩
  invFun x := ⟨x.val, AddSubgroup.torsionBy.nsmul_iff.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Comparison with the literal fibre used by `HasGeometricDegree`. -/
def torsionFibreEquiv (n : ℕ) : finiteTorsionPoints E n ≃
    {x : Over.mk (FieldGalois.geometricPoint F) ⟶ E.X //
      x ≫ multiplication E n = 1} where
  toFun x := ⟨x.val.toMul, by
    rw [point_multiplication]
    exact x.property⟩
  invFun x := ⟨Additive.ofMul x.val, by
    change x.val ^ n = 1
    rw [← point_multiplication]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual geometric torsion subgroup has the cardinality supplied by the
proved multiplication degree. -/
theorem card_finiteTorsionPoints (hE : Curve.Properties E.X)
    (hg : Curve.coherentGenus F E.X = 1) (n : ℕ) (hn : IsUnit (n : F)) :
    Nat.card (finiteTorsionPoints E n) = n * n := by
  rw [Nat.card_congr (torsionFibreEquiv E n)]
  exact Multiplication.multiplication_hasGeometricDegree E hE hg n hn
    (AlgebraicClosure F) (FieldGalois.geometricPoint F) 1

/-- An invertible level makes every divisor level invertible in the same field. -/
theorem divisor_isUnit {d n : ℕ} (hdn : d ∣ n) (hn : IsUnit (n : F)) :
    IsUnit (d : F) := by
  obtain ⟨e, rfl⟩ := hdn
  rw [Nat.cast_mul] at hn
  exact isUnit_of_mul_isUnit_left hn

/-- Every divisor-level cardinality comes from its own literal multiplication
degree; the composite-level conclusion uses this whole family. -/
theorem card_torsionBy_divisor (hE : Curve.Properties E.X)
    (hg : Curve.coherentGenus F E.X = 1) (n : ℕ) (hn : IsUnit (n : F))
    (d : ℕ) (hdn : d ∣ n) :
    Nat.card (AddSubgroup.torsionBy (geometricPoints E) (d : ℤ)) = d * d :=
  (Nat.card_congr (torsionByEquiv E d).toEquiv).symm.trans
    (card_finiteTorsionPoints E hE hg d (divisor_isUnit hdn hn))

/-- A basis on the literal existing torsion point group. Its only geometric
premises are the actual curve properties, coherent genus one, and invertibility
of the positive level. -/
def torsionBasis (hE : Curve.Properties E.X)
    (hg : Curve.coherentGenus F E.X = 1) (n : ℕ) (hn : 0 < n)
    (hnF : IsUnit (n : F)) : Module.Basis (Fin 2) (ZMod n) (finiteTorsionPoints E n) :=
  AddSubgroup.TorsionBy.basisOfEquiv n ((torsionByEquiv E n).trans
    (Classical.choice (AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card
      (geometricPoints E) n hn (card_torsionBy_divisor E hE hg n hnF))))

/-- Scalar-compatible coordinates for the actual torsion point group. -/
def torsionCoordinates (hE : Curve.Properties E.X)
    (hg : Curve.coherentGenus F E.X = 1) (n : ℕ) (hn : 0 < n)
    (hnF : IsUnit (n : F)) :
    finiteTorsionPoints E n ≃ₗ[ZMod n] (Fin 2 → ZMod n) :=
  (torsionBasis E hE hg n hn hnF).equivFun

/-- The original Galois endomorphism is linear for the canonical scalar action. -/
def torsionGaloisLinear (n : ℕ) (σ : Field.absoluteGaloisGroup F) :
    finiteTorsionPoints E n →ₗ[ZMod n] finiteTorsionPoints E n :=
  (torsionGalois E n σ).toZModLinearMap n

@[simp] theorem torsionGaloisLinear_apply (n : ℕ) (σ : Field.absoluteGaloisGroup F)
    (x : finiteTorsionPoints E n) :
    torsionGaloisLinear E n σ x = torsionGalois E n σ x := rfl

/-- Every actual additive map between divisible torsion levels respects
the usual coefficient reduction. In particular this applies to the existing
literal lowering and reduction maps, without choosing new coordinates. -/
def torsionMapLinear (d n : ℕ) (hdn : d ∣ n)
    (f : finiteTorsionPoints E n →+ finiteTorsionPoints E d) :
    finiteTorsionPoints E n →ₛₗ[ZMod.castHom hdn (ZMod d)] finiteTorsionPoints E d :=
  { f with
    map_smul' := by
      intro c x
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact map_zsmul f k x }

@[simp] theorem torsionMapLinear_apply (d n : ℕ) (hdn : d ∣ n)
    (f : finiteTorsionPoints E n →+ finiteTorsionPoints E d)
    (x : finiteTorsionPoints E n) : torsionMapLinear E d n hdn f x = f x := rfl

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel
