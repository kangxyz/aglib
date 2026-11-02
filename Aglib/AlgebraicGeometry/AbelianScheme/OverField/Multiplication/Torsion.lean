/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Rank
public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale
public import Aglib.GroupTheory.Torsion.Rank

/-!
# Geometric torsion of the original projective field group

At an invertible level, the original multiplication map is finite etale
with its proved native rank. Its full geometric degree therefore counts
the actual torsion points and the actual native kernel points. The free
torsion description uses the proved cardinality at EVERY divisor level,
not just the cardinality of the final torsion group.

The equivalence is asserted to exist. No canonical basis or Galois-equivariant
choice is claimed. Level one and dimension zero are included.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

private theorem card_finiteTorsionPoints_of_hasGeometricDegree
    (G : Grp (FScheme k)) [IsCommMonObj G.X] (n D : ℕ)
    (h : HasGeometricDegree (MultiplicationKernel.multiplication G n) D) :
    Nat.card (MultiplicationKernel.finiteTorsionPoints G n) = D := by
  let T := Over.mk (FieldGalois.geometricPoint k)
  let e : MultiplicationKernel.finiteTorsionPoints G n ≃
      {x : T ⟶ G.X // x ≫ MultiplicationKernel.multiplication G n = 1} :=
    { toFun := fun x => ⟨x.val.toMul,
        (MultiplicationKernel.point_multiplication G n x.val.toMul).trans
          (show x.val.toMul ^ n = 1 from x.property)⟩
      invFun := fun x => ⟨Additive.ofMul x.val,
        (MultiplicationKernel.point_multiplication G n x.val).symm.trans x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  exact (Nat.card_congr e).trans (h (AlgebraicClosure k) (FieldGalois.geometricPoint k) 1)

/-- Invertible original multiplication has geometric degree equal to
its proved locally free rank, over every original field. -/
theorem multiplication_hasGeometricDegree_of_isUnit
    (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : IsUnit (n : k)) :
    HasGeometricDegree ((𝟙 G.X) ^ n)
      (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  let : IsFinite ((𝟙 G.X) ^ n).left :=
    (multiplication_finite_flat_surjective_of_isHProjective G n hpos).1
  let : Etale ((𝟙 G.X) ^ n).left := multiplication_etale_of_smooth_of_isUnit G n hn
  exact (Hom.hasLocallyFreeRank_iff_hasGeometricDegree Hom.finiteFlatPresentationLocallyFree
    Scheme.Modules.affineModuleBaseChange ((𝟙 G.X) ^ n) _).mp
      (multiplication_hasLocallyFreeRank G n hpos)

/-- The actual n-torsion of the original geometric point group has
cardinality n^(2d) when n is invertible in the original field. -/
theorem card_geometric_torsionBy_of_isUnit
    (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Nat.card (AddSubgroup.torsionBy (MultiplicationKernel.geometricPoints G) (n : ℤ)) =
      n ^ (2 * Module.finrank k (Cotangent.Space η[G.X])) := by
  rw [AddSubgroup.torsionBy_natCast_eq_ker]
  change Nat.card (MultiplicationKernel.finiteTorsionPoints G n) = _
  exact card_finiteTorsionPoints_of_hasGeometricDegree G n _
    (multiplication_hasGeometricDegree_of_isUnit G n hn)

/-- The geometric points of the existing native multiplication kernel
have the same cardinality, through its original kernel-point equivalence. -/
theorem card_nativeKernelPoints_of_isUnit
    (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Nat.card (Over.mk (FieldGalois.geometricPoint k) ⟶ (MultiplicationKernel.kernelGroup G n).X) =
      n ^ (2 * Module.finrank k (Cotangent.Space η[G.X])) := by
  exact (Nat.card_congr (MultiplicationKernel.nativeKernelPointEquiv G n)).symm.trans
    (card_finiteTorsionPoints_of_hasGeometricDegree G n _
      (multiplication_hasGeometricDegree_of_isUnit G n hn))

/-- The original geometric n-torsion admits a noncanonical free torsion
description. Every divisor-level cardinality is supplied by the native
geometric degree theorem. -/
theorem nonempty_geometric_torsionEquiv_of_isUnit
    (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Nonempty (AddSubgroup.torsionBy (MultiplicationKernel.geometricPoints G) (n : ℤ) ≃+
      (Fin (2 * Module.finrank k (Cotangent.Space η[G.X])) → ZMod n)) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  apply AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card_pow
    (MultiplicationKernel.geometricPoints G) _ n hpos
  intro d hdn
  have hd : IsUnit (d : k) := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hn.ne_zero
    obtain ⟨a, ha⟩ := hdn
    rw [ha, Nat.cast_mul, hzero, zero_mul]
  exact card_geometric_torsionBy_of_isUnit G d hd

end AlgebraicGeometry.Scheme.Group.Multiplication
