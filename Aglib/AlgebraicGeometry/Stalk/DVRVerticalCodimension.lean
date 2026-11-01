/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.DVRPoints
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOneOrder
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The original vertical codimension-one target point

When the actual special fibre is integral, its original generic point
specializes to every original vertical target point. A coheight-one vertical
point must equal that generic image: any strict intermediate generization
would be the generic point of the whole target, contradicting its base image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

variable [IsIntegral (pullback p
  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u})]

/-- The generic point of the actual integral special fibre specializes to
every original point above the closed base point. -/
theorem specialFiber_generic_specializes (x : X)
    (hx : p x = IsLocalRing.closedPoint R) :
    (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      (genericPoint (pullback p
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u})) ⤳ x := by
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let C : Scheme.{u} := pullback p r
  let b : C ⟶ X := pullback.fst p r
  let : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hr : r (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      IsLocalRing.closedPoint R :=
    AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨y, hy, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := r)
    x (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) (hx.trans hr.symm)
  exact hy ▸ ((genericPoint_spec C).specializes (Set.mem_univ y)).map b.continuous

/-- The actual special-fibre generic point is not the generic point of a
whole integral target that dominates the original DVR spectrum. -/
theorem specialFiber_generic_ne_genericPoint [IsIntegral X] [IsDominant p] :
    (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      (genericPoint (pullback p
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u})) ≠
      genericPoint X := by
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let C : Scheme.{u} := pullback p r
  let b : C ⟶ X := pullback.fst p r
  let : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hbase : p (b (genericPoint C)) = IsLocalRing.closedPoint R := by
    change (b ≫ p) (genericPoint C) = _
    rw [pullback.condition]
    change r ((pullback.snd p r) (genericPoint C)) = _
    rw [Subsingleton.elim ((pullback.snd p r) (genericPoint C))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)), AlgebraicGeometry.Spec_closedPoint]
  intro h
  rw [h, Scheme.map_genericPoint_of_isDominant X p] at hbase
  exact Scheme.Spec.DiscreteValuationRing.closedPoint_ne_genericPoint R hbase.symm

/-- Every original vertical coheight-one point is the image of the generic
point of the actual integral special fibre. -/
theorem eq_specialFiber_genericPoint_of_coheight_one [IsIntegral X] [IsDominant p]
    (x : X) (hx : Order.coheight x = 1) (hclosed : p x = IsLocalRing.closedPoint R) :
    x = (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      (genericPoint (pullback p
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u})) := by
  by_contra hne
  have he := Scheme.generic_of_strict_generalization_of_coheight_one hx
    (specialFiber_generic_specializes R p x hclosed) (Ne.symm hne)
  exact specialFiber_generic_ne_genericPoint R p he

end AlgebraicGeometry.Scheme.Hom
