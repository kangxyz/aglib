/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineExtendedStalkIso
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineBaseChangeIndex
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.TupleCoordinateComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-! # Original finite base change on affine geometric stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open CoefficientStalkBaseChange StalkInverseImage
attribute [local instance] hasSheafifyLarge

/-- The original pointed stalk unit is invertible, retaining its specified
point triangle rather than replacing the canonical map. -/
theorem pointedStalkUnit_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (s : Spec (.of Ω) ⟶ S) (hx : x ≫ f = s) (L : AbelianSheaf.{u, u + 1} S) :
    IsIso (pointedStalkUnit f x L s hx) := by
  subst s
  change IsIso (stalkUnit f x L)
  infer_instance

namespace Finite.GeometricNeighborhood

variable (R R' Ω : Type u) [CommRing R] [CommRing R'] [Field Ω] [IsAlgClosed Ω]
  [Algebra R Ω] [Algebra R' Ω]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of R)) (f' : X' ⟶ Spec (.of R'))
  [IsFinite f] [IsFinite f'] (g : Spec (.of R') ⟶ Spec (.of R)) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)
  (hpoint : Spec.algebraMap R' Ω ≫ g = Spec.algebraMap R Ω)

include hpoint

/-- The literal original ordinary exchange is invertible on each common-field
stalk. The component matching and all coordinate maps are the actual ones. -/
theorem finiteAffineBaseChange_stalk_isIso (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((pointSmallEtale (Spec.algebraMap R' Ω)).sheafFiber.map
      ((baseChangeMap f f' g g' h.w.symm).app F)) := by
  let s := Spec.algebraMap R Ω
  let s' := Spec.algebraMap R' Ω
  let e := finiteAffineBaseChangeIndex R R' Ω f f' g g' h hpoint
  let x := fun m => finiteAffineExtendedPoint R Ω f (e m)
  let x' := finiteAffineExtendedPoint R' Ω f'
  have hx : ∀ m, x m ≫ f = s := fun m => finiteAffineExtendedPoint_comp R Ω f (e m)
  have hx' : ∀ m, x' m ≫ f' = s' := finiteAffineExtendedPoint_comp R' Ω f'
  have hm : ∀ m, x' m ≫ g' = x m := fun m =>
    (finiteAffineBaseChangeIndex_point R R' Ω f f' g g' h hpoint m).symm
  let k : ∀ m, coefficientFiber (x m) F ≅
      coefficientFiber (x' m) ((inverseImage g').obj F) := fun m => by
    let := pointedStalkUnit_isIso g' (x' m) (x m) (hm m) F
    exact asIso (pointedStalkUnit g' (x' m) F (x m) (hm m))
  let a := finiteAffineExtendedStalkIso R Ω f F
  let b := finiteAffineExtendedStalkIso R' Ω f' ((inverseImage g').obj F)
  let v := pointedStalkUnit g s' ((directImage f).obj F) s hpoint
  let β := (pointSmallEtale s').sheafFiber.map
    ((baseChangeMap f f' g g' h.w.symm).app F)
  have hv : IsIso v := pointedStalkUnit_isIso g s' s hpoint ((directImage f).obj F)
  have ht : IsIso (v ≫ β) := by
    apply isIso_of_tuple_coordinates a b e k (v ≫ β)
    intro z m
    change (finiteAffineExtendedStalkIso R' Ω f' ((inverseImage g').obj F)).hom
        ((v ≫ β) z) m = (k m).hom
      ((finiteAffineExtendedStalkIso R Ω f F).hom z (e m))
    rw [finiteAffineExtendedStalkIso_apply, finiteAffineExtendedStalkIso_apply]
    rw [finiteAffineExtendedCoordinate_eq_evaluation,
      finiteAffineExtendedCoordinate_eq_evaluation]
    exact ConcreteCategory.congr_hom
      (pointedDirectImageEvaluation_baseChange f f' g g' h.w.symm
        (x m) s (x' m) s' (hx m) hpoint (hx' m) (hm m) F) z
  exact (isIso_comp_left_iff v β).mp ht

end Finite.GeometricNeighborhood

end AlgebraicGeometry.Scheme.EtaleCohomology
