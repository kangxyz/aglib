/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.FullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-!
# Original geometric stalks of extension by zero

Inside the open, the original inverse-image stalk comparison and the actual
lower-shriek unit identify the stalk. Outside the open, chart restriction of
a geometric skyscraper is zero; the two actual adjunctions then force the
extension stalk to vanish. No neighborhood disjoint from the open is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Inside the open, lower shriek has the original geometric stalk of its coefficient sheaf. -/
def etaleLowerShriekStalkIso (η : Spec (.of Ω) ⟶ U) :
    etaleLowerShriek j ⋙ (pointSmallEtale (η ≫ j)).sheafFiber
        (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale η).sheafFiber :=
  Functor.isoWhiskerLeft (etaleLowerShriek j) (StalkInverseImage.nativeStalkIso j η) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleLowerShriekInverseImageIso j) _ ≪≫
    Functor.leftUnitor _

/-- A skyscraper whose geometric point does not lift to the open restricts to zero. -/
theorem isZero_etaleRestriction_skyscraper_of_no_lift
    (η : Spec (.of Ω) ⟶ X) (hη : ∀ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j ≠ η)
    (N : AddCommGrpCat.{u + 1}) :
    IsZero ((etaleRestriction j).obj ((pointSmallEtale η).skyscraperSheaf N)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply Pi.hom_ext
  intro p
  exact (hη (p.left ≫ V.unop.hom) (by
    have hp := Over.w p
    change p.left ≫ (V.unop.hom ≫ j) = η at hp
    exact (Category.assoc _ _ _).trans hp)).elim

/-- The original geometric stalk of lower shriek vanishes when the point has no open lift. -/
theorem isZero_etaleLowerShriek_stalk_of_no_lift
    (η : Spec (.of Ω) ⟶ X) (hη : ∀ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j ≠ η)
    (F : AbelianSheaf.{u, u + 1} U) :
    IsZero ((pointSmallEtale η).sheafFiber.obj ((etaleLowerShriek j).obj F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  let N := (pointSmallEtale η).sheafFiber.obj ((etaleLowerShriek j).obj F)
  let e := ((pointSmallEtale η).skyscraperSheafAdjunction.homEquiv _ N).trans
    ((etaleLowerShriekRestrictionAdjunction j).homEquiv F _)
  exact e.injective
    ((isZero_etaleRestriction_skyscraper_of_no_lift j η hη N).eq_of_tgt _ _)

/-- At a geometric point outside the open image, the original extension stalk is zero. -/
theorem isZero_etaleLowerShriek_stalk_of_not_mem
    (η : Spec (.of Ω) ⟶ X) (hη : η (default : Spec (.of Ω)) ∉ Set.range j)
    (F : AbelianSheaf.{u, u + 1} U) :
    IsZero ((pointSmallEtale η).sheafFiber.obj ((etaleLowerShriek j).obj F)) := by
  apply isZero_etaleLowerShriek_stalk_of_no_lift j η _ F
  intro ζ h
  apply hη
  refine ⟨ζ (default : Spec (.of Ω)), ?_⟩
  exact congrArg (fun f : Spec (.of Ω) ⟶ X => f (default : Spec (.of Ω))) h

end AlgebraicGeometry.Scheme.EtaleCohomology
