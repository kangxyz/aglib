/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.UnitEndRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SepClosedConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange

/-! Descent of original represented coefficient morphisms from a connected scheme. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Spec (.of k))
  (H K : Grp (Over (Spec (.of k)))) [IsCommMonObj H.X] [IsCommMonObj K.X]
  [IsFinite H.X.hom] [Etale H.X.hom] [Etale K.X.hom]
  (hH : IsAddTorsion ((globalSections (Spec (.of k))).obj (representedSheaf H)))
  (hK : IsAddTorsion ((globalSections (Spec (.of k))).obj (representedSheaf K)))

/-- Every homomorphism of the actual pulled-back represented coefficients
descends uniquely to a group homomorphism over the original field. -/
def representedPullbackHomEquiv :
    (H ⟶ K) ≃ (representedSheaf (baseChangedGroup p H) ⟶ representedSheaf (baseChangedGroup p K)) :=
  let F := inverseImage p
  let A := (globalSections (Spec (.of k))).obj (representedSheaf H)
  let B := (globalSections (Spec (.of k))).obj (representedSheaf K)
  let e := fieldTorsionConstantIso k (representedSheaf H) hH
  let d := fieldTorsionConstantIso k (representedSheaf K) hK
  let E := Equiv.ofBijective (fun (g : representedSheaf H ⟶ representedSheaf K) => F.map g)
    (inverseImage_map_bijective_of_constantIso p A B hK e d)
  (representedSheafHomEquiv H K).trans (E.trans
    ((representedSheafBaseChangeIso p H).homCongr (representedSheafBaseChangeIso p K)))

/-- The descent equivalence uses the literal original represented pullback map. -/
theorem representedPullbackHomEquiv_apply (g : H ⟶ K) :
    representedPullbackHomEquiv k p H K hH hK g =
      representedSheafMap ((Over.pullback p).mapGrp.map g) := by
  let e := representedSheafBaseChangeIso p H
  let d := representedSheafBaseChangeIso p K
  change e.inv ≫ (inverseImage p).map (representedSheafMap g) ≫ d.hom = _
  rw [representedSheafBaseChangeIso_naturality p g, e.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
