/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.PointSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The exact original residue-point ideal on affine opens

The native kernel ideal is the actual affine chart prime, not merely an ideal
with the same support. The point morphism is quasi-compact because its original
source is a singleton. The original app/appLE restriction and Spec comparison
are retained as explicit injective maps. No global instance is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- On an actual affine neighbourhood, the original residue-point kernel is its chart prime. -/
theorem fromSpecResidueField_ker_ideal {X : Scheme.{u}}
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    (X.fromSpecResidueField x).ker.ideal U =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let j := X.fromSpecResidueField x
  let : QuasiCompact j := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have hpre : (⊤ : (Spec (X.residueField x)).Opens) ≤ j ⁻¹ᵁ U.1 :=
    residueRestriction_le x U.1 hx
  let : IsIso (homOfLE hpre) :=
    homOfLE_isIso_of_eq hpre (le_antisymm hpre le_top)
  have hr : Function.Injective
      ((Spec (X.residueField x)).presheaf.map (homOfLE hpre).op).hom :=
    (ConcreteCategory.bijective_of_isIso
      ((Spec (X.residueField x)).presheaf.map (homOfLE hpre).op)).injective
  have hGamma : Function.Injective (Scheme.ΓSpecIso (X.residueField x)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (X.residueField x)).inv).injective
  calc
    j.ker.ideal U = RingHom.ker (j.app U.1).hom := j.ker_apply U
    _ = RingHom.ker (j.appLE U.1 ⊤ hpre).hom :=
      (RingHom.ker_comp_of_injective (j.app U.1).hom hr).symm
    _ = RingHom.ker ((X.evaluation U.1 x hx) ≫
        (Scheme.ΓSpecIso (X.residueField x)).inv).hom := by
      apply congrArg (fun φ : Γ(X, U) ⟶ Γ(Spec (X.residueField x), ⊤) =>
        RingHom.ker φ.hom)
      simpa only [Scheme.evaluation, Category.assoc] using residuePoint_appLE x U.1 hx
    _ = RingHom.ker (X.evaluation U.1 x hx).hom :=
      RingHom.ker_comp_of_injective (X.evaluation U.1 x hx).hom hGamma
    _ = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := ker_evaluation_eq_primeIdealOf x U hx

/-- The same point-centre ideal restricts along the original principal-open section map. -/
theorem fromSpecResidueField_ker_ideal_basicOpen {X : Scheme.{u}}
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) (f : Γ(X, U)) :
    (X.fromSpecResidueField x).ker.ideal (X.affineBasicOpen f) =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
  rw [← (X.fromSpecResidueField x).ker.map_ideal_basicOpen U f,
    fromSpecResidueField_ker_ideal x U hx]

end AlgebraicGeometry.Scheme
