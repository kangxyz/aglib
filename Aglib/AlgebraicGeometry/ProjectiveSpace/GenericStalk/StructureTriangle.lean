/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Original generic-image fields through a structural triangle

The original structural triangle gives the actual function-field composition.
An isomorphism of the original intervening function fields propagates finite
base degree. These native calculations are extracted once from the actual
ProjectiveSurfaceChain consumer. No embedding, properness, normality,
Noetherianity or dimension hypothesis beyond the displayed maps is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] [IsDomain R]
  (ιX ιY : Type u) {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsDominant f]
  (iX : X ⟶ ProjectiveSpace R ιX) [IsDominant (iX ≫ toSpec R ιX)]
  (iY : Y ⟶ ProjectiveSpace R ιY) [IsDominant (iY ≫ toSpec R ιY)]
  (hb : iY ≫ toSpec R ιY = f ≫ (iX ≫ toSpec R ιX))

include hb in
/-- The original generic-image map respects the SAME structural triangle. -/
theorem genericImageBaseMap_eq_comp_of_structureTriangle :
    genericImageBaseMap R ιY iY =
      (Scheme.functionFieldMap f).comp (genericImageBaseMap R ιX iX) := by
  have hcongr {s t : Y ⟶ Spec (.of R)} [IsDominant s] [IsDominant t]
      (hst : s = t) : Scheme.functionFieldMap s = Scheme.functionFieldMap t := by
    subst t
    rfl
  change Scheme.functionFieldMap (iY ≫ toSpec R ιY) = _
  exact (hcongr hb).trans (Scheme.functionFieldMap_comp f (iX ≫ toSpec R ιX))

include hb in
/-- A genuine original field-map isomorphism transports finite generic base
extension through the SAME structural triangle. -/
theorem genericImageBaseMap_finite_of_structureTriangle
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hfin : (genericImageBaseMap R ιX iX).Finite) :
    (genericImageBaseMap R ιY iY).Finite := by
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := hff
  have hfinite : (Scheme.functionFieldMap f).Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (Scheme.functionFieldMap f))).2
  rw [genericImageBaseMap_eq_comp_of_structureTriangle R ιX ιY f iX iY hb]
  exact hfinite.comp hfin

end AlgebraicGeometry.ProjectiveSpace
