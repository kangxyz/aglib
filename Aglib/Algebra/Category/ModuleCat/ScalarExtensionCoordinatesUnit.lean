/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinates

/-! # Original scalar-extension units in specified coordinates -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
namespace ModuleCat
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {M N : ModuleCat.{u} R} {P : ModuleCat.{u} S}
  (d : (extendScalars (algebraMap R S)).obj M ≅ P) (e : M ≅ N)

/-- The coordinate comparison preserves the actual adjunction unit as a morphism. -/
theorem scalarExtensionCoordinatesIso_unit :
    (extendRestrictScalarsAdj (algebraMap R S)).unit.app N ≫
      (restrictScalars (algebraMap R S)).map
        ((extendScalarsAlgebraIso R S N).hom ≫
          (scalarExtensionCoordinatesIso d e).inv) =
    e.inv ≫ (extendRestrictScalarsAdj (algebraMap R S)).unit.app M ≫
      (restrictScalars (algebraMap R S)).map d.hom := by
  have h := congrArg
    (fun k => k ≫ (restrictScalars (algebraMap R S)).map d.hom)
    ((extendRestrictScalarsAdj (algebraMap R S)).unit.naturality e.inv).symm
  simpa only [scalarExtensionCoordinatesIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp,
    Functor.comp_map, Functor.id_map] using h

end ModuleCat
