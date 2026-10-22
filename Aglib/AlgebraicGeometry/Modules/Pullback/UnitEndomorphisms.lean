/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Pulling back actual scalar coordinates

Conjugation by the native pullback-unit comparison preserves composition of
scheme pullbacks. On affine schemes it takes literal multiplication by `a`
to literal multiplication by its image, including over nonreduced rings.
These equations retain the actual maps needed for projective agreement on a
prescribed principal open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The actual scalar-coordinate map under pullback and its canonical unit
comparison. -/
def pullbackUnitEnd (f : X ⟶ Y)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom

/-- Pulling a scalar coordinate through two scheme morphisms is exactly the
pullback through their composite, with all native unit comparisons retained. -/
theorem pullbackUnitEnd_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : SheafOfModules.unit Z.ringCatSheaf ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    pullbackUnitEnd (f ≫ g) a = pullbackUnitEnd f (pullbackUnitEnd g a) := by
  have hn := (pullbackComp f g).hom.naturality a
  simp only [Functor.comp_map] at hn
  have hu : (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
        (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    simp only [Category.assoc]
    rw [pullbackUnitIso_comp]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  symm
  simp only [pullbackUnitEnd, Functor.map_comp, Category.assoc]
  rw [← pullbackUnitIso_comp f g, reassoc_of% hn, reassoc_of% hu]

end AlgebraicGeometry.Scheme.Modules
