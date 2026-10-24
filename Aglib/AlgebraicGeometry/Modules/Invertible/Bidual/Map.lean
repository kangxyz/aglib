/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual

/-!
# Extending an original raw map to the actual bidual

The bidualization of an original sheaf map is natural for the original
evaluation morphism. A raw map to a genuine line therefore extends to the
actual source bidual through the inverse of the target evaluation.
Both internal-Hom maps and evaluation are the original native maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})
  {M N : SheafOfModules.{u} X.ringCatSheaf}

/-- Precompose twice using the actual internal-Hom map. -/
def doubleDualMap (h : M ⟶ N) :
    dualSheaf X (dualSheaf X M) ⟶ dualSheaf X (dualSheaf X N) :=
  InternalHom.map X
    (InternalHom.map X h (𝟙 (SheafOfModules.unit X.ringCatSheaf)))
    (𝟙 (SheafOfModules.unit X.ringCatSheaf))

/-- Original bidual evaluation is natural for this actual double-dual map. -/
theorem bidualMap_naturality (h : M ⟶ N) :
    bidualMap X M ≫ doubleDualMap X h = h ≫ bidualMap X N := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : InternalHom.RawHom X (dualSheaf X N)
    (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
  ext V ell
  change ell.val.app (op (Over.mk (𝟙 V.unop.left)))
      (h.val.app (op V.unop.left) (M.val.map V.unop.hom.op m)) =
    ell.val.app (op (Over.mk (𝟙 V.unop.left)))
      (N.val.map V.unop.hom.op (h.val.app U m))
  exact congrArg (ell.val.app (op (Over.mk (𝟙 V.unop.left))))
    (_root_.PresheafOfModules.naturality_apply h.val V.unop.hom.op m)

/-- Extend a constructed raw map to a genuine line using original biduality. -/
def extendToBidualLine (L : LineBundle X) (h : M ⟶ L.val) :
    dualSheaf X (dualSheaf X M) ⟶ L.val :=
  doubleDualMap X h ≫ (bidualIso X L).inv

/-- The extension agrees with the given raw map through original evaluation. -/
theorem extendToBidualLine_evaluation (L : LineBundle X) (h : M ⟶ L.val) :
    bidualMap X M ≫ extendToBidualLine X L h = h := by
  change bidualMap X M ≫ (doubleDualMap X h ≫ (bidualIso X L).inv) = h
  calc
    bidualMap X M ≫ (doubleDualMap X h ≫ (bidualIso X L).inv) =
        (bidualMap X M ≫ doubleDualMap X h) ≫ (bidualIso X L).inv :=
      (Category.assoc _ _ _).symm
    _ = (h ≫ bidualMap X L.val) ≫ (bidualIso X L).inv :=
      congrArg (fun a => a ≫ (bidualIso X L).inv) (bidualMap_naturality X h)
    _ = h ≫ (bidualMap X L.val ≫ (bidualIso X L).inv) := Category.assoc _ _ _
    _ = h ≫ 𝟙 L.val :=
      congrArg (fun a => h ≫ a) (Iso.hom_inv_id (bidualIso X L))
    _ = h := Category.comp_id h

end AlgebraicGeometry.Scheme.Modules.Invertible
