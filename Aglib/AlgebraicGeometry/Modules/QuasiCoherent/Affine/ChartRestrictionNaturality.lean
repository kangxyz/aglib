/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionGeneration
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.OpenRestrictionSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-! # Affine chart comparison squares from original section restrictions -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- A comparison square on nested affine charts is determined by the original
restriction-unit images of the larger chart's sections. -/
theorem affineChart_restriction_square_of_unit
    {X : Scheme.{u}} (U V : X.affineOpens) (h : V.val ≤ U.val)
    (M : X.Modules) (Q : (Spec Γ(X, U)).Modules) [Q.IsQuasicoherent]
    [IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op))]
    (f : Q ⟶ M.restrict U.property.fromSpec)
    (g : Q.restrict (Spec.map (X.presheaf.map (homOfLE h).op)) ⟶
      M.restrict V.property.fromSpec)
    (hs : ∀ m : moduleSpecΓFunctor.obj Q,
      (affineChartΓIso V M).hom (moduleSpecΓFunctor.map g
        ((((restrictAdjunction (Spec.map (X.presheaf.map (homOfLE h).op))).unit.app Q).app ⊤) m)) =
      M.presheaf.map (homOfLE h).op
        ((affineChartΓIso U M).hom (moduleSpecΓFunctor.map f m))) :
    (restrictFunctor (Spec.map (X.presheaf.map (homOfLE h).op))).map f ≫
        ((restrictFunctorComp (Spec.map (X.presheaf.map (homOfLE h).op))
          U.property.fromSpec).symm.app M ≪≫
          (restrictFunctorCongr (U.property.map_fromSpec V.property (homOfLE h).op)).app M).hom =
      g := by
  apply hom_eq_of_globalSections_eq
  apply (cancel_mono (affineChartΓIso V M).hom).1
  apply ModuleCat.hom_ext
  apply affineRestriction_linearMap_ext (X.presheaf.map (homOfLE h).op) Q
  intro m
  have hn := congrArg (fun q => q.app ⊤ m)
    ((restrictAdjunction (Spec.map (X.presheaf.map (homOfLE h).op))).unit.naturality f)
  change (((restrictAdjunction (Spec.map (X.presheaf.map (homOfLE h).op))).unit.app
      (M.restrict U.property.fromSpec)).app ⊤) (f.app ⊤ m) =
    (((restrictFunctor (Spec.map (X.presheaf.map (homOfLE h).op))).map f).app ⊤)
      ((((restrictAdjunction (Spec.map (X.presheaf.map (homOfLE h).op))).unit.app Q).app ⊤) m) at hn
  change (affineChartRestrictionSectionsIso U V (homOfLE h) M).hom
      ((((restrictFunctor (Spec.map (X.presheaf.map (homOfLE h).op))).map f).app ⊤)
        ((((restrictAdjunction (Spec.map (X.presheaf.map (homOfLE h).op))).unit.app Q).app ⊤)
          m)) = _
  rw [← hn, affineChartRestrictionSectionsIso_unit]
  exact (hs m).symm

end AlgebraicGeometry.Scheme.Modules
