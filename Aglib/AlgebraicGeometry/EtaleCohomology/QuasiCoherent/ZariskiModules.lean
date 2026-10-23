/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.CoefficientMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiAdjunction
public import Aglib.AlgebraicGeometry.Descent.Modules.RestrictPullback
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic

/-! # Original module sections on open étale charts

The components use the native restriction/pullback comparison and the original
module presheaf. No affine tensor formula is used on a general open chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Inverse coherence of the native restriction/pullback comparison. -/
theorem restrictPullback_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (pullbackComp f g).hom.app M ≫ (restrictFunctorIsoPullback (f ≫ g)).inv.app M =
      (restrictFunctorIsoPullback f).inv.app ((pullback g).obj M) ≫
        (Scheme.Modules.restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app M) ≫
          (restrictFunctorComp f g).inv.app M := by
  have h : (restrictFunctorIsoPullback (f ≫ g)).app M ≪≫
      ((pullbackComp f g).app M).symm =
      (restrictFunctorComp f g).app M ≪≫
        (Scheme.Modules.restrictFunctor f).mapIso ((restrictFunctorIsoPullback g).app M) ≪≫
          (restrictFunctorIsoPullback f).app ((pullback g).obj M) :=
    Iso.ext (restrictFunctorIsoPullback_comp_hom_app f g M)
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Category.assoc] using congrArg Iso.inv h

/-- Equality transport also commutes with the original inverse comparison. -/
theorem restrictPullback_congr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    (pullbackCongr h).hom.app M ≫ (restrictFunctorIsoPullback g).inv.app M =
      (restrictFunctorIsoPullback f).inv.app M ≫ (restrictFunctorCongr h).hom.app M := by
  apply (cancel_epi ((restrictFunctorIsoPullback f).hom.app M)).mp
  rw [← Category.assoc, restrictFunctorIsoPullback_congr_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.hom_inv_id_app_assoc]

/-- On an open chart, pullback sections are the original module's sections on that open. -/
def openPullbackSectionsIso (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) :
    Γ((pullback U.ι).obj F, ⊤) ≅ Γ(F, U) :=
  ((Scheme.Modules.toPresheaf U.toScheme).mapIso
      ((restrictFunctorIsoPullback U.ι).app F).symm).app (op ⊤) ≪≫
    F.restrictAppIso U.ι ⊤ ≪≫ F.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- The underlying section formula uses the original module isomorphism and open equality. -/
theorem openPullbackSectionsIso_hom_apply (X : Scheme.{u}) (F : X.Modules) (U : X.Opens)
    (s : Γ((pullback U.ι).obj F, ⊤)) :
    (openPullbackSectionsIso X F U).hom s =
      F.presheaf.map (eqToHom U.ι_image_top.symm).op
        (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app F) ⊤ s) := by
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
