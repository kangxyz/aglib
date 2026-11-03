/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum

/-!
# Naturality of the original local-spectrum section and stalk comparisons

The natural isomorphisms below have the already constructed component maps:
the original closed-point germ and the original scalar-extension unit followed
by inverse pullback-stalk and inverse germ comparisons. No quasicoherence,
finite type, properness or finite map from an initial base is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing closed-point germ equivalences are natural on all module sheaves. -/
def localSpectrumSectionsStalkNatIso (R : CommRingCat.{u}) [IsLocalRing R] :
    moduleSpecΓFunctor ≅ moduleStalk (Spec R) (closedPoint R) ⋙
      ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom :=
  NatIso.ofComponents (localSpectrumSectionsStalkIso R) (by
    intro M N f
    exact localSpectrumSectionsToStalk_naturality R f)

/-- Naturality retains precisely the previously constructed original germ component. -/
@[simp]
theorem localSpectrumSectionsStalkNatIso_app (R : CommRingCat.{u}) [IsLocalRing R]
    (M : (Spec R).Modules) :
    (localSpectrumSectionsStalkNatIso R).app M = localSpectrumSectionsStalkIso R M := rfl

/-- The original stalk/pullback-sections component construction is natural.
This is the same scalar unit and same two comparison maps, with their actual
functor associators inserted. -/
def stalkFromSpecStalkSectionsNatIso (Y : Scheme.{u}) (y : Y) :
    moduleStalk Y y ≅ pullback (Y.fromSpecStalk y) ⋙ moduleSpecΓFunctor := by
  let R := Y.presheaf.stalk y
  let σ := (stalkClosedPointIso R).inv.hom
  let P := pullback (Y.fromSpecStalk y)
  let S := moduleStalk (Spec R) (closedPoint R)
  let H := moduleStalk Y y
  let E := ModuleCat.extendScalars σ
  let Q := ModuleCat.restrictScalars σ
  letI : Q.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    ((stalkClosedPointIso R).symm.commRingCatIsoToRingEquiv)
  exact (Functor.rightUnitor H).symm ≪≫
    Functor.isoWhiskerLeft H (asIso (ModuleCat.extendRestrictScalarsAdj σ).unit) ≪≫
    (Functor.associator H E Q).symm ≪≫
    Functor.isoWhiskerRight (fromSpecStalkPullbackStalkIso Y y).symm Q ≪≫
    Functor.associator P S Q ≪≫
    Functor.isoWhiskerLeft P (localSpectrumSectionsStalkNatIso R).symm

/-- The forward component is exactly the original local-spectrum comparison,
not just another isomorphism between its endpoints. -/
@[simp]
theorem stalkFromSpecStalkSectionsNatIso_hom_app (Y : Scheme.{u}) (y : Y)
    (M : Y.Modules) :
    (stalkFromSpecStalkSectionsNatIso Y y).hom.app M =
      (stalkFromSpecStalkSectionsIso Y y M).hom := by
  simp only [stalkFromSpecStalkSectionsNatIso, stalkFromSpecStalkSectionsIso,
    closedPointScalarExtensionUnitIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.comp_obj,
    Category.id_comp, localSpectrumSectionsStalkNatIso, Functor.mapIso_hom]
  rfl

/-- Every original coefficient morphism commutes with the actual stalk to
local-spectrum sections map, with the original scalar actions. -/
@[reassoc]
theorem stalkFromSpecStalkSectionsIso_naturality (Y : Scheme.{u}) (y : Y)
    {M N : Y.Modules} (f : M ⟶ N) :
    (moduleStalk Y y).map f ≫ (stalkFromSpecStalkSectionsIso Y y N).hom =
      (stalkFromSpecStalkSectionsIso Y y M).hom ≫
        moduleSpecΓFunctor.map ((pullback (Y.fromSpecStalk y)).map f) := by
  simpa only [stalkFromSpecStalkSectionsNatIso_hom_app, Functor.comp_map] using
    (stalkFromSpecStalkSectionsNatIso Y y).hom.naturality f

end AlgebraicGeometry.Scheme.Modules
