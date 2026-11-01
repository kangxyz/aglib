/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteStalkProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Original module sections over finite strictly local bases

The original linear restriction fan is reflected through scalar forgetting.
Its component germs give the actual module stalk product, including an empty
index set. Base, algebra and coefficient-ring universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Constructible.Modules

universe u v r

variable (R : Type r) [CommRing R]
  (A : Type v) [CommRing A] (B : Type u) [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A]

local instance moduleFiniteStalkLimits :
    HasLimitsOfSize.{v, v} (ModuleCat.{v + 1} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, v + 1, r}

/-- The actual module-valued geometric stalk of a local component. -/
abbrev localComponentModuleStalk (F : ModuleSheaf R (Spec (.of A)))
    (p : MaximalSpectrum A) : ModuleCat.{v + 1} R :=
  (localComponentClosedPoint A B p).presheafFiber.obj F.obj

/-- The original linear component germ is invertible by its underlying germ. -/
def localComponentModuleStalkIso (F : ModuleSheaf R (Spec (.of A)))
    (p : MaximalSpectrum A) :
    F.obj.obj (op (localComponentEtale A B p)) ≅ localComponentModuleStalk R A B F p := by
  let U := forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1}
  let : PreservesColimitsOfSize.{v, v} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{v + 1, r, v, v} R
  let : PreservesFilteredColimitsOfSize.{v, v} U := ⟨fun _ _ _ => inferInstance⟩
  let := HenselianLocalRing.henselian_localizationAtPrime B A p.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A p.asIdeal
  let := localComponentInclusion_isOpenImmersion A B p
  let Φ := localComponentClosedPoint A B p
  let x := openComponentFiberPoint (Localization.AtPrime p.asIdeal) (localComponentInclusion A p)
  let := openComponent_germ_isIso (Localization.AtPrime p.asIdeal)
    (localComponentInclusion A p) (F.obj ⋙ U)
  have : IsIso (U.map (Φ.toPresheafFiber (localComponentEtale A B p) x F.obj)) := by
    rw [← Φ.toPresheafFiber_presheafFiberCompIso_hom_app U]
    infer_instance
  let := isIso_of_reflects_iso (Φ.toPresheafFiber (localComponentEtale A B p) x F.obj) U
  exact asIso (Φ.toPresheafFiber (localComponentEtale A B p) x F.obj)

/-- The literal module restriction fan is limiting. -/
def localComponentModuleSectionsFanIsLimit (F : ModuleSheaf R (Spec (.of A))) :
    IsLimit (Fan.mk (F.obj.obj (op (StrictlyLocal.terminalObject A)))
      (fun p : MaximalSpectrum A => F.obj.map (localComponentArrow A B p).op)) := by
  apply isLimitOfReflects (forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1})
  apply (Fan.isLimitMapConeEquiv
    (forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1}) _ _).symm.toFun
  exact localComponentSectionsFanIsLimit A B ((moduleUnderlying R (Spec (.of A))).obj F)

/-- Original module sections are the finite product of the actual component stalks. -/
def finiteModuleStalkProductIso (F : ModuleSheaf R (Spec (.of A))) :
    F.obj.obj (op (StrictlyLocal.terminalObject A)) ≅
      ∏ᶜ fun p : MaximalSpectrum A => localComponentModuleStalk R A B F p :=
  (localComponentModuleSectionsFanIsLimit R A B F).conePointUniqueUpToIso
    (productIsProduct _) ≪≫ Limits.Pi.mapIso (localComponentModuleStalkIso R A B F)

/-- Every projection is the original restriction followed by its original germ. -/
@[reassoc (attr := simp)]
theorem finiteModuleStalkProductIso_hom_π (F : ModuleSheaf R (Spec (.of A)))
    (p : MaximalSpectrum A) :
    (finiteModuleStalkProductIso R A B F).hom ≫
      Pi.π (fun p => localComponentModuleStalk R A B F p) p =
        F.obj.map (localComponentArrow A B p).op ≫
          (localComponentModuleStalkIso R A B F p).hom := by
  change (_ ≫ (Limits.Pi.mapIso (localComponentModuleStalkIso R A B F)).hom) ≫ _ = _
  rw [Category.assoc, Limits.Pi.mapIso_hom_π, ← Category.assoc]
  exact congrArg (fun k => k ≫ (localComponentModuleStalkIso R A B F p).hom)
    ((localComponentModuleSectionsFanIsLimit R A B F).conePointUniqueUpToIso_hom_comp
      (productIsProduct _) ⟨p⟩)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
