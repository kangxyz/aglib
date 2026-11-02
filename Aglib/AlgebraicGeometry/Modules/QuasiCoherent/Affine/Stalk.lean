/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Original affine sections and actual module stalks

The original tilde stalk map, its localization property, and the affine
counit germ formula are extracted from the finite-source closed-adjoint
stalk comparison. Only naturality and the explicit original scalar-germ
equation are added. No replacement module or localization is chosen.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual stalk map induced by a tilde comparison, with the original
structure-stalk scalar action. -/
public def tildeIsoToModuleStalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {N : (Spec R).Modules} (e : tilde M ≅ N) (x : PrimeSpectrum R) :
    M ⟶ (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
      ((moduleStalk (Spec R) x).obj N) :=
  tilde.toStalk M x ≫
    (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).map
      ((moduleStalk (Spec R) x).map e.hom)

public theorem tildeIsoToModuleStalk_isLocalized {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) {N : (Spec R).Modules} (e : tilde M ≅ N)
    (x : PrimeSpectrum R) :
    IsLocalizedModule x.asIdeal.primeCompl (tildeIsoToModuleStalk M e x).hom :=
  IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl (tilde.toStalk M x).hom
    (((ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).mapIso
      ((moduleStalk (Spec R) x).mapIso e)).toLinearEquiv)

/-- Ambient coefficient sections map to their actual stalk by the
tilde counit and the original germ. -/
public def affineSectionsToStalk {R : CommRingCat.{u}} (N : (Spec R).Modules)
    (x : PrimeSpectrum R) :
    (moduleSpecΓFunctor (R := R)).obj N ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
        ((moduleStalk (Spec R) x).obj N) :=
  tilde.toStalk ((moduleSpecΓFunctor (R := R)).obj N) x ≫
    (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).map
      ((moduleStalk (Spec R) x).map (fromTildeΓ (R := R) N))

public theorem affineSectionsToStalk_isLocalized {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent] (x : PrimeSpectrum R) :
    IsLocalizedModule x.asIdeal.primeCompl (affineSectionsToStalk N x).hom := by
  let e : tilde ((moduleSpecΓFunctor (R := R)).obj N) ≅ N :=
    @asIso _ _ _ _ (fromTildeΓ (R := R) N)
      (isIso_fromTildeΓ_of_isQuasicoherent (R := R) N)
  exact tildeIsoToModuleStalk_isLocalized (R := R) _ e x

@[simp]
public theorem affineSectionsToStalk_apply {R : CommRingCat.{u}}
    (N : (Spec R).Modules) (x : PrimeSpectrum R)
    (s : (moduleSpecΓFunctor (R := R)).obj N) :
    affineSectionsToStalk N x s = N.presheaf.germ ⊤ x trivial s := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
    (X := (Spec R : TopCat.{u})) x).map
    (fromTildeΓ (R := R) N).mapPresheaf
    ((tilde ((moduleSpecΓFunctor (R := R)).obj N)).presheaf.germ ⊤ x trivial
      (tilde.toOpen (R := R) ((moduleSpecΓFunctor (R := R)).obj N) ⊤ s)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  let G := (modulesSpecToSheaf (R := R)).obj N
  have hi : (homOfLE (show (⊤ : (Spec R).Opens) ≤ ⊤ from le_rfl)).op =
      𝟙 (Opposite.op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
  have h₀ := (toOpen_fromTildeΓ_app (R := R) N ⊤).trans
    ((congrArg G.obj.map hi).trans (G.obj.map_id _))
  have h := ConcreteCategory.congr_hom h₀ s
  change ((fromTildeΓ (R := R) N).mapPresheaf.app (Opposite.op ⊤))
    (tilde.toOpen (R := R) ((moduleSpecΓFunctor (R := R)).obj N) ⊤ s) = s at h
  exact h

/-- Native affine stalk scalars are exactly the original top ring germ. -/
theorem affineSectionsToStalk_scalar (R : CommRingCat.{u}) (x : Spec R) :
    StructureSheaf.toStalk R x =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial := rfl

/-- The original affine germ commutes with the actual induced module stalk map. -/
theorem affineSectionsToStalk_naturality {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) (x : Spec R) :
    moduleSpecΓFunctor.map f ≫ affineSectionsToStalk N x =
      affineSectionsToStalk M x ≫
        (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).map
          ((moduleStalk (Spec R) x).map f) := by
  ext s
  change affineSectionsToStalk N x (moduleSpecΓFunctor.map f s) =
    (moduleStalk (Spec R) x).map f (affineSectionsToStalk M x s)
  refine (affineSectionsToStalk_apply N x (moduleSpecΓFunctor.map f s)).trans ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
    f.mapPresheaf s).symm.trans ?_
  exact congrArg ((moduleStalk (Spec R) x).map f)
    (affineSectionsToStalk_apply M x s).symm

end AlgebraicGeometry.Scheme.Modules
