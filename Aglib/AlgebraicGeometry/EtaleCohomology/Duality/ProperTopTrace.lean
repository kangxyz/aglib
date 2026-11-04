/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSectionsEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! The original proper-curve trace on the top homology sheaf of the native direct image. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wX

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]

/-- Trace on the original second derived direct image of the roots of unity to the base. -/
@[no_expose]
def properCurveTopDirectImageTraceIso :
    let Λ := ULift.{u + 1} (ZMod n)
    (DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Base k) Λ) 2).obj
        ((moduleDerivedDirectImage Λ X.hom).obj
          ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj
            (moduleRootsOfUnity X.left n))) ≅ moduleUnit (Base k) Λ := by
  let R := ZMod n
  let Λ := ULift.{u + 1} R
  let S := Base k
  let D := ModuleSheaf S Λ
  let K := (moduleDerivedDirectImage Λ X.hom).obj
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj
      (moduleRootsOfUnity X.left n))
  let M := (DerivedCategory.Plus.homologyFunctor D 2).obj K
  let Γ := moduleGlobalSections S Λ
  let : HasExt.{u + 2} (ModuleSheaf X.left Λ) := SheafOfModules.hasExt (constantRing X.left Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X.left) := hasExtStandard X.left
  let e₀ := moduleFieldDirectImageHomologyAddEquiv k X.hom n (moduleRootsOfUnity X.left n) 2
  let e₁ := moduleRootsUnitExtCohomologyAddEquiv X.left n 2
  let e₂ := Curves.traceAddEquiv hX n hn hunit (modulePoint_globalLevelInvertible n hunit)
  let A := Γ.obj M
  let e : A ≃+ Λ := e₀.symm.trans (e₁.trans (e₂.trans AddEquiv.ulift.symm))
  let : Module Λ A := A.isModule
  let : Module R A := Module.compHom A (ULift.ringEquiv.symm : R ≃+* Λ).toRingHom
  let : Module R Λ := Module.compHom Λ (ULift.ringEquiv.symm : R ≃+* Λ).toRingHom
  let eL : A ≃ₗ[Λ] Λ := { e with
    map_smul' := fun a z => (e.toAddMonoidHom.toZModLinearMap n).map_smul a.down z }
  let τ : Γ.obj M ≅ ModuleCat.of Λ Λ := eL.toModuleIso
  let a := moduleGlobalSectionsAdjunction S Λ
  let : IsIso (a.unit.app (ModuleCat.of Λ Λ)) :=
    moduleFieldGlobalSectionsAdjunction_unit_isIso k Λ (ModuleCat.of Λ Λ)
  let u : ModuleCat.of Λ Λ ≅ Γ.obj (moduleUnit S Λ) :=
    asIso (a.unit.app (ModuleCat.of Λ Λ)) ≪≫ Γ.mapIso (moduleUnitConstantIso S Λ)
  let : Γ.IsEquivalence := by
    change (moduleGlobalSections (Base k) Λ).IsEquivalence
    rw [← moduleFieldSectionsEquivalence_inverse k Λ]
    infer_instance
  exact Γ.preimageIso (τ ≪≫ u)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wY

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]

local instance : HasExt.{u + 2} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n))) :=
  SheafOfModules.hasExt (constantRing Y.left (ULift.{u + 1} (ZMod n)))

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.left) := hasExtStandard Y.left

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original field trace on global sections has the original cohomology trace value. -/
theorem properCurveTopDirectImageTraceIso_hom_value
    (x : Ext.{u + 2} (moduleUnit Y.left (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity Y.left n) 2) :
    let Λ := ULift.{u + 1} (ZMod n)
    let Γ := moduleGlobalSections (Base k) Λ
    Γ.map (properCurveTopDirectImageTraceIso hY n hn hunit).hom
        (moduleFieldDirectImageHomologyAddEquiv k Y.hom n (moduleRootsOfUnity Y.left n) 2 x) =
      Γ.map (moduleUnitConstantIso (Base k) Λ).hom
        ((moduleGlobalSectionsAdjunction (Base k) Λ).unit.app (ModuleCat.of Λ Λ)
          (ULift.up (Curves.traceAddEquiv hY n hn hunit
            (modulePoint_globalLevelInvertible n hunit)
            (moduleRootsUnitExtCohomologyAddEquiv Y.left n 2 x)))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let Γ := moduleGlobalSections (Base k) Λ
  let e₀ := moduleFieldDirectImageHomologyAddEquiv k Y.hom n (moduleRootsOfUnity Y.left n) 2
  let e₁ := moduleRootsUnitExtCohomologyAddEquiv Y.left n 2
  let e₂ := Curves.traceAddEquiv hY n hn hunit (modulePoint_globalLevelInvertible n hunit)
  dsimp only
  unfold properCurveTopDirectImageTraceIso
  dsimp only
  rw [Functor.preimageIso_hom, Functor.map_preimage]
  change Γ.map (moduleUnitConstantIso (Base k) Λ).hom
      ((moduleGlobalSectionsAdjunction (Base k) Λ).unit.app (ModuleCat.of Λ Λ)
        (ULift.up (e₂ (e₁ (e₀.symm (e₀ x)))))) = _
  rw [e₀.symm_apply_apply]

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
