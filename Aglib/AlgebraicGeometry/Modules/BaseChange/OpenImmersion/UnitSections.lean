/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.AffineUnits

/-! # Native section carriers for affine restriction units -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The original restriction-unit section, with its native target carrier. -/
def affineRestrictionUnitSection {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsOpenImmersion (Spec.map φ)] (M : (Spec R).Modules)
    (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) :=
  (pushforwardGlobalSectionsIso φ).hom.app (M.restrict (Spec.map φ))
    (((restrictAdjunction (Spec.map φ)).unit.app M).app ⊤ x)

/-- The original base-change unit equality with both section carriers fixed
before coefficient specialization. -/
theorem cartesianOpenBaseChange_affine_unit_inverse
    {R S R' S' : CommRingCat.{u}} (pU : R ⟶ S) (pV : R' ⟶ S')
    (φ : R ⟶ R') (ψ : S ⟶ S')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU) (Spec.map φ))
    (M : (Spec S).Modules) (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map
      ((cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
        (Spec.map φ) H).hom.app M)
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app
        ((pushforward (Spec.map pU)).obj M))
        ((pushforwardGlobalSectionsIso pU).inv.app M x)) =
    (pushforwardGlobalSectionsIso pV).inv.app (M.restrict (Spec.map ψ))
      (affineRestrictionUnitSection ψ M x) := by
  have h := congrArg
    ((pushforwardGlobalSectionsIso pV).inv.app (M.restrict (Spec.map ψ)))
      (cartesianOpenBaseChange_affine_unit pU pV φ ψ H M x)
  simp only [← Iso.app_hom, ← Iso.app_inv, Iso.hom_inv_id_apply] at h
  exact h

/-- The original pushed coefficient map evaluated on an original restriction unit. -/
def pushforwardRestrictionUnitSection
    {R S T : CommRingCat.{u}} (p : R ⟶ T) (ψ : S ⟶ T)
    [IsOpenImmersion (Spec.map ψ)] (M : (Spec S).Modules) (N : (Spec T).Modules)
    (d : M.restrict (Spec.map ψ) ⟶ N) (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.obj ((pushforward (Spec.map p)).obj N) :=
  moduleSpecΓFunctor.map ((pushforward (Spec.map p)).map d)
    ((pushforwardGlobalSectionsIso p).inv.app (M.restrict (Spec.map ψ))
      (affineRestrictionUnitSection ψ M x))

/-- The actual pushforward section comparison preserves the evaluated map. -/
theorem pushforwardRestrictionUnitSection_sections
    {R S T : CommRingCat.{u}} (p : R ⟶ T) (ψ : S ⟶ T)
    [IsOpenImmersion (Spec.map ψ)] (M : (Spec S).Modules) (N : (Spec T).Modules)
    (d : M.restrict (Spec.map ψ) ⟶ N) (x : moduleSpecΓFunctor.obj M) :
    (pushforwardGlobalSectionsIso p).hom.app N
      (pushforwardRestrictionUnitSection p ψ M N d x) =
      moduleSpecΓFunctor.map d (affineRestrictionUnitSection ψ M x) := by
  have h := congrArg (fun q => q
    ((pushforwardGlobalSectionsIso p).inv.app (M.restrict (Spec.map ψ))
      (affineRestrictionUnitSection ψ M x)))
    ((pushforwardGlobalSectionsIso p).hom.naturality d)
  simp only [Functor.comp_map, ConcreteCategory.comp_apply] at h
  dsimp only [pushforwardRestrictionUnitSection]
  erw [h]

/-- The original base-change and pushed coefficient maps evaluate to the same
native section, without rebuilding a scalar-restriction carrier. -/
theorem cartesianOpenBaseChange_pushforwardRestrictionUnitSection
    {R S R' S' : CommRingCat.{u}} (pU : R ⟶ S) (pV : R' ⟶ S')
    (φ : R ⟶ R') (ψ : S ⟶ S')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU) (Spec.map φ))
    (M : (Spec S).Modules) (N : (Spec S').Modules)
    (d : M.restrict (Spec.map ψ) ⟶ N) (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((pushforward (Spec.map pV)).map d)
      (moduleSpecΓFunctor.map
      ((cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
        (Spec.map φ) H).hom.app M)
      (((restrictAdjunction (Spec.map φ)).unit.app
        ((pushforward (Spec.map pU)).obj M)).app ⊤
        ((pushforwardGlobalSectionsIso pU).inv.app M x))) =
    pushforwardRestrictionUnitSection pV ψ M N d x := by
  change moduleSpecΓFunctor.map ((pushforward (Spec.map pV)).map d)
    (moduleSpecΓFunctor.map
      ((cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
        (Spec.map φ) H).hom.app M)
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app
        ((pushforward (Spec.map pU)).obj M))
        ((pushforwardGlobalSectionsIso pU).inv.app M x))) = _
  dsimp only [pushforwardRestrictionUnitSection]
  rw [cartesianOpenBaseChange_affine_unit_inverse]

end AlgebraicGeometry.Scheme.Modules
