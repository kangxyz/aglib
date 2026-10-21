/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections

/-! # Original units of affine tilde restriction comparisons -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules

/-- A comparison with the original scalar-extension section map preserves the
original restriction unit on every coefficient. -/
theorem tildeRestriction_unit_of_sections
    {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
    (N : ModuleCat R) (P : ModuleCat S)
    (d : (tilde N).restrict (Spec.map φ) ⟶ tilde P)
    (e : (ModuleCat.extendScalars φ.hom).obj N ⟶ P)
    (hd : moduleSpecΓFunctor.map d ≫ ((tilde.toTildeΓNatIso (R := S)).app P).inv =
      (affineRestrictGlobalSectionsIso φ (tilde N)).inv ≫
        (ModuleCat.extendScalars φ.hom).map ((tilde.toTildeΓNatIso (R := R)).app N).inv ≫ e)
    (x : N) :
    ((tilde.toTildeΓNatIso (R := S)).app P).inv
      (moduleSpecΓFunctor.map d
        ((pushforwardGlobalSectionsIso φ).hom.app ((tilde N).restrict (Spec.map φ))
          (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (tilde N))
            (((tilde.toTildeΓNatIso (R := R)).app N).hom x)))) =
      e ((1 : S) ⊗ₜ[R,φ.hom] x) := by
  have hu := congrArg (fun q => q (((tilde.toTildeΓNatIso (R := R)).app N).hom x))
    (affineRestrictGlobalSectionsIso_unit φ (tilde N))
  change (affineRestrictGlobalSectionsIso φ (tilde N)).hom
    ((1 : S) ⊗ₜ[R,φ.hom] ((tilde.toTildeΓNatIso (R := R)).app N).hom x) = _ at hu
  have hs := congrArg (fun q => q
    ((pushforwardGlobalSectionsIso φ).hom.app ((tilde N).restrict (Spec.map φ))
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (tilde N))
        (((tilde.toTildeΓNatIso (R := R)).app N).hom x)))) hd
  simp only [ConcreteCategory.comp_apply] at hu hs
  erw [hs, ← hu, Iso.hom_inv_id_apply, ModuleCat.ExtendScalars.map_tmul,
    Iso.hom_inv_id_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules
