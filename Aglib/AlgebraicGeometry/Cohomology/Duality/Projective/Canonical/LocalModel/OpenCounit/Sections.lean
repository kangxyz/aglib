/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Localization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction.Counit
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-!
# The original affine open-section map and the tilde counit

The original restriction unit, followed by an arbitrary actual coefficient
arrow, has the original scalar-adjunction mate. The tilde counit of that mate
is the original restriction of the source counit followed by the same arrow.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (ψ : R ⟶ S) [IsOpenImmersion (Spec.map ψ)]

/-- The actual affine open-section map transposes to the original tilde/restriction
counit square for arbitrary source and target module sheaves. -/
theorem affineOpenRestrictionSectionsMap_counit
    (P : (Spec R).Modules) (Q : (Spec S).Modules) (k : P.restrict (Spec.map ψ) ⟶ Q) :
    let T := affineOpenRestrictionSectionsMap ψ P ≫
      (ModuleCat.restrictScalars ψ.hom).map (moduleSpecΓFunctor.map k)
    let D := ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv
      (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm T
    (tilde.functor S).map D ≫ Q.fromTildeΓ =
      (tildePullbackIso ψ).inv.app (moduleSpecΓFunctor.obj P) ≫
        (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
          (tilde (moduleSpecΓFunctor.obj P)) ≫
        (restrictFunctor (Spec.map ψ)).map P.fromTildeΓ ≫ k := by
  let k' := (restrictFunctorIsoPullback (Spec.map ψ)).inv.app P ≫ k
  let T := affineOpenRestrictionSectionsMap ψ P ≫
    (ModuleCat.restrictScalars ψ.hom).map (moduleSpecΓFunctor.map k)
  let u := moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction (Spec.map ψ)).unit.app P ≫
        (pushforward (Spec.map ψ)).map k') ≫
    (pushforwardGlobalSectionsIso ψ).hom.app Q
  have hmate : (pullbackPushforwardAdjunction (Spec.map ψ)).unit.app P ≫
        (pushforward (Spec.map ψ)).map k' =
      (restrictAdjunction (Spec.map ψ)).unit.app P ≫
        (pushforward (Spec.map ψ)).map k := by
    dsimp only [k']
    rw [Functor.map_comp, ← Category.assoc,
      restrictFunctorIsoPullback_inv_adjunction_unit]
  have hn := (pushforwardGlobalSectionsIso ψ).hom.naturality k
  simp only [Functor.comp_map] at hn
  have hT : T = u := by
    dsimp only [T, u, affineOpenRestrictionSectionsMap]
    rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, ← hmate]
  have hc := tildePullbackIso_counit ψ P Q k'
  change (tilde.functor S).map
      (((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv
        (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm u) ≫ Q.fromTildeΓ =
    (tildePullbackIso ψ).inv.app (moduleSpecΓFunctor.obj P) ≫
      (pullback (Spec.map ψ)).map P.fromTildeΓ ≫ k' at hc
  change (tilde.functor S).map
      (((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv
        (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm T) ≫ Q.fromTildeΓ = _
  rw [hT]
  refine hc.trans ?_
  have hnat : (pullback (Spec.map ψ)).map P.fromTildeΓ ≫
        (restrictFunctorIsoPullback (Spec.map ψ)).inv.app P =
      (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
          (tilde (moduleSpecΓFunctor.obj P)) ≫
        (restrictFunctor (Spec.map ψ)).map P.fromTildeΓ :=
    (restrictFunctorIsoPullback (Spec.map ψ)).inv.naturality P.fromTildeΓ
  simpa only [k', Category.assoc, Functor.comp_obj] using congrArg
    (fun z => (tildePullbackIso ψ).inv.app (moduleSpecΓFunctor.obj P) ≫ z ≫ k) hnat

end AlgebraicGeometry.Scheme.Modules
