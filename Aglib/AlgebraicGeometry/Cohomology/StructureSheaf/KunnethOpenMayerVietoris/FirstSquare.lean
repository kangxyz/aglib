/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.SourceEquations

/-! # The first square of the original mixed-open ladder -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u v r

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

open KunnethOpenMayerVietoris

namespace KunnethOpenMayerVietoris

/-- Evaluate the original preimage restriction pair with its actual mapped arrows. -/
private theorem presheaf_preimage_pair_value {R : Type r} [CommRing R]
    (Z T : Scheme.{u}) (f : Z ⟶ T) (P : Z.Opensᵒᵖ ⥤ ModuleCat.{v} R)
    (U V : T.Opens) (x : P.obj (op (f ⁻¹ᵁ (U ⊔ V)))) :
    (ModuleCat.biprodIsoProd (P.obj (op (f ⁻¹ᵁ U))) (P.obj (op (f ⁻¹ᵁ V)))).hom
        (biprod.lift
          (P.map (homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_left)).op)
          (P.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_right)).op) x) =
      ((P.map (((Opens.map f.base).map (homOfLE (le_sup_left : U ≤ U ⊔ V))).op)) x,
        (P.map (((Opens.map f.base).map (homOfLE (le_sup_right : V ≤ U ⊔ V))).op)) x) := by
  have hL : (Opens.map f.base).map (homOfLE (le_sup_left : U ≤ U ⊔ V)) =
      homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_left) :=
    Subsingleton.elim _ _
  have hR : (Opens.map f.base).map (homOfLE (le_sup_right : V ≤ U ⊔ V)) =
      homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_right) :=
    Subsingleton.elim _ _
  rw [hL, hR]
  exact Kunneth.MayerVietoris.biprodIsoProd_lift_value
    (P.obj (op (f ⁻¹ᵁ U))) (P.obj (op (f ⁻¹ᵁ V)))
    (P.obj (op (f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V)))
    (P.map (homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_left)).op)
    (P.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V from le_sup_right)).op) x

/-- The whole first restriction square uses only the original mixed restrictions. -/
theorem structureOpenKunnethMV_first_square (U V : Y.left.Opens) (n : ℕ) :
    (structureOpenMVFirst (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
        ((snd X Y).left ⁻¹ᵁ V) n).comp (structureOpenKunnethMap X Y (U ⊔ V) n) =
      (structureOpenMVMiddleMap X Y U V n).comp
        (structureOpenKunnethMVFirst X Y U V n) := by
  apply LinearMap.ext
  intro z
  apply (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))).injective
  have hU := LinearMap.congr_fun
    (structureOpenKunnethMap_restriction X Y (homOfLE (le_sup_left : U ≤ U ⊔ V)) n) z
  have hV := LinearMap.congr_fun
    (structureOpenKunnethMap_restriction X Y (homOfLE (le_sup_right : V ≤ U ⊔ V)) n) z
  have hB := presheaf_preimage_pair_value (X ⊗ Y).left Y.left (snd X Y).left
    (moduleHPrimePresheaf (X ⊗ Y).left (constants (X ⊗ Y))
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n) U V
    (structureOpenKunnethMap X Y (U ⊔ V) n z)
  have hSource := LinearMap.congr_fun
    (structureOpenMVMiddleSourceEquiv_first X Y U V n) z
  have hPair : structureOpenKunnethFirstPair X Y U V n z =
      (structureOpenKunnethRestriction X Y (homOfLE (le_sup_left : U ≤ U ⊔ V)) n z,
        structureOpenKunnethRestriction X Y (homOfLE (le_sup_right : V ≤ U ⊔ V)) n z) := rfl
  have hSourcePoint := hSource.trans hPair
  have hMap := congrArg
    (LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n))
    hSourcePoint
  have hMapValue :
      LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)
        (structureOpenKunnethRestriction X Y (homOfLE (le_sup_left : U ≤ U ⊔ V)) n z,
          structureOpenKunnethRestriction X Y (homOfLE (le_sup_right : V ≤ U ⊔ V)) n z) =
      (structureOpenKunnethMap X Y U n
          (structureOpenKunnethRestriction X Y (homOfLE (le_sup_left : U ≤ U ⊔ V)) n z),
        structureOpenKunnethMap X Y V n
          (structureOpenKunnethRestriction X Y (homOfLE (le_sup_right : V ≤ U ⊔ V)) n z)) := rfl
  have hRight := hMap.trans hMapValue
  let e := CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))
  have hMiddle := e.apply_symm_apply
    (LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)
      (structureOpenMVMiddleSourceEquiv X Y U V n (structureOpenKunnethMVFirst X Y U V n z)))
  have hMiddleNative : e (structureOpenMVMiddleMap X Y U V n
      (structureOpenKunnethMVFirst X Y U V n z)) =
      LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)
        (structureOpenMVMiddleSourceEquiv X Y U V n (structureOpenKunnethMVFirst X Y U V n z)) :=
    hMiddle
  have hLeft := hB.trans ((Prod.ext hU.symm hV.symm).trans hRight.symm)
  have hFinal := hLeft.trans hMiddleNative.symm
  exact hFinal

end KunnethOpenMayerVietoris

end AlgebraicGeometry.Scheme.Cohomology
