/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.SourceEquations

/-! # The difference square of the original mixed-open ladder -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u v r a b c d

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

open KunnethOpenMayerVietoris

namespace KunnethOpenMayerVietoris

/-- Normalize the original preimage difference over a variable original presheaf. -/
private theorem presheaf_preimage_difference {R : Type r} [CommRing R]
    (Z T : Scheme.{u}) (f : Z ⟶ T) (P : Z.Opensᵒᵖ ⥤ ModuleCat.{v} R)
    (U V : T.Opens) :
    (biprod.desc
      (P.map (homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from inf_le_left)).op)
      (-(P.map (homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from inf_le_right)).op))).hom =
    (biprod.desc
      (P.map (((Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))).op))
      (-(P.map (((Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))).op)))).hom := by
  have hL : (Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)) =
      homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from inf_le_left) :=
    Subsingleton.elim _ _
  have hR : (Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)) =
      homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from inf_le_right) :=
    Subsingleton.elim _ _
  simp only [hL, hR]

/-- Complete the original difference square while its presheaf and middle map are variable. -/
private theorem presheaf_preimage_difference_square {R : Type r} [CommRing R]
    (Z T : Scheme.{u}) (f : Z ⟶ T) (P : Z.Opensᵒᵖ ⥤ ModuleCat.{v} R)
    (U V : T.Opens) {D : Type d} {A : Type a} {B : Type b} {I : Type c}
    [AddCommGroup D] [Module R D] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup I] [Module R I]
    (e : D ≃ₗ[R] A × B)
    (fU : A →ₗ[R] P.obj (op (f ⁻¹ᵁ U))) (fV : B →ₗ[R] P.obj (op (f ⁻¹ᵁ V)))
    (fI : I →ₗ[R] P.obj (op (f ⁻¹ᵁ (U ⊓ V)))) (a : A →ₗ[R] I) (b : B →ₗ[R] I)
    (j : D →ₗ[R] I)
    (m : D →ₗ[R] (P.obj (op (f ⁻¹ᵁ U)) ⊞ P.obj (op (f ⁻¹ᵁ V)) : ModuleCat.{v} R))
    (hj : j = (a.comp (LinearMap.fst R A B) - b.comp (LinearMap.snd R A B)).comp
      e.toLinearMap)
    (hU : fI.comp a =
      (P.map (((Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))).op)).hom.comp fU)
    (hV : fI.comp b =
      (P.map (((Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))).op)).hom.comp fV)
    (hm : ∀ z,
      (ModuleCat.biprodIsoProd (P.obj (op (f ⁻¹ᵁ U))) (P.obj (op (f ⁻¹ᵁ V)))).hom (m z) =
        (fU (e z).1, fV (e z).2)) :
    (biprod.desc
      (P.map (homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from inf_le_left)).op)
      (-(P.map (homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from inf_le_right)).op))).hom.comp m =
      fI.comp j := by
  let eT := CategoryTheory.Iso.toLinearEquiv
    (ModuleCat.biprodIsoProd (P.obj (op (f ⁻¹ᵁ U))) (P.obj (op (f ⁻¹ᵁ V))))
  have hmEq : m = eT.symm.toLinearMap.comp
      ((LinearMap.prodMap fU fV).comp e.toLinearMap) := by
    apply LinearMap.ext
    intro z
    apply eT.injective
    exact (hm z).trans (eT.apply_symm_apply (fU (e z).1, fV (e z).2)).symm
  have hCore := Kunneth.MayerVietoris.biprod_difference_square
    (P.obj (op (f ⁻¹ᵁ U))) (P.obj (op (f ⁻¹ᵁ V))) (P.obj (op (f ⁻¹ᵁ (U ⊓ V))))
    e fU fV fI a b
    (P.map (((Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))).op))
    (P.map (((Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))).op))
    j hj hU hV
  have hCoreOriginal :
      (biprod.desc
        (P.map (((Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))).op))
        (-(P.map (((Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))).op)))).hom.comp m =
      fI.comp j := by
    rw [hmEq]
    exact hCore
  have hTarget := presheaf_preimage_difference Z T f P U V
  exact (congrArg (fun t => t.comp m) hTarget).trans hCoreOriginal

/-- The whole original difference square follows from its two original restrictions. -/
theorem structureOpenKunnethMV_second_square (U V : Y.left.Opens) (n : ℕ) :
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
        ((snd X Y).left ⁻¹ᵁ V) n).comp (structureOpenMVMiddleMap X Y U V n) =
      (structureOpenKunnethMap X Y (U ⊓ V) n).comp
        (structureOpenKunnethMVSecond X Y U V n) := by
  have hU := structureOpenKunnethMap_restriction X Y
    (homOfLE (inf_le_left : U ⊓ V ≤ U)) n
  have hV := structureOpenKunnethMap_restriction X Y
    (homOfLE (inf_le_right : U ⊓ V ≤ V)) n
  let eT := CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))
  have hMiddle : ∀ z,
      (ModuleCat.biprodIsoProd
        (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
        (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n)).hom
          (structureOpenMVMiddleMap X Y U V n z) =
        (structureOpenKunnethMap X Y U n (structureOpenMVMiddleSourceEquiv X Y U V n z).1,
          structureOpenKunnethMap X Y V n (structureOpenMVMiddleSourceEquiv X Y U V n z).2) := by
    intro z
    exact eT.apply_symm_apply
      (structureOpenKunnethMap X Y U n (structureOpenMVMiddleSourceEquiv X Y U V n z).1,
        structureOpenKunnethMap X Y V n (structureOpenMVMiddleSourceEquiv X Y U V n z).2)
  have h := presheaf_preimage_difference_square
    (X ⊗ Y).left Y.left (snd X Y).left
    (moduleHPrimePresheaf (X ⊗ Y).left (constants (X ⊗ Y))
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n) U V
    (structureOpenMVMiddleSourceEquiv X Y U V n)
    (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)
    (structureOpenKunnethMap X Y (U ⊓ V) n)
    (structureOpenKunnethRestriction X Y (homOfLE (inf_le_left : U ⊓ V ≤ U)) n)
    (structureOpenKunnethRestriction X Y (homOfLE (inf_le_right : U ⊓ V ≤ V)) n)
    (structureOpenKunnethMVSecond X Y U V n) (structureOpenMVMiddleMap X Y U V n)
    (structureOpenMVMiddleSourceEquiv_second X Y U V n) hU hV hMiddle
  exact h

end KunnethOpenMayerVietoris

end AlgebraicGeometry.Scheme.Cohomology
