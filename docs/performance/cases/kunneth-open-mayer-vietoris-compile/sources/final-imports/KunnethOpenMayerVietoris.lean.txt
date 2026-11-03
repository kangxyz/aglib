/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.Compatibility
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.GluingInjective
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.GluingSurjective

/-!
# The original mixed-open Mayer–Vietoris ladder

The original native rows, restrictions, difference maps and twice-occurring degree-p
Koszul sign are assembled into the same unsigned target ladder in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

open KunnethOpenMayerVietoris

/-- Bijectivity of the original mixed maps glues in degree zero by the native four lemma. -/
private theorem structureOpenKunnethMap_bijective_sup_zero (U V : Y.left.Opens)
    (hU : Function.Bijective (structureOpenKunnethMap X Y U 0))
    (hV : Function.Bijective (structureOpenKunnethMap X Y V 0))
    (hI : Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) 0)) :
    Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) 0) := by
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (structureOpenKunnethMVFirst X Y U V 0) (structureOpenKunnethMVSecond X Y U V 0)
    (structureOpenMVFirst (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenKunnethMap X Y (U ⊔ V) 0) (structureOpenMVMiddleMap X Y U V 0)
    (structureOpenKunnethMap X Y (U ⊓ V) 0)
    (structureOpenKunnethMV_first_square X Y U V 0)
    (structureOpenKunnethMV_second_square X Y U V 0)
    (structureOpenKunnethMV_exact_first X Y U V 0)
    (structureOpenMV_exact_first (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenMVMiddleMap_bijective X Y U V 0 hU hV) hI.1
    (structureOpenKunnethMV_first_zero_injective X Y U V)
    (structureOpenMV_first_zero_injective (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V))

/-- Every positive union degree follows from the native five lemma on the actual signed ladder. -/
private theorem structureOpenKunnethMap_bijective_sup_succ (U V : Y.left.Opens) (n : ℕ)
    (hU : ∀ m, Function.Bijective (structureOpenKunnethMap X Y U m))
    (hV : ∀ m, Function.Bijective (structureOpenKunnethMap X Y V m))
    (hI : ∀ m, Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) m)) :
    Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) (n + 1)) := by
  have hMiddle := structureOpenMVMiddleMap_bijective X Y U V n (hU n) (hV n)
  have hMiddleNext := structureOpenMVMiddleMap_bijective X Y U V (n + 1)
    (hU (n + 1)) (hV (n + 1))
  exact ⟨structureOpenKunnethMap_injective_sup_succ X Y U V n
      hMiddle.2 (hI n).1 hMiddleNext.1,
    structureOpenKunnethMap_surjective_sup_succ X Y U V n
      (hI n).2 hMiddleNext.2 (hI (n + 1)).1⟩

/-- The literal original mixed-open maps glue across an actual union, in all degrees. -/
theorem structureOpenKunnethMap_bijective_sup (U V : Y.left.Opens)
    (hU : ∀ n, Function.Bijective (structureOpenKunnethMap X Y U n))
    (hV : ∀ n, Function.Bijective (structureOpenKunnethMap X Y V n))
    (hI : ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) n)) :
    ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) n) := by
  intro n
  cases n with
  | zero => exact structureOpenKunnethMap_bijective_sup_zero X Y U V (hU 0) (hV 0) (hI 0)
  | succ n => exact structureOpenKunnethMap_bijective_sup_succ X Y U V n hU hV hI

end AlgebraicGeometry.Scheme.Cohomology
