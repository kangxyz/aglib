/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris

/-! The actual mixed-open maps form the original Mayer–Vietoris ladder. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example (U V : Y.left.Opens)
    (hU : ∀ n, Function.Bijective (structureOpenKunnethMap X Y U n))
    (hV : ∀ n, Function.Bijective (structureOpenKunnethMap X Y V n))
    (hI : ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) n)) :
    ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) n) :=
  structureOpenKunnethMap_bijective_sup X Y U V hU hV hI

example (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethMap X Y (U ⊔ V) (n + 1) ∘ₗ structureOpenKunnethBoundary X Y U V n =
      structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n ∘ₗ
        structureOpenKunnethMap X Y (U ⊓ V) n :=
  structureOpenKunnethMap_boundary X Y U V n
