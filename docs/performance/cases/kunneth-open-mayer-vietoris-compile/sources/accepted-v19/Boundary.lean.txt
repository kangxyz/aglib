/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.Rows

/-! # The two original Koszul signs in the mixed-open boundary -/

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

private theorem integer_koszul_smul {T : Type*} [AddCommGroup T] [Module k T]
    (p : ℕ) (z : T) : ((-1 : ℤ) ^ p) • z = ((-1 : k) ^ p) • z := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The original cup boundary law expressed with the identical structural field sign. -/
theorem structureExternalOpenCup_mayerVietoris_smul (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n) (x : structureCohomology k X p)
    (y : structureOpenCohomology Y (U ⊓ V) q) :
    structureExternalOpenCup X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
        (structureOpenMayerVietorisDelta Y U V q y) =
      ((-1 : k) ^ p) • structureOpenMayerVietorisDelta (X ⊗ Y)
        ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
        (structureExternalOpenCup X Y (U ⊓ V) h x y) := by
  rw [structureExternalOpenCup_mayerVietoris, integer_koszul_smul (k := k)]

/-- The unsigned homogeneous tensor square retains the original structural sign. -/
private theorem structureExternalOpenTensor_boundary (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n) :
    structureExternalOpenTensor X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) ∘ₗ
        (structureOpenMayerVietorisDelta Y U V q).lTensor (structureCohomology k X p) =
      ((-1 : k) ^ p) •
        (structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n ∘ₗ
            structureExternalOpenTensor X Y (U ⊓ V) h) := by
  apply TensorProduct.ext'
  intro x y
  change structureExternalOpenCup X Y (U ⊔ V) _ x
    (structureOpenMayerVietorisDelta Y U V q y) = _
  exact structureExternalOpenCup_mayerVietoris_smul X Y U V h x y

/-- The actual signed source boundary on the original finite antidiagonal. -/
def structureOpenKunnethBoundary (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethSum X Y (U ⊓ V) n →ₗ[k]
      structureOpenKunnethSum X Y (U ⊔ V) (n + 1) :=
  Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
    (fun q => structureOpenMayerVietorisDelta Y U V q) n

/-- The source Koszul sign cancels the native crossing sign in the whole boundary square. -/
theorem structureOpenKunnethMap_boundary (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethMap X Y (U ⊔ V) (n + 1) ∘ₗ structureOpenKunnethBoundary X Y U V n =
      structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n ∘ₗ
        structureOpenKunnethMap X Y (U ⊓ V) n := by
  apply DirectSum.linearMap_ext
  intro s
  apply LinearMap.ext
  intro z
  have hs : s.val.1 + s.val.2 = n := s.property
  let t := Kunneth.MayerVietoris.rightSuccessor n s
  let d := (structureOpenMayerVietorisDelta Y U V s.val.2).lTensor
    (structureCohomology k X s.val.1)
  let sign : k := (-1 : k) ^ s.val.1
  let T := structureExternalOpenTensor X Y (U ⊔ V)
    (show s.val.1 + (s.val.2 + 1) = n + 1 by omega)
  have hB := Kunneth.MayerVietoris.tensorBoundary_lof (R := k) (structureCohomology k X)
    (fun q => structureOpenMayerVietorisDelta Y U V q) n s z
  have hMap := congrArg (structureOpenKunnethMap X Y (U ⊔ V) (n + 1)) hB
  have hLof := structureOpenKunnethMap_lof X Y (U ⊔ V) (n + 1) t (sign • d z)
  have hSmul := T.map_smul sign (d z)
  have hCell := LinearMap.congr_fun (structureExternalOpenTensor_boundary X Y U V s.property) z
  change T (d z) = sign •
    structureOpenMayerVietorisDelta (X ⊗ Y)
      ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
      (structureExternalOpenTensor X Y (U ⊓ V) s.property z) at hCell
  have hSign := congrArg (fun w => sign • w) hCell
  rw [Kunneth.MayerVietoris.koszul_smul_smul (R := k)] at hSign
  have hRight := congrArg (structureOpenMayerVietorisDelta (X ⊗ Y)
    ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenKunnethMap_lof X Y (U ⊓ V) n s z)
  have hFinal := hMap.trans (hLof.trans (hSmul.trans (hSign.trans hRight.symm)))
  exact hFinal

end AlgebraicGeometry.Scheme.Cohomology
