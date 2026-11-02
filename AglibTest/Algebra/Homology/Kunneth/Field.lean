/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Kunneth.Field
public import Mathlib.Algebra.Field.ZMod

/-! Consumers of the original cycle formula, whole naturality, unit and
Koszul symmetry of the canonical field Künneth map. Characteristic two
uses exactly the same map and proof, without an invertible factorial. -/

@[expose] public noncomputable section

open CategoryTheory HomologicalComplex
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]
  (C D : CochainComplex (ModuleCat.{u} k) ℕ)

example (p q n : ℕ) (h : p + q = n) (x : C.cycles p) (y : D.cycles q) :
    Kunneth.equiv C D n
      (DirectSum.lof k _ _ (⟨(p, q), h⟩ : HomologicalComplex₂.TotalDegree n)
        (C.homologyπ p x ⊗ₜ[k] D.homologyπ q y)) =
      (HomologicalComplex.tensorObj C D).homologyπ n
        (Kunneth.tensorCyclesToCycles C D p q n h (x ⊗ₜ[k] y)) :=
  Kunneth.map_lof_homologyπ_tmul C D p q n h x y

example {C' D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    (homologyMap (HomologicalComplex.tensorHom f g) n).hom ∘ₗ Kunneth.map C D n =
      Kunneth.map C' D' n ∘ₗ Kunneth.homologyTensorSumMap f g n :=
  Kunneth.map_naturality f g n

example (n : ℕ) (a : C.homology n) :
    homologyMap (HomologicalComplex.leftUnitor C).hom n
      (Kunneth.tensorHomologyMap (HomologicalComplex.tensorUnit (ModuleCat.{u} k) (.up ℕ))
        C 0 n n (zero_add n) (Kunneth.tensorUnitHomology 1 ⊗ₜ[k] a)) = a := by
  simpa only [one_smul] using Kunneth.tensorHomologyMap_leftUnitor C n (1 : k) a

example (p q n : ℕ) (h : p + q = n) :
    (homologyMap (Kunneth.tensorSwap C D).hom n).hom ∘ₗ
        Kunneth.tensorHomologyMap C D p q n h =
      (-1 : ℤˣ) ^ (p * q) •
        (Kunneth.tensorHomologyMap D C q p n (by omega) ∘ₗ
          (TensorProduct.comm k (C.homology p) (D.homology q)).toLinearMap) :=
  Kunneth.tensorHomologyMap_swap C D p q n h

section CharacteristicTwo

local instance charTwoField : Field (ZMod 2) := inferInstance
local instance : CommRing (ZMod 2) := charTwoField.toCommRing

example (C D : CochainComplex (ModuleCat (ZMod 2)) ℕ) (n : ℕ) :
    Function.Bijective (Kunneth.map (R := ZMod 2) C D n) :=
  @Kunneth.map_bijective (ZMod 2) charTwoField C D n

end CharacteristicTwo
