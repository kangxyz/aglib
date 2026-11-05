/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Finite colimits from finite sums and weak cokernel closure

The original standard coproduct/coequalizer presentation expresses any finite
colimit as a cokernel of a map between finite sums. No arbitrary quotient or
subobject closure is used.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe u h v

variable {C : Type u} [Category.{h} C] [Preadditive C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderFiniteCoproducts] [P.IsClosedUnderCokernels]
    {J : Type v} [SmallCategory J] [Finite (Arrow J)]
    [HasFiniteColimits C]

/-- Weak cokernel closure and finite coproduct closure suffice for every
original finite colimit, without ambient quotient closure. -/
theorem prop_of_isColimit_of_finiteCoproducts_cokernels
    (D : J ⥤ C) {c : Cocone D} (hc : IsColimit c) (hD : ∀ j, P (D.obj j)) : P c.pt := by
  classical
  let : Finite J := Finite.of_surjective (fun a : Arrow J => a.left)
    (fun j => ⟨Arrow.mk (𝟙 j), rfl⟩)
  let (i j : J) : Finite (i ⟶ j) := Finite.of_injective Arrow.mk (Arrow.mk_injective i j)
  let : Fintype J := Fintype.ofFinite J
  let (i j : J) : Fintype (i ⟶ j) := Fintype.ofFinite (i ⟶ j)
  let s : (∐ fun f : Σ p : J × J, p.1 ⟶ p.2 => D.obj f.1.1) ⟶ ∐ D.obj :=
    Sigma.desc (fun f => D.map f.2 ≫ Sigma.ι D.obj f.1.2)
  let t : (∐ fun f : Σ p : J × J, p.1 ⟶ p.2 => D.obj f.1.1) ⟶ ∐ D.obj :=
    Sigma.desc (fun f => Sigma.ι D.obj f.1.1)
  have hq : P (coequalizer s t) :=
    P.prop_of_isColimit_cokernelCofork
      (Preadditive.isColimitCokernelCoforkOfCofork (coequalizerIsCoequalizer s t))
      (P.prop_coproduct (fun f => hD f.1.1)) (P.prop_coproduct hD)
  let d := colimitCoconeOfCoequalizerAndCoproduct D
  have hd : P d.cocone.pt := hq
  exact P.prop_of_iso (d.isColimit.coconePointUniqueUpToIso hc) hd

end CategoryTheory.ObjectProperty
