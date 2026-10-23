/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftZero

/-! # Naturality of the original cohomology universe map

The coefficient square uses the original `Sheaf.H.map`, not a newly chosen
cohomology model. Consequently the all-degree equivalence in `ValueComparison`
has this same natural forward map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe e e' c h v t

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{e'} (Sheaf J AddCommGrpCat.{max v t})]
  {T : C} (hT : IsTerminal T)

/-- Universe lifting commutes with the actual cohomology map of every
coefficient morphism, in every degree and at independent Ext universes. -/
theorem valueLiftCohomologyMap_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (x : Sheaf.H.{e} F n) :
    valueLiftCohomologyMap.{e, e', c, h, v, t} hT G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((valueLift.{c, h, v, t} J).map f) n
        (valueLiftCohomologyMap.{e, e', c, h, v, t} hT F n x) := by
  change (valueLift.{c, h, v, t} J).extPrecompMap
      (valueLiftConstantMap.{c, h, v, t} hT) G n
      (x.comp (Ext.mk₀ f) (Nat.add_zero n)) = _
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  rfl

end CategoryTheory.Sheaf.BasisAcyclicity
