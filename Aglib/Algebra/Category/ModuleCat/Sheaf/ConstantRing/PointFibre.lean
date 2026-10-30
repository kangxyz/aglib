/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Actual point fibres of native constant-ring module sheaves

The one coefficient equivalence is followed by the supplied point's module-valued
fibre. The underlying comparison is the native filtered-colimit comparison at
the actual point size followed by the original coefficient underlying comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w p

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
  (Φ : GrothendieckTopology.Point.{p} J)
  [HasColimitsOfSize.{p, p} (ModuleCat.{w} R)]
  [HasColimitsOfSize.{p, p} AddCommGrpCat.{w}]

/-- The native module fibre at the actual supplied point. -/
def pointFibre : ModuleSheaf.{u, v, r, w} J R ⥤ ModuleCat.{w} R :=
  (moduleSheafEquivalence J R).inverse ⋙ Φ.sheafFiber

variable [LocallySmall.{p} C]
  [PreservesFilteredColimitsOfSize.{p, p}
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Forgetting this same module fibre gives the original additive point fibre. -/
def pointFibreUnderlyingIso :
    pointFibre J R Φ ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf (constantRing J R) ⋙
        Φ.sheafFiber (A := AddCommGrpCat.{w}) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso J R) _

/-- The whole coefficient comparison keeps its original four factors. -/
theorem pointFibreUnderlyingIso_eq_original :
    pointFibreUnderlyingIso J R Φ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso J R) _ := rfl

end ModuleCat.Sheaf.ConstantRing
