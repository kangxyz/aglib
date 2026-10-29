/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Cohomology

/-! # Original represented Ext for underlying injective module sheaves

The existing ringed-module acyclicity theorem is transported by the selected
coefficient equivalence and its original underlying natural isomorphism.
The source is the original free representable at every site object. No
terminal object is needed for this represented Ext statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.TorsionZMod

universe u v e a b

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] Ringed.hasSheafifyRingStandard Ringed.hasSheafifyAbStandard
  Ringed.abWEqualsLocallyBijectiveStandard

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]

/-- The original coefficient equivalence transports native represented Ext
vanishing from genuine ringed-module injectives at every site object. -/
theorem representedExt_subsingleton_of_ringedEquivalence
    {D : Type a} [Category.{b} D] (R : Sheaf J RingCat.{max u v})
    (E : D ≌ SheafOfModules.{max u v} R) (U : D ⥤ Sheaf J AddCommGrpCat.{max u v})
    (η : E.functor ⋙ SheafOfModules.toSheaf R ≅ U)
    (I : D) [Injective I] (W : C) (q : ℕ) :
    Subsingleton (Ext.{e} (Sheaf.Hypercohomology.freeAbelianSheaf.{u} J W)
      (U.obj I) (q + 1)) := by
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge J
  let : Injective (E.functor.obj I) :=
    E.functor.injective_obj_of_injective (inferInstance : Injective I)
  have hM : Subsingleton
      (Ext.{e} (Sheaf.Hypercohomology.freeAbelianSheaf.{u} J W)
        ((SheafOfModules.toSheaf R).obj (E.functor.obj I)) (q + 1)) :=
    Sheaf.ModuleCoefficients.toSheaf_injective_ext_subsingleton_largeScalars
      R (E.functor.obj I) W q
  exact subsingleton_of_additiveIso
    ((extFunctorObj (Sheaf.Hypercohomology.freeAbelianSheaf.{u} J W)
      (q + 1)).mapIso (η.app I)) hM

/-- Genuine injective ZMod-module sheaves have vanishing original positive Ext
from every original free representable, with the selected coefficient realization. -/
theorem underlying_injective_representedExt_subsingleton (n : ℕ)
    (I : Sheaf J (ModuleCat.{max u v} (ZMod n))) [Injective I] (W : C) (q : ℕ) :
    Subsingleton (Ext.{e} (Sheaf.Hypercohomology.freeAbelianSheaf.{u} J W)
      ((sheafCompose J
        (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj I)
      (q + 1)) :=
  representedExt_subsingleton_of_ringedEquivalence J (Ringed.constantRingSheaf J n)
    (Ringed.equivalenceStandard J n)
    (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}))
    (Ringed.forwardUnderlyingIsoStandard J n) I W q

end CategoryTheory.TorsionZMod
