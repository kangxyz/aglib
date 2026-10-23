/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.Equivalence

/-!
# Genuine ZMod-valued sheaves and native ringed module sheaves

At the standard site/value size, genuine sheaves of modules over the original
`ZMod n` are equivalent to native `SheafOfModules` over the associated sheaf
of the constant presheaf on `ULift (ZMod n)`. All ring and abelian sheafification
premises are supplied natively. The underlying abelian natural comparison
uses the original scalar transport, constant-presheaf identity comparisons,
and the actual native abelian-sheafification counit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

/-- The native module equivalence with all actual standard coefficient objects fixed. -/
def moduleEquivalenceStandard :
    (moduleSheafProperty.{u, v, max u v, max u v} J
      (constantRingPresheaf (C := C) n)).FullSubcategory ≌
      SheafOfModules.{max u v} (constantRingSheaf J n : Sheaf J RingCat.{max u v}) := by
  let R₀ : Cᵒᵖ ⥤ RingCat.{max u v} := constantRingPresheaf n
  let R : Sheaf J RingCat.{max u v} := constantRingSheaf J n
  let α : R₀ ⟶ R.obj := ringUnit J n
  letI : Presheaf.IsLocallyInjective J α := ringUnit_isLocallyInjective J n
  letI : Presheaf.IsLocallySurjective J α := ringUnit_isLocallySurjective J n
  exact moduleSheafificationEquivalence J (R₀ := R₀) (R := R) (α := α)

/-- The same typed native equivalence has the actual abelian counit comparison. -/
def moduleUnderlyingIsoStandard : (moduleEquivalenceStandard J n).functor ⋙
      SheafOfModules.toSheaf (constantRingSheaf J n) ≅
    moduleUnderlyingSheaf.{u, v, max u v, max u v} J
      (constantRingPresheaf (C := C) n) := by
  let R₀ : Cᵒᵖ ⥤ RingCat.{max u v} := constantRingPresheaf n
  let R : Sheaf J RingCat.{max u v} := constantRingSheaf J n
  let α : R₀ ⟶ R.obj := ringUnit J n
  letI : Presheaf.IsLocallyInjective J α := ringUnit_isLocallyInjective J n
  letI : Presheaf.IsLocallySurjective J α := ringUnit_isLocallySurjective J n
  exact moduleSheafificationUnderlyingIso J (R₀ := R₀) (R := R) (α := α)

/-- The actual standard-sized equivalence, including moduli zero and one.
The scalar ring transport is the native RingEquiv to the actual lifted ring. -/
def equivalenceStandard : Sheaf J (ModuleCat.{max u v} (ZMod n)) ≌
    SheafOfModules.{max u v} (constantRingSheaf J n : Sheaf J RingCat.{max u v}) :=
  (scalarSheafEquivalence.{u, v, max u v} J n).trans
    ((constantSheafEquivalence.{u, v, max u v, max u v} J
        (ULift.{max u v} (ZMod n))).trans
      (moduleEquivalenceStandard J n))

/-- The exact natural comparison with the original underlying abelian sheaf.
Its final sheafification factor is the original native counit. -/
def forwardUnderlyingIsoStandard : (equivalenceStandard J n).functor ⋙
      SheafOfModules.toSheaf (constantRingSheaf J n) ≅
    sheafCompose J
      (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}) :=
  let E := scalarSheafEquivalence.{u, v, max u v} J n
  let K := constantSheafEquivalence.{u, v, max u v, max u v} J
    (ULift.{max u v} (ZMod n))
  let L := moduleEquivalenceStandard J n
  (Functor.associator E.functor (K.functor ⋙ L.functor)
      (SheafOfModules.toSheaf (constantRingSheaf J n))) ≪≫
    Functor.isoWhiskerLeft E.functor
      ((Functor.associator K.functor L.functor
          (SheafOfModules.toSheaf (constantRingSheaf J n))) ≪≫
        Functor.isoWhiskerLeft K.functor
          (moduleUnderlyingIsoStandard J n) ≪≫
        constantSheafUnderlyingIso.{u, v, max u v, max u v} J
          (ULift.{max u v} (ZMod n))) ≪≫
    scalarSheafUnderlyingIso.{u, v, max u v} J n

/-- Every original coefficient morphism commutes with the actual underlying
ringed-module comparison. -/
@[reassoc]
theorem forwardUnderlyingIsoStandard_naturality
    {F G : Sheaf J (ModuleCat.{max u v} (ZMod n))} (f : F ⟶ G) :
    (SheafOfModules.toSheaf (constantRingSheaf J n)).map
        ((equivalenceStandard J n).functor.map f) ≫
      (forwardUnderlyingIsoStandard J n).hom.app G =
    (forwardUnderlyingIsoStandard J n).hom.app F ≫
      (sheafCompose J
        (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map f :=
  (forwardUnderlyingIsoStandard J n).hom.naturality f

end CategoryTheory.TorsionZMod.Ringed
