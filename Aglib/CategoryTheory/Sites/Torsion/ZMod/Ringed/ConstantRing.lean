/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The actual associated constant coefficient ring sheaf

The presheaf ring is the constant presheaf on the standard-size lift of the
original `ZMod n`. The ring sheaf is its native associated sheaf, and the ring
map is the original sheafification unit. Scalar conversion uses the actual
canonical ring equivalence to the original ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v w

/-- The scalar transport is the native equivalence of the original and lifted rings. -/
def scalarEquivalence (n : ℕ) :
    ModuleCat.{w} (ZMod n) ≌ ModuleCat.{w} (ULift.{w} (ZMod n)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{w} (ZMod n) ≃+* ZMod n)

variable {C : Type u} [Category.{v} C]

/-- The actual constant ring presheaf on the lifted original coefficient ring. -/
def constantRingPresheaf (n : ℕ) : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{w} (ZMod n)))

variable (J : GrothendieckTopology C)

/-- The native associated sheaf of the actual constant lifted ring presheaf. -/
def constantRingSheaf [HasWeakSheafify J RingCat.{w}] (n : ℕ) : Sheaf J RingCat.{w} :=
  (presheafToSheaf J RingCat.{w}).obj (constantRingPresheaf n)

/-- The original native ring sheafification unit, with its original source and target. -/
abbrev ringUnit [HasWeakSheafify J RingCat.{w}] (n : ℕ) :
    (constantRingPresheaf (C := C) n : Cᵒᵖ ⥤ RingCat.{w}) ⟶
      (constantRingSheaf J n : Sheaf J RingCat.{w}).obj :=
  CategoryTheory.toSheafify J (constantRingPresheaf n)

/-- The native ring filtered-colimit cocone supplies the actual filtered colimits. -/
theorem ringHasFilteredColimits : HasFilteredColimits RingCat.{w} where
  HasColimitsOfShape _K _ _ := {
    has_colimit F := ⟨_, RingCat.FilteredColimits.colimitCoconeIsColimit F⟩ }

attribute [local instance] ringHasFilteredColimits

/-- Native ring sheafification exists at the value size covering the original site. -/
theorem hasSheafifyRingStandard : HasSheafify J RingCat.{max u v} := by
  infer_instance

/-- Native abelian sheafification exists at the same actual value size. -/
theorem hasSheafifyAbStandard : HasSheafify J AddCommGrpCat.{max u v} := by
  infer_instance

/-- The native ring sheafification class is exactly local bijectivity at standard size. -/
theorem ringWEqualsLocallyBijectiveStandard : J.WEqualsLocallyBijective RingCat.{max u v} := by
  let := hasSheafifyRingStandard J
  infer_instance

/-- The native abelian sheafification class is exactly local bijectivity at standard size. -/
theorem abWEqualsLocallyBijectiveStandard :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := by
  let := hasSheafifyAbStandard J
  infer_instance

section Unit

variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]

/-- The actual constant-ring unit is locally injective. -/
theorem ringUnit_isLocallyInjective (n : ℕ) :
    Presheaf.IsLocallyInjective J (ringUnit.{u, v, w} J n) := by
  change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J
    (constantRingPresheaf n : Cᵒᵖ ⥤ RingCat.{w}))
  infer_instance

/-- The same actual constant-ring unit is locally surjective. -/
theorem ringUnit_isLocallySurjective (n : ℕ) :
    Presheaf.IsLocallySurjective J (ringUnit.{u, v, w} J n) := by
  change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J
    (constantRingPresheaf n : Cᵒᵖ ⥤ RingCat.{w}))
  infer_instance

end Unit

end CategoryTheory.TorsionZMod.Ringed
