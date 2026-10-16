/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
/-! # Standard abelian exact structures agree with their transported structures -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure

/-- The selected conflations determine all the remaining exact structure data,
since the universal-property witnesses are unique. -/
theorem ext_conflation {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasFiniteBiproducts C] {E E' : ExactStructure C}
    (h : E.conflation = E'.conflation) : E = E' := by
  cases E
  cases E'
  cases h
  congr <;> apply Subsingleton.elim

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (e : C ≌ D) [e.functor.Additive]

/-- Short exactness is preserved and reflected by the actual additive equivalence. -/
theorem shortExact_map_equivalence_iff (S : ShortComplex C) :
    (S.map e.functor).ShortExact ↔ S.ShortExact := by
  let : e.inverse.Additive := e.inverse_additive
  constructor
  · intro h
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.unitIso.symm)
      (h.map_of_exact e.inverse)
  · exact fun h => h.map_of_exact e.functor

/-- Transporting the standard abelian exact structure yields the standard
abelian exact structure, not merely another unspecified exact structure. -/
theorem abelianExactStructure_ofEquivalence :
    (abelianExactStructure D).ofEquivalence e = abelianExactStructure C := by
  apply ExactStructure.ext_conflation
  funext S
  exact propext (shortExact_map_equivalence_iff e S)

variable (C) [EssentiallySmall.{w} C]

/-- The actual small model's inherited exact structure is its standard abelian one. -/
theorem abelianExactStructure_smallModel :
    (abelianExactStructure C).smallModel = abelianExactStructure (SmallModel.{w} C) :=
  abelianExactStructure_ofEquivalence (equivSmallModel C).symm

end CategoryTheory.ExactCategory

namespace CategoryTheory.SmallModel

open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The identity exact functor between the proved-equal transported and
standard abelian exact structures on the chosen small model. -/
def abelianExactComparison : ExactCategory.ExactFunctor (abelianExactStructure C).smallModel
    (abelianExactStructure (SmallModel.{w} C)) where
  toFunctor := 𝟭 _
  map_conflation _ h := by
    rw [abelianExactStructure_smallModel] at h
    exact h

/-- The identity exact comparison has an underlying equivalence. -/
instance abelianExactComparison_isEquivalence :
    (abelianExactComparison.{w} C).toFunctor.IsEquivalence := inferInstanceAs (𝟭 _).IsEquivalence

variable {C} {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EssentiallySmall.{w} D]

/-- The same canonical small-model functor, with the equal standard abelian
exact structures instead of the transported structures. -/
def mapAbelianExactFunctor
    (F : ExactCategory.ExactFunctor (abelianExactStructure C) (abelianExactStructure D)) :
    ExactCategory.ExactFunctor (abelianExactStructure (SmallModel.{w} C))
      (abelianExactStructure (SmallModel.{w} D)) where
  toFunctor := F.smallModel.toFunctor
  map_conflation S h := by
    have hs : (abelianExactStructure C).smallModel.conflation S := by
      rwa [abelianExactStructure_smallModel]
    have ht := F.smallModel.map_conflation S hs
    exact (congrArg (fun E : ExactStructure (SmallModel.{w} D) =>
      E.conflation (S.map F.smallModel.toFunctor)) (abelianExactStructure_smallModel D)).mp ht

end CategoryTheory.SmallModel
