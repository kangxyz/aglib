/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.AllowedColimit
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-! # Original comparison on allowed-annihilator colimits

The actual allowed divisibility index is countable and filtered. Its native
final sequential functor transfers sequential preservation to the original
allowed diagram. No forbidden factorial annihilators enter the construction.
-/

@[expose] public noncomputable section
open CategoryTheory.Limits
namespace CategoryTheory

instance AllowedAnnihilatorIndex.countable (M : Submonoid ℕ) :
    Countable (AllowedAnnihilatorIndex M) :=
  Function.Injective.countable (f := AllowedAnnihilatorIndex.val) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

namespace Sheaf
universe u v w uD vD

/-- Sequential preservation suffices for the actual allowed-annihilator
comparison; only positive orders in the specified monoid are tested. -/
theorem natTrans_isIso_of_isLocallyAllowedTorsion
    {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    (M : Submonoid ℕ) (L R : Sheaf J AddCommGrpCat.{w} ⥤ D) (α : L ⟶ R)
    [PreservesColimitsOfShape ℕ L] [PreservesColimitsOfShape ℕ R]
    (hbounded : ∀ n : ℕ, 0 < n → n ∈ M →
      ∀ F : Sheaf J AddCommGrpCat.{w}, n • 𝟙 F = 0 → IsIso (α.app F))
    (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) : IsIso (α.app F) := by
  let Q := IsFiltered.sequentialFunctor (AllowedAnnihilatorIndex M)
  let : PreservesColimitsOfShape (AllowedAnnihilatorIndex M) L :=
    Functor.Final.preservesColimitsOfShape_of_final Q L
  let : PreservesColimitsOfShape (AllowedAnnihilatorIndex M) R :=
    Functor.Final.preservesColimitsOfShape_of_final Q R
  let K := allowedAnnihilatorDiagram M F
  let (i : AllowedAnnihilatorIndex M) : IsIso ((Functor.whiskerLeft K α).app i) :=
    hbounded i.val i.positive i.mem (K.obj i) (nsmul_id_annihilator F i.val)
  let : IsIso (Functor.whiskerLeft K α) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft K α)
  exact isIso_app_coconePt_of_preservesColimit K α
    (allowedAnnihilatorCocone M F) (allowedAnnihilatorCoconeIsColimit M F hF)

end Sheaf
end CategoryTheory
