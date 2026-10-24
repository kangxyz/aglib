/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.AffineRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable

/-! # Positive genuine presentations on separated schemes

The actual finite-etale stratification of affine-etale generators supplies
the partition input for the original bounded presentation. Every genuine
ZMod sheaf at nonzero modulus on a separated scheme therefore has a filtered
presentation with constructible underlying stages, ambient finite
presentability globally and on every original affine open, and both the
genuine and underlying colimit cocones.

There is no Noetherian assumption. The algebraic presentations at modulus
zero remain the separate all-modulus statements in `GenuineModules`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

open Constructible.PositivePresentation

/-- Every positive-modulus genuine coefficient on a separated scheme is
the filtered colimit of genuine coefficients whose original underlying
sheaves are constructible and ambient finitely presentable, including after
restriction to every original affine open. Both cocones use the original
coefficient as their point. -/
theorem exists_filtered_genuine_presentation_of_isSeparated
    (X : Scheme.{u}) [X.IsSeparated] (n : ℕ) (hn : n ≠ 0)
    (M : Reduction.ZModSheaf X n) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Reduction.ZModSheaf X n) (κ : D ⟶ (Functor.const I).obj M),
      Nonempty (IsColimit (Cocone.mk M κ)) ∧
        Nonempty (IsColimit
          ((Reduction.zmodUnderlying X n).mapCocone (Cocone.mk M κ))) ∧
        ∀ i, IsFinitelyPresentable.{u + 1}
            ((Reduction.zmodUnderlying X n).obj (D.obj i)) ∧
          Constructible.IsConstructible ((Reduction.zmodUnderlying X n).obj (D.obj i)) ∧
          ∀ V : X.affineOpens, IsFinitelyPresentable.{u + 1}
            ((inverseImage V.1.ι).obj ((Reduction.zmodUnderlying X n).obj (D.obj i))) := by
  have : IsSeparated (terminal.from X) :=
    (inferInstance : X.IsSeparated).isSeparated_terminal_from
  refine exists_filtered_genuine_presentation_constructible_affineFP_of_finiteEtalePartitions
    X n hn ?_ M
  intro U
  have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
    inferInstanceAs (IsAffine (Spec U.left.unop))
  exact finiteEtalePartitions_of_isAffine_of_isSeparated
    ((Scheme.AffineEtale.Spec X).obj U)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
