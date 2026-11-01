/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteEtalePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FilteredCoefficients

/-! # Passing original cohomology vanishing from constructible coefficients

The actual positive-modulus filtered presentations have geometrically
constructible stages on a separated scheme. On a qcqs scheme, original
cohomology preserves their original colimit cocones. Vanishing for
constructible coefficients killed by a fixed nonzero integer therefore
extends to all coefficients killed by that same integer.

The existing factorial-annihilator reduction then passes vanishing for all
constructible coefficients to arbitrary internal torsion. Filtered colimits
are computed in the native standard Ext universe and the resulting vanishing
is transported back, so the original Ext universe remains arbitrary without
a large-index colimit-existence hypothesis on its value category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge

open Constructible.PositivePresentation

variable {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- Vanishing for constructible coefficients with a fixed nonzero annihilator
extends to every coefficient with that same annihilator. The actual original
filtered presentation supplies the constructible stages and coefficient maps.
-/
theorem subsingleton_H_of_killed_of_constructible
    (n : ℕ) (hn : n ≠ 0) (q : ℕ)
    (hconstructible : ∀ G : AbelianSheaf.{u, u + 1} X,
      Constructible.IsConstructible G → n • 𝟙 G = 0 →
        Subsingleton (Sheaf.H.{e} G q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    Subsingleton (Sheaf.H.{e} F q) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := HasExt.standard _
  have : IsSeparated (terminal.from X) :=
    (inferInstance : X.IsSeparated).isSeparated_terminal_from
  have hparts (U : Scheme.AffineEtale X) :
      ∀ V : X.affineOpens, ∃ p : Constructible.FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom := by
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact finiteEtalePartitions_of_isAffine_of_isSeparated
      ((Scheme.AffineEtale.Spec X).obj U)
  obtain ⟨I, hI, hfiltered, D, ι, ⟨hcolimit⟩, hstage⟩ :=
    exists_filtered_presentation_constructible_of_finiteEtalePartitions
      X n hn hparts F hF
  let := hI
  let := hfiltered
  let G := D ⋙ Constructible.BoundedPresentation.inclusion X n
  let H := cohomologyFunctor.{u, u + 2} X q
  let : PreservesColimitsOfShape I H :=
    qcqsCohomologyFunctor_preservesColimitsOfShape X q
  have hzero : IsZero (G ⋙ H) := by
    apply Functor.isZero
    intro i
    let : Subsingleton (Sheaf.H.{e} (D.obj i).obj q) :=
      hconstructible (D.obj i).obj (hstage i).2.2 (D.obj i).property
    let eH : Sheaf.H.{e} (D.obj i).obj q ≃ Sheaf.H.{u + 2} (D.obj i).obj q :=
      Ext.chgUniv
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr eH.surjective.subsingleton
  have hFzero : IsZero (H.obj F) :=
    (isColimitOfPreserves H hcolimit).isZero_pt hzero
  let : Subsingleton (Sheaf.H.{u + 2} F q) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hFzero
  let eH : Sheaf.H.{e} F q ≃ Sheaf.H.{u + 2} F q := Ext.chgUniv
  exact eH.injective.subsingleton

/-- Vanishing for every constructible coefficient on a separated qcqs scheme
extends to every internally torsion coefficient, without imposing a common
annihilator on the latter. -/
theorem subsingleton_H_of_isTorsion_of_constructible
    (q : ℕ)
    (hconstructible : ∀ G : AbelianSheaf.{u, u + 1} X,
      Constructible.IsConstructible G → Subsingleton (Sheaf.H.{e} G q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    Subsingleton (Sheaf.H.{e} F q) := by
  apply subsingleton_H_of_isTorsion_of_bounded q ?_ F hF
  intro n hn G hG
  exact subsingleton_H_of_killed_of_constructible n (Nat.ne_of_gt hn) q
    (fun L hL _ => hconstructible L hL) G hG

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
