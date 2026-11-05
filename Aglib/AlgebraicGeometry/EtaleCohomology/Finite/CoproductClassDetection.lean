/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceZeroDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.RefinedRestrictionZero
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.Large.TerminalFiniteCoproductDetection

/-! # Actual component restrictions detect original finite-coproduct classes

Each given zero is zero of the literal scheme-cohomology pullback along the
canonical component inclusion. The proved source square returns it to the
original represented augmentation; the genuine finite coproduct of those
sources then detects the unchanged class. No vanishing of whole cohomology
groups, or unproved evaluation formula for an equivalence, is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u e e'

attribute [local instance] hasSheafifyLarge

variable {ι : Type u} (Y : ι → Scheme.{u})

/-- The canonical component augmentation is the original free-representable
component map followed by the inverse constant-integer/terminal isomorphism. -/
theorem representedIntegerAugmentation_sigmaChart (i : ι) :
    representedIntegerAugmentation (Scheme.Etale.sigmaChart Y i) =
      (freeAbelianSheafFunctor.{u + 1} (∐ Y).smallEtaleTopology).map
          (Scheme.Etale.sigmaChartInclusion Y i) ≫
        (constantIntegerFreeTerminalIso (∐ Y).smallEtaleTopology
          (etaleTerminalIsTerminal (∐ Y))).inv := by
  have ht : (etaleTerminalIsTerminal (∐ Y)).from (Scheme.Etale.sigmaChart Y i) =
      Scheme.Etale.sigmaChartInclusion Y i :=
    (etaleTerminalIsTerminal (∐ Y)).hom_ext _ _
  simp only [representedIntegerAugmentation, ht]

variable [Finite ι]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (∐ Y))]
  [∀ i, HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i))]

/-- Zero of each actual component pullback forces the same original class
on a finite scheme coproduct to vanish, including the empty coproduct. -/
theorem eq_zero_of_finiteCoproduct_cohomologyPullbacks_eq_zero
    (F : AbelianSheaf.{u, u + 1} (∐ Y)) (q : ℕ) (x : Sheaf.H.{e} F q)
    (hx : ∀ i, cohomologyPullback.{u, e, e'} (Sigma.ι Y i) F q x = 0) : x = 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  apply Sheaf.LargeCohomology.eq_zero_of_terminalFiniteCoproduct_precomp.{u + 1, u, u + 1, e, u}
    (∐ Y).smallEtaleTopology (etaleTerminalIsTerminal (∐ Y))
    (Scheme.Etale.sigmaChartInclusion Y)
    (Scheme.Etale.sigmaSections_bijective.{u, u + 1} Y) F q x
  intro i
  let : HasExt.{e'}
      (AbelianSheaf.{u, u + 1} (Scheme.Etale.sigmaChart Y i).left) :=
    inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i)))
  have hi := represented_precomp_eq_zero_of_cohomologyPullback_eq_zero
    (Scheme.Etale.sigmaChart Y i) F q x (hx i)
  simpa only [representedIntegerAugmentation_sigmaChart] using hi

/-- A finite-coproduct original class is zero exactly when all its original
component pullbacks are zero. -/
theorem finiteCoproduct_cohomologyPullbacks_eq_zero_iff
    (F : AbelianSheaf.{u, u + 1} (∐ Y)) (q : ℕ) (x : Sheaf.H.{e} F q) :
    (∀ i, cohomologyPullback.{u, e, e'} (Sigma.ι Y i) F q x = 0) ↔ x = 0 := by
  constructor
  · exact eq_zero_of_finiteCoproduct_cohomologyPullbacks_eq_zero Y F q x
  · intro hx i
    rw [hx, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite
universe u e
section OriginalCover
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Componentwise zero on the actual etale neighborhoods produces zero on
their whole finite coproduct, for the unchanged class on the original scheme. -/
theorem coproductEtale_cohomologyPullback_eq_zero
    {X : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    {κ : Type u} [Finite κ] (U : κ → X.Etale)
    (M : AbelianSheaf.{u, u + 1} X) (q : ℕ) (x : Sheaf.H.{e} M q)
    (hx : ∀ i, cohomologyPullback.{u, e, u + 2} (X := X) (S := (U i).left) (U i).hom M q x = 0) :
    cohomologyPullback.{u, e, u + 2} (X := X)
      (S := (coproductEtale U).left) (coproductEtale U).hom M q x = 0 := by
  apply eq_zero_of_finiteCoproduct_cohomologyPullbacks_eq_zero
    (fun i => (U i).left) _ q
  intro i
  exact restriction_zero_after_refinement
    (Y := X) (V := (U i).left)
    (Y' := ∐ fun i => (U i).left) (V' := (U i).left)
    (U i).hom (coproductEtale U).hom
    (Sigma.ι (fun i => (U i).left) i) (𝟙 (U i).left)
    (by
      change 𝟙 (U i).left ≫ (U i).hom =
        Sigma.ι (fun i => (U i).left) i ≫ Sigma.desc (fun i => (U i).hom)
      rw [Category.id_comp, Sigma.ι_comp_desc]) M q x (hx i)

end OriginalCover

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
