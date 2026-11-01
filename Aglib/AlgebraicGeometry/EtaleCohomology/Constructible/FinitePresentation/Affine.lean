/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentation.FiniteGeneration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteEtalePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure

/-! # Ordinary finite presentation of constructible coefficients on separated qc schemes

The original positive bounded presentation has constructible, ordinarily
finitely presentable stages on a separated base. Finite generation selects
an epimorphic stage. Its kernel remains constructible, so a second such
selection supplies a finitely presentable relation object. The original
coefficient is their actual cokernel, hence ordinarily finitely presentable.

This proves the affine case needed by the global finite-cogenerator consumer.
The separated hypothesis in the generator producer is retained explicitly;
no result on arbitrary nonseparated qcqs bases is claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

/-- An actual constructible coefficient on a quasi-compact separated scheme
is a quotient of an original constructible, ordinarily finitely presentable
coefficient. No compactness of the given target is used. -/
theorem exists_epi_from_constructible_finitelyPresentable
    {X : Scheme.{u}} [CompactSpace X] [IsSeparated (terminal.from X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    ∃ (P : AbelianSheaf.{u, u + 1} X) (q : P ⟶ F),
      IsConstructible P ∧ IsFinitelyPresentable.{u + 1} P ∧ Epi q := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (terminal.from X)
  obtain ⟨n, hn, hkill⟩ := exists_positive_annihilator_of_isConstructible F hF
  have hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom := by
    intro U
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact PositivePresentation.finiteEtalePartitions_of_isAffine_of_isSeparated _
  obtain ⟨I, hI, hfilt, D, ι, hc, hstage⟩ :=
    PositivePresentation.exists_filtered_presentation_constructible_of_finiteEtalePartitions
      X n (Nat.ne_of_gt hn) hparts F hkill
  let := hI
  have : IsFiltered I := hfilt
  obtain ⟨i, hi⟩ := exists_epi_of_isColimit_of_isConstructible hc.some hF
  exact ⟨(D.obj i).obj, ι.app i, (hstage i).2.2, (hstage i).2.1, hi⟩

/-- A genuine constructible abelian sheaf on a quasi-compact separated scheme
is finitely presentable in the original abelian sheaf category at size u+1. -/
theorem isFinitelyPresentable_of_isConstructible_of_isSeparated
    {X : Scheme.{u}} [CompactSpace X] [IsSeparated (terminal.from X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    IsFinitelyPresentable.{u + 1} F := by
  obtain ⟨P, q, hP, hFP, hq⟩ := exists_epi_from_constructible_finitelyPresentable F hF
  have : Epi q := hq
  obtain ⟨R, r, _, hFR, hr⟩ := exists_epi_from_constructible_finitelyPresentable
    (kernel q) (isConstructible_kernel q hP hF)
  have : Epi r := hr
  let d : R ⟶ P := r ≫ kernel.ι q
  have hd : d ≫ q = 0 := by simp [d, Category.assoc]
  have hc : IsColimit (CokernelCofork.ofπ q hd) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)) r rfl
  have (j : WalkingParallelPair) :
      IsFinitelyPresentable.{u + 1} ((parallelPair d 0).obj j) := by
    cases j with
    | zero => exact hFR
    | one => exact hFP
  exact isCardinalPresentable_of_isColimit' (CokernelCofork.ofπ q hd) hc
    Cardinal.aleph0.{u + 1} ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

/-- The ordinary affine constructible-to-FP implication, with no Noetherian
hypothesis and no replacement of the original abelian sheaf category. -/
theorem isFinitelyPresentable_of_isConstructible_of_isAffine
    {X : Scheme.{u}} [IsAffine X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_isConstructible_of_isSeparated F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
