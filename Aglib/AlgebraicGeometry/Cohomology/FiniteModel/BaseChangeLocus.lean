/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeCriterion
public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Locus

/-!
# Basic-open original cohomology base change on the same finite-cover model

Surjectivity of the original cohomology comparison at an actual prime's
residue field gives a basic-open neighbourhood where the original comparison
is invertible after every further ring map. The proof localizes the same
supplied finite-projective complex and uses native homology-mate composition.
The geometric maps retain the original morphism, coefficient and ordinary
fibre products. Neither reducedness nor Noetherianity is added to the
supplied-model hypotheses, and the new ring need not be flat or Noetherian.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}} [X.IsSeparated]
  {f : X ⟶ Spec (CommRingCat.of R)} {U : ι → X.Opens}
  {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : FiniteCechCohomologyModel R ι X f U M n)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
  (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)

include D hU hcover e hflat

/-- Surjectivity of the original comparison to the actual residue field at a prime
gives a basic-open neighbourhood on which every factored original cohomology
base-change map is invertible, using the same supplied finite Cech model. -/
theorem exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue
    (q : ℕ) (p : PrimeSpectrum R)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R p.asIdeal.ResidueField) M q)) :
    ∃ r ∉ p.asIdeal,
      ∀ (B : Type u) [CommRing B] (τ : Localization.Away r →+* B),
        IsIso (moduleCohomologyBaseChangeMap f
          (τ.comp (algebraMap R (Localization.Away r))) M q) := by
  let S := D.complex.sc (q : ℤ)
  let : Module.Finite R S.X₂ := D.finite_X (q : ℤ)
  let : Module.Finite R S.X₃ := D.finite_X ((ComplexShape.up ℤ).next (q : ℤ))
  let : Module.Projective R S.X₃ := D.projective_X ((ComplexShape.up ℤ).next (q : ℤ))
  let : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_projective R S.X₃
  have hρ : Epi (ModuleCat.homologyBaseChangeMap.{u, 0, u}
      (algebraMap R p.asIdeal.ResidueField) S) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff hU hcover e hflat _ q).mp hres
  obtain ⟨r, hr, hfree, _⟩ :=
    ShortComplex.exists_basicOpen_homologyBaseChangeMap_isIso_of_epi_residue.{u, 0, u} S p hρ
  refine ⟨r, hr, ?_⟩
  intro B _ τ
  apply (D.moduleCohomologyBaseChangeMap_isIso_iff hU hcover e hflat _ q).mpr
  exact ShortComplex.homologyBaseChangeMap_comp_isIso_of_basicOpen_subset_freeLocus.{u, 0}
    S r hfree τ

end AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel
