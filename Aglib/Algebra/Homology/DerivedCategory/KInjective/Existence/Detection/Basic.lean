/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Detection.Stages
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Colimit
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Detection of native K-injectivity by the constructed small family

The detecting property is proved from the exhaustive source filtration,
not supplied as a hypothesis or new typeclass. The same shift-closed family
is available to the replacement map-killing construction.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K I : CochainComplex C ℤ}

/-- Degree-zero exactness of the native Hom complex supplies an actual homotopy. -/
lemma nullhomotopy_of_acyclic (h : (HomComplex K I).Acyclic) (f : K ⟶ I) :
    Nonempty (Homotopy f 0) := by
  have he := ((HomComplex K I).exactAt_iff' (-1) 0 1 (by simp) (by simp)).1 (h 0)
  obtain ⟨b, hb⟩ := ((HomComplex K I).sc' (-1) 0 1).ab_exact_iff.mp he
    (Cochain.ofHom f) (by change δ 0 1 (Cochain.ofHom f) = 0; simp)
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨b, ?_⟩⟩
  change δ (-1) 0 b = Cochain.ofHom f at hb
  simpa using hb.symm

end CochainComplex.HomComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]

/-- The actual small tests detect all degrees for every acyclic source. -/
lemma homComplex_acyclic_of_smallAcyclicTests
    (hI : ∀ i (f : smallAcyclicTests hG i ⟶ I), Nonempty (Homotopy f 0))
    (M : CochainComplex C ℤ) (hM : M.Acyclic) : (HomComplex M I).Acyclic := by
  let F := acyclicFiltration hG M hM
  have (j : acyclicFiltrationIndex hG M hM) :
      Mono (HomComplex.sourcePredecessorComparison F j) :=
    HomComplex.sourcePredecessorComparison_mono_of_monoOver
      (acyclicStagesFunctor hG M hM) j
  have hc : (HomComplex (colimit F) I).Acyclic :=
    HomComplex.acyclic_colimit_of_wellFounded F I wellFounded_lt
      (fun j => acyclicStages_homComplex_acyclic hG M hM I
        (smallAcyclicTests_homComplex_acyclic hG I hI) j)
  exact HomComplex.acyclic_of_source_iso I (acyclicFiltrationColimitIso hG M hM).symm hc

/-- Native K-injectivity is detected by the constructed single small family. -/
theorem isKInjective_of_smallAcyclicTests
    (hI : ∀ i (f : smallAcyclicTests hG i ⟶ I), Nonempty (Homotopy f 0)) :
    I.IsKInjective where
  nonempty_homotopy_zero {M} f hM :=
    HomComplex.nullhomotopy_of_acyclic
      (homComplex_acyclic_of_smallAcyclicTests hG I hI M hM) f

end CochainComplex
