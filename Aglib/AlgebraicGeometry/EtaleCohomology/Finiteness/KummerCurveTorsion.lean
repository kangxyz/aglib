/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.KummerChartFiniteValues

/-! # Finite prime-to-characteristic Picard torsion of a smooth proper curve

The actual finite Kummer chart cover realizes all original torsion line
bundles. Each chart has finite image by proper-henselian H1 rigidity and
continuity. Their finite union bounds the original Picard torsion subgroup;
no Picard representability or proper base change hypothesis is inserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
open GroupCohomology.Kummer.Coefficients

universe u
namespace AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hX : Properties X)

include o ho hX

/-- Finitely many original Kummer classes map onto all original positive
invertible-level torsion line-bundle classes. -/
theorem exists_finset_kummer_preimages (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    ∃ S : Finset (H1Etale.{u, u + 1, u + 2} X.left (mu X.left n)),
      ∀ L : LineBundle X.left, n • classOf X.left L = 0 →
        ∃ c ∈ S, Sheaf.H.map (inclusion X.left n) 1 c =
          Picard.picardCohomologyEquiv X.left (classOf X.left L) := by
  classical
  let : DecidableEq (H1Etale.{u, u + 1, u + 2} X.left (mu X.left n)) :=
    Classical.decEq _
  let := hX.smooth
  let := hX.proper
  let := hX.connected
  let : ConnectedSpace X.left := GeometricallyConnected.connectedSpace_of_subsingleton X.hom
  obtain ⟨s, C, _, hC⟩ := exists_finite_kummer_families_realizing_torsion X o ho hX n hn hunit
  choose S hS using fun i : s => exists_finset_chart_roots_values X o ho (C i) hn hunit
  refine ⟨Finset.univ.biUnion S, ?_⟩
  intro L hL
  obtain ⟨i, b, a, hpb, hb, haX, hc⟩ := hC L hL
  refine ⟨Kummer.rootsCohomologyPullback a n hn ((C i).levelInvertible hunit) 1
    (C i).cohomologyClass, ?_, hc⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hS i b hb a haX hpb.w⟩

/-- The actual n-torsion subset of the original Picard group is finite.
The curve has its supplied rational point, and n is positive and invertible. -/
theorem finite_picard_torsion (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Set.Finite {c : PicardGroup X.left | n • c = 0} := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_kummer_preimages X o ho hX n hn hunit
  let image : H1Etale.{u, u + 1, u + 2} X.left (mu X.left n) → PicardGroup X.left :=
    fun c => (Picard.picardCohomologyEquiv X.left).symm
      (Sheaf.H.map (inclusion X.left n) 1 c)
  apply (S.finite_toSet.image image).subset
  intro c hc
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  obtain ⟨a, ha, he⟩ := hS L hc
  refine ⟨a, ha, ?_⟩
  exact (congrArg (Picard.picardCohomologyEquiv X.left).symm he).trans
    ((Picard.picardCohomologyEquiv X.left).symm_apply_apply _)

end AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues
