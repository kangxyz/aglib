/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsProducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SupportedFamilyColimit

/-! # Acyclicity of filtered colimits of injective étale sheaves on qcqs schemes

The full original small étale site is retained. Only its qcqs objects are used
for finite tuple cochains and section lifting. Thus arbitrary non-qc objects
of the site are not incorrectly assumed to have finite covering refinements.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe e u

attribute [local instance] hasSheafifyLarge

/-- The supported objects of the original small étale site. -/
def qcqsObjects (S : Scheme.{u}) (U : S.Etale) : Prop :=
  CompactSpace U.left ∧ QuasiSeparatedSpace U.left

/-- Covering sieves over qcqs objects have finite qcqs refinements in the original site. -/
theorem qcqsObjects_finiteRefinements (S : Scheme.{u}) :
    HasFiniteSupportedRefinements (J := S.smallEtaleTopology) (qcqsObjects S) := by
  intro W hW R hR
  let : CompactSpace W.left := hW.1
  obtain ⟨ι, hι, V, f, hV, hf, hcov⟩ :=
    EtaleAffineBasis.exists_finite_affine_family W R hR
  let : Finite ι := hι
  let U : ULift.{u + 1} ι → Over W := fun i => Over.mk (f i.down)
  refine ⟨ULift.{u + 1} ι, inferInstance, U, ?_, ?_, fun i => hf i.down⟩
  · intro i
    let : IsAffine (V i.down).left := hV i.down
    change CompactSpace (V i.down).left ∧ QuasiSeparatedSpace (V i.down).left
    exact ⟨inferInstance, inferInstance⟩
  · apply S.smallEtaleTopology.superset_covering (S := Sieve.ofArrows V f) ?_ hcov
    intro Z g hg
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
    exact (Sieve.ofArrows (fun j => (U j).left) (fun j => (U j).hom)).downward_closed
      (Sieve.ofArrows_mk _ _ (ULift.up i)) a

/-- Finite tuple products stay in the actual qcqs part of the small site. -/
theorem qcqsObjects_tupleProducts (S : Scheme.{u}) :
    SupportedTupleProducts (qcqsObjects S) := by
  intro W hW ι _ U hU n a
  exact qcqs_product W hW (fun i => U (a i)) (fun i => hU (a i))

variable {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

/-- Actual filtered colimits of injective sheaves satisfy supported acyclicity. -/
theorem qcqs_colimit_injective_supported_acyclic
    (G : I ⥤ AbelianSheaf.{u, u + 1} S) [HasColimit G]
    [∀ i, Injective (G.obj i)] :
    SupportedFamilyCechAcyclic (qcqsObjects S) (Limits.colimit G) := by
  apply supportedFamilyCechAcyclic_colimit_of_injective (qcqsObjects S)
    (qcqsObjects_tupleProducts S) _ G
  intro U hU
  let : CompactSpace U.left := hU.1
  let : QuasiSeparatedSpace U.left := hU.2
  exact qcqsSectionsPreservesFilteredColimits (I := I) U

variable [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]

/-- On any qcqs scheme, filtered colimits of injective original étale sheaves
have vanishing positive original global cohomology, with independent Ext universe. -/
theorem qcqs_colimit_injective_cohomology_eq_zero
    [CompactSpace S] [QuasiSeparatedSpace S]
    (G : I ⥤ AbelianSheaf.{u, u + 1} S) [HasColimit G]
    [∀ i, Injective (G.obj i)] (n : ℕ)
    (x : Sheaf.H.{e} (Limits.colimit G) (n + 1)) : x = 0 := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} S) := abelianSheaf_enoughInjectives S
  have hqcqs : qcqsObjects S (etaleTerminal S) := by
    change CompactSpace S ∧ QuasiSeparatedSpace S
    exact ⟨inferInstance, inferInstance⟩
  exact (qcqs_colimit_injective_supported_acyclic G).cohomology_eq_zero (qcqsObjects S)
    (qcqsObjects_finiteRefinements S) (qcqsObjects_tupleProducts S)
    hqcqs (etaleTerminalIsTerminal S) n x

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
