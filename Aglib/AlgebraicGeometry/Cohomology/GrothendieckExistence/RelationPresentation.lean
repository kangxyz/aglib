/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProjectivePresentation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationCoverBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TowerCoverGeneration

/-!
# A fixed algebraic negative-twist cover of the ordinary relation diagram

Unlike a coherent adic system, the ordinary relation diagram need not be
cartesian. Its proved finite-cover kernel bound chooses the stage at which
to lift generators. Nilpotent generation then supplies all-level epimorphy.
Only the uniform relation-kernel H¹ bound remains conditional here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (ι : Type u) [Finite ι]
  (I : Ideal A)

/-- A uniform vanishing bound for the actual successive relation kernels
constructs a componentwise epimorphism from completion of a fixed finite sum
of algebraic negative twists onto the ordinary ambient relation diagram. -/
theorem exists_completion_relation_epi_of_uniform_h1
    {P F : AdicSystem (ProjectiveSpace A ι)
      (idealThickeningIdealSheaf (toSpec A ι) I)} (φ : P ⟶ F)
    (hφ : ∀ n : ℕ, Epi (φ.hom.app (op n))) (B : ℕ)
    (hK : ∀ d : ℕ, B ≤ d → ∀ n, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).obj
          (kernel ((relationDiagram φ).map (homOfLE (Nat.le_succ n)).op)))) 1)) :
    ∃ d : ℕ, B ≤ d ∧ ∃ (J : Type u) (_ : Finite J)
      (r : (ambientCompletion (ProjectiveSpace A ι)
        (idealThickeningIdealSheaf (toSpec A ι) I)).obj
          (finiteNegativeTwistCoefficient A ι J d) ⟶ relationDiagram φ),
      ∀ n : ℕ, Epi (r.app (op n)) := by
  let U (i : ι) : (ProjectiveSpace A ι).affineOpens :=
    ⟨coordinateOpen A ι i, isAffineOpen_coordinateOpen A ι i⟩
  have hU : ∀ x : ProjectiveSpace A ι, ∃ i, x ∈ (U i).val := by
    intro x
    exact Opens.mem_iSup.mp (show x ∈ iSup (coordinateOpen A ι) by
      rw [iSup_coordinateOpen_eq_top]; trivial)
  obtain ⟨k, _, hk⟩ := exists_relationDiagram_kernel_bound_on_finite_family
    (toSpec A ι) I φ U hφ
  have ht : ∀ n m (h : n ≤ m), Epi ((relationDiagram φ).map (homOfLE h).op) := by
    intro n m h
    let := hφ m
    exact relationDiagram_map_epi φ h
  obtain ⟨d, hd, J, hJ, p, hp⟩ :=
    exists_compatible_negativeTwist_generators_of_uniform_h1 A ι (relationDiagram φ) k
      (relationDiagram_coherent φ k) (fun n => ht n (n + 1) (Nat.le_succ n)) B hK
  let := hJ
  let : (∐ fun _ : J => twistingSheaf A ι (-(d : ℤ))).IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent A ι (fun _ : J => -(d : ℤ))
  let := hp
  have hep (n : ℕ) : Epi (p.app (op n)) :=
    compatible_epi_of_affineCover_kernel_bound U hU
      (idealThickeningIdealSheaf (toSpec A ι) I) (relationDiagram φ)
      (fun n => relationDiagram_isQuasicoherent φ n) p k ht
      (relationDiagram_killed φ) (fun n h j => hk j n h) n
  let r := compatibleQuotientDesc (idealThickeningIdealSheaf (toSpec A ι) I)
    (relationDiagram_killed φ) p
  refine ⟨d, hd, J, hJ, r, ?_⟩
  intro n
  let := hep n
  exact compatibleQuotientDesc_app_epi
    (idealThickeningIdealSheaf (toSpec A ι) I) (relationDiagram_killed φ) p (op n)

end AlgebraicGeometry.Scheme.Cohomology
