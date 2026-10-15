/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules

/-!
# Serre vanishing for actual coherent modules on polynomial projective space

An actual coherent module over a Noetherian base has vanishing positive cohomology after
all sufficiently large tensor twists. The single bound works in every positive degree.
The proof uses the actual finite negative-twist presentations, the original exact tensor
functor and long exact cohomology sequence, and the proved coordinate-cover bound. Its
cohomology groups are the unchanged native `Sheaf.H`, in every dimension and universe.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original tensor twist of a finite twist sum has zero positive cohomology when all
its sum degrees obey the sharp twist bound. -/
theorem twistingTensorCoproductCohomology_subsingleton {I : Type u} [Finite I]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a : ℤ) (d : I → ℤ) (q : ℕ)
    (hd : ∀ i, -(n : ℤ) ≤ a + d i) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (∐ fun i => twistingSheaf R ι (d i)))) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  let : Subsingleton (H.obj (∐ fun i => twistingSheaf R ι (a + d i))) :=
    twistingCoproductCohomology_subsingleton_of_neg_le_degree R ι n e
      (fun i => a + d i) q hd hq
  exact (H.mapIso (twistingTensorCoproductIso R ι a d)).toLinearEquiv.injective.subsingleton

variable [IsNoetherianRing R]

/-- Serre vanishing over every Noetherian base ring: one bound kills every positive
original cohomology group of all larger actual tensor twists of a coherent module.
The explicit coordinate labeling includes dimension zero and arbitrary universes. -/
theorem projectiveSerreVanishing (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M)) q) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hzero (N : (ProjectiveSpace R ι).Modules)
      (hN : affineLocallyFiniteType (ProjectiveSpace R ι) N) (d : ℤ)
      (q : ℕ) (hq : n < q) :
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj N)) q) := by
    let T := (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj N
    have hT := twistingTensor_affineLocallyFiniteType R ι d N hN
    let : T.IsQuasicoherent := quasicoherent_of_affineCharts T (fun A j _ => (hT A j).1)
    exact projectiveCohomology_subsingleton_of_gt R ι n e T q hq
  have hvan : ∀ k ≤ n + 1, ∀ N : (ProjectiveSpace R ι).Modules,
      affineLocallyFiniteType (ProjectiveSpace R ι) N →
      ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, k ≤ q → q ≠ 0 →
        Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj N)) q) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      intro N hN
      refine ⟨0, fun d _ q hq _ => ?_⟩
      exact hzero N hN d q (by omega)
    | of_succ k hk ih =>
      intro N hN
      obtain ⟨m, _, I, hI, π, hπ, hK⟩ :=
        exists_uniformNegativeTwistCoherentPresentation R ι N hN 0
      let := hI
      obtain ⟨B, hB⟩ := ih (kernel π) hK
      refine ⟨max B m, ?_⟩
      intro d hd q hkq hq
      let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)
      let S := (ShortComplex.kernelSequence π).map T
      have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree
        (twistingSheaf R ι d) (ShortComplex.kernelSequence π) hπ
      have hsource : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
          S.X₂) q) := by
        apply twistingTensorCoproductCohomology_subsingleton R ι n e d
          (fun _ : I => -(m : ℤ)) q _ hq
        intro i
        have hm := le_max_right B m
        omega
      have hkernel : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
          S.X₁) (q + 1)) := by
        apply hB d _ (q + 1) (by omega) (by omega)
        have hBmax := le_max_left B m
        omega
      let := hsource
      let := hkernel
      let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₂ q
      let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₃ q
      let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₁ (q + 1)
      have hex := moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace R ι) α S hS q
      have hsurj : Function.Surjective
          (moduleCohomologyMapOfHom (ProjectiveSpace R ι) α S.g q) :=
        (LinearMap.surjective_iff_eq_zero_of_exact hex).mpr (Subsingleton.elim _ _)
      exact hsurj.subsingleton
  obtain ⟨B, hB⟩ := hvan 0 (Nat.zero_le _) M hM
  exact ⟨B, fun d hd q hq => hB d hd q (Nat.zero_le _) hq⟩

end AlgebraicGeometry.Scheme.Cohomology
