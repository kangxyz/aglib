/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Modules

/-!
# Coherent cohomological finiteness on polynomial projective space

Over a Noetherian ring, every coherent module on actual polynomial projective space has
finite original cohomology in every nonnegative degree. The proof descends from the native
affine-cover bound through actual finite negative-twist presentations with coherent kernels.
The long exact sequence and scalar action are the original ones; no finiteness family,
assumed Serre vanishing or bounded-resolution hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)

/-- Every original cohomology module of a coherent module on polynomial projective
`n`-space over a Noetherian ring is finite over the structural base ring. The explicit
coordinate labeling preserves arbitrary universes and includes dimension zero. -/
theorem projectiveCohomology_finite (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M q
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hzero (k : ℕ) (hk : n < k) (N : (ProjectiveSpace R ι).Modules)
      (hN : affineLocallyFiniteType (ProjectiveSpace R ι) N) :
      letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α N k
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) N) k) := by
    let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α N k
    let : N.IsQuasicoherent := quasicoherent_of_affineCharts N (fun A j _ => (hN A j).1)
    let := projectiveCohomology_subsingleton_of_gt R ι n e N k hk
    infer_instance
  have hfinite : ∀ k ≤ n + 1, ∀ N : (ProjectiveSpace R ι).Modules,
      affineLocallyFiniteType (ProjectiveSpace R ι) N →
      letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α N k
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) N) k) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact hzero (n + 1) (Nat.lt_succ_self n)
    | of_succ k hk ih =>
      intro N hN
      obtain ⟨I, hI, d, π, hπ, hK⟩ := exists_negativeTwistCoherentPresentation R ι N hN
      let := hI
      exact moduleCohomology_finite_quotient_of_hom (ProjectiveSpace R ι) α
        (ShortComplex.kernelSequence π) hπ k
        (twistingCoproductCohomology_finite R ι n e (fun a => -(d a : ℤ)) k)
        (ih (kernel π) hK)
  by_cases hq : n < q
  · exact hzero q hq M hM
  · exact hfinite q (by omega) M hM

end AlgebraicGeometry.Scheme.Cohomology
