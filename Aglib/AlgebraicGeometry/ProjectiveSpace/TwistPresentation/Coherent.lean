/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Epimorphism
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent

/-!
# Coherent kernels of finite negative-twist presentations

Over a Noetherian base ring, finite-coordinate polynomial projective space is locally
Noetherian. The original kernel of the constructed finite negative-twist epimorphism is
therefore coherent. Its native kernel sequence is short exact, with the original inclusion
and quotient map. No cohomological finiteness or vanishing premise enters this construction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Finite ι]

/-- A finite native coproduct of twists is coherent on polynomial projective space over a
Noetherian ring. The individual twist property comes from its original local rank-one bases. -/
theorem twistingCoproduct_affineLocallyFiniteType {I : Type u} [Finite I] (d : I → ℤ) :
    affineLocallyFiniteType (ProjectiveSpace R ι) (∐ fun a => twistingSheaf R ι (d a)) :=
  (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_coproduct
    (fun a => Scheme.Modules.coherent_of_finiteLocallyFree (twistingSheaf R ι (d a)))

/-- The actual kernel of a map from a finite sum of twists to a coherent module is coherent. -/
theorem negativeTwistKernel_affineLocallyFiniteType {I : Type u} [Finite I] (N : I → ℕ)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (π : (∐ fun a => twistingSheaf R ι (-(N a : ℤ))) ⟶ M) :
    affineLocallyFiniteType (ProjectiveSpace R ι) (kernel π) :=
  (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_kernel π
    (twistingCoproduct_affineLocallyFiniteType R ι (fun a => -(N a : ℤ))) hM

/-- A coherent module has an actual short exact presentation by one common negative twist
beyond any prescribed bound, and its original kernel is coherent. -/
theorem exists_uniformNegativeTwistCoherentPresentation
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ ∃ (I : Type u) (_ : Finite I)
      (π : (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ))) ⟶ M),
      (ShortComplex.kernelSequence π).ShortExact ∧
        affineLocallyFiniteType (ProjectiveSpace R ι) (kernel π) := by
  obtain ⟨N, hN, I, hI, π, hπ, _⟩ := exists_uniformNegativeTwistEpimorphism R ι M hM B
  let := hI
  refine ⟨N, hN, I, hI, π, ?_,
    negativeTwistKernel_affineLocallyFiniteType R ι (fun _ : I => N) M hM π⟩
  exact { exact := ShortComplex.kernelSequence_exact π, epi_g := hπ }

/-- Every coherent module on finite-coordinate polynomial projective space over a
Noetherian ring has an actual short exact negative-twist presentation with coherent kernel. -/
theorem exists_negativeTwistCoherentPresentation
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ (I : Type u) (_ : Finite I) (N : I → ℕ)
      (π : (∐ fun a => twistingSheaf R ι (-(N a : ℤ))) ⟶ M),
      (ShortComplex.kernelSequence π).ShortExact ∧
        affineLocallyFiniteType (ProjectiveSpace R ι) (kernel π) := by
  obtain ⟨N, _, I, hI, π, hπ⟩ :=
    exists_uniformNegativeTwistCoherentPresentation R ι M hM 0
  exact ⟨I, hI, fun _ => N, π, hπ⟩

/-- Both stages of an actual two-step coherent presentation can use common negative degrees
beyond a prescribed bound. The relation is the original map into the actual kernel followed
by its inclusion, so the displayed native short complex is exact. -/
theorem exists_uniformNegativeTwistTwoStepPresentation
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ ∃ L : ℕ, B ≤ L ∧
      ∃ (I : Type u) (_ : Finite I) (J : Type u) (_ : Finite J)
      (d : (∐ fun _ : J => twistingSheaf R ι (-(L : ℤ))) ⟶
        (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ))))
      (π : (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ))) ⟶ M)
      (hd : d ≫ π = 0),
      (ShortComplex.mk d π hd).Exact ∧ Epi π := by
  obtain ⟨N, hN, I, hI, π, hπ, hK⟩ :=
    exists_uniformNegativeTwistCoherentPresentation R ι M hM B
  let := hI
  obtain ⟨L, hL, J, hJ, ρ, hρ, _⟩ :=
    exists_uniformNegativeTwistEpimorphism R ι (kernel π) hK B
  let := hJ
  let d := ρ ≫ kernel.ι π
  have hd : d ≫ π = 0 := by simp [d]
  let S := ShortComplex.mk d π hd
  have hlift : kernel.lift π d hd = ρ := by
    apply (cancel_mono (kernel.ι π)).mp
    simp only [kernel.lift_ι]
    rfl
  refine ⟨N, hN, L, hL, I, hI, J, hJ, d, π, hd, ?_, hπ.epi_g⟩
  apply S.exact_iff_epi_kernel_lift.mpr
  change Epi (kernel.lift π d hd)
  rw [hlift]
  exact hρ

/-- Applying the proved finite-twist epimorphism to the actual coherent kernel gives a
two-step finite-twist presentation, with its original relation and quotient morphisms. -/
theorem exists_negativeTwistTwoStepPresentation
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ (I : Type u) (_ : Finite I) (N : I → ℕ)
      (J : Type u) (_ : Finite J) (L : J → ℕ)
      (d : (∐ fun b => twistingSheaf R ι (-(L b : ℤ))) ⟶
        (∐ fun a => twistingSheaf R ι (-(N a : ℤ))))
      (π : (∐ fun a => twistingSheaf R ι (-(N a : ℤ))) ⟶ M)
      (hd : d ≫ π = 0),
      (ShortComplex.mk d π hd).Exact ∧ Epi π := by
  obtain ⟨N, _, L, _, I, hI, J, hJ, d, π, hd, h⟩ :=
    exists_uniformNegativeTwistTwoStepPresentation R ι M hM 0
  exact ⟨I, hI, fun _ => N, J, hJ, fun _ => L, d, π, hd, h⟩

end AlgebraicGeometry.ProjectiveSpace
