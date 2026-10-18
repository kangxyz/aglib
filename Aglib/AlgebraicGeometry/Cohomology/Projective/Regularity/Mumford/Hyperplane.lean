/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.HyperplaneStep

/-!
# Hyperplane sections kept on projective space

Let `μ : O(-1) ⊗ - ⟶ 𝟭` be a natural transformation of endofunctors of modules on projective
space; in the application `μ` is multiplication by a linear form `h`. The hyperplane section
of a module `M` is `M_H = coker μ_M`, a module on `P^n` (the pushforward of Nitsure's restriction
`M|_H`, which is never formed here). `hyperplaneSequence μ M` is the sequence
`0 → O(-1) ⊗ M → M → M_H → 0`; it is short exact when `μ_M` is a monomorphism, that is, when
`h` is a nonzerodivisor on `M` (Nitsure, arXiv:math/0504590v1, p. 9).

For a monomorphism `j : F ⟶ G` with `μ_G` and `μ_{G/F}` monomorphisms, `μ_F` is a monomorphism
(`mono_app_of_mono`) and the induced map `F_H ⟶ G_H` is a monomorphism
(`mono_hyperplaneCokernelMap`), by the snake lemma: its kernel is a quotient of
`ker μ_{G/F} = 0`. This is the step "`F_H` is a subsheaf of `O_H^p`" of Nitsure's proof of
Thm 2.3 (p. 12), where `Tor₁(O_H, O^p/F) = 0` is the condition that `μ` is injective on `O^p/F`.

Over a field, `projectiveHilbertFunction_hyperplane` gives
`χ(M_H(r)) = χ(M(r)) - χ(M(r - 1))` for coherent `M`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

section Ring

variable {R : Type u} [CommRing R] {ι : Type u}
  (μ : moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1)) ⟶
    𝟭 (ProjectiveSpace R ι).Modules)

/-- The hyperplane sequence `O(-1) ⊗ M → M → M_H` of `μ`, with `M_H = coker μ_M`. -/
abbrev hyperplaneSequence (M : (ProjectiveSpace R ι).Modules) :
    ShortComplex (ProjectiveSpace R ι).Modules :=
  ShortComplex.cokernelSequence (μ.app M)

/-- The hyperplane sequence is short exact when `μ_M` is a monomorphism. -/
theorem hyperplaneSequence_shortExact (M : (ProjectiveSpace R ι).Modules) [Mono (μ.app M)] :
    (hyperplaneSequence μ M).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _, mono_f := inferInstanceAs (Mono (μ.app M)) }

variable {μ}

/-- `O(-1) ⊗ -` preserves monomorphisms. -/
theorem mono_twistingTensor_map {F G : (ProjectiveSpace R ι).Modules} (j : F ⟶ G) [Mono j]
    (d : ℤ) : Mono ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map j) :=
  (tensor_shortExact_finiteLocallyFree (twistingSheaf R ι d) (ShortComplex.cokernelSequence j)
    { exact := ShortComplex.cokernelSequence_exact _, mono_f := inferInstanceAs (Mono j) }).mono_f

/-- If `j : F ⟶ G` and `μ_G` are monomorphisms, so is `μ_F`. -/
theorem mono_app_of_mono {F G : (ProjectiveSpace R ι).Modules} (j : F ⟶ G) [Mono j]
    [Mono (μ.app G)] : Mono (μ.app F) := by
  have := mono_twistingTensor_map j (-1)
  have h : μ.app F ≫ j =
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map j ≫ μ.app G :=
    (μ.naturality j).symm
  have : Mono (μ.app F ≫ j) := by
    rw [h]
    infer_instance
  exact mono_of_mono (μ.app F) j

variable (μ)

/-- The induced map `F_H ⟶ G_H` of hyperplane sections. -/
abbrev hyperplaneCokernelMap {F G : (ProjectiveSpace R ι).Modules} (j : F ⟶ G) :
    cokernel (μ.app F) ⟶ cokernel (μ.app G) :=
  cokernel.map (μ.app F) (μ.app G)
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map j) j
    (μ.naturality j).symm

/-- The snake input of `μ` on the sequence `0 → F → G → G/F → 0`: kernels and cokernels of
`μ_F`, `μ_G`, `μ_{G/F}`. -/
def hyperplaneSnakeInput {F G : (ProjectiveSpace R ι).Modules} (j : F ⟶ G) [Mono j] :
    ShortComplex.SnakeInput (ProjectiveSpace R ι).Modules where
  L₀ :=
    { f := kernel.map (μ.app F) (μ.app G)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map j) j
        (μ.naturality j).symm
      g := kernel.map (μ.app G) (μ.app (cokernel j))
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map
          (cokernel.π j)) (cokernel.π j) (μ.naturality (cokernel.π j)).symm
      zero := by
        rw [← cancel_mono (kernel.ι (μ.app (cokernel j)))]
        simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, zero_comp]
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero] }
  L₁ := (ShortComplex.cokernelSequence j).map
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1)))
  L₂ := ShortComplex.cokernelSequence j
  L₃ :=
    { f := hyperplaneCokernelMap μ j
      g := hyperplaneCokernelMap μ (cokernel.π j)
      zero := by
        rw [← cancel_epi (cokernel.π (μ.app F))]
        simp only [Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc,
          cokernel.condition_assoc, comp_zero, zero_comp] }
  v₀₁ :=
    { τ₁ := kernel.ι _
      τ₂ := kernel.ι _
      τ₃ := kernel.ι _
      comm₁₂ := (kernel.lift_ι _ _ _).symm
      comm₂₃ := (kernel.lift_ι _ _ _).symm }
  v₁₂ :=
    { τ₁ := μ.app F
      τ₂ := μ.app G
      τ₃ := μ.app (cokernel j)
      comm₁₂ := (μ.naturality j).symm
      comm₂₃ := (μ.naturality (cokernel.π j)).symm }
  v₂₃ :=
    { τ₁ := cokernel.π _
      τ₂ := cokernel.π _
      τ₃ := cokernel.π _
      comm₁₂ := cokernel.π_desc _ _ _
      comm₂₃ := cokernel.π_desc _ _ _ }
  w₀₂ := by
    apply ShortComplex.hom_ext
    · exact kernel.condition _
    · exact kernel.condition _
    · exact kernel.condition _
  w₁₃ := by
    apply ShortComplex.hom_ext
    · exact cokernel.condition _
    · exact cokernel.condition _
    · exact cokernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
  L₁_exact := (tensor_shortExact_finiteLocallyFree (twistingSheaf R ι (-1))
    (ShortComplex.cokernelSequence j)
    { exact := ShortComplex.cokernelSequence_exact _, mono_f := inferInstanceAs (Mono j) }).exact
  epi_L₁_g := (tensor_shortExact_finiteLocallyFree (twistingSheaf R ι (-1))
    (ShortComplex.cokernelSequence j)
    { exact := ShortComplex.cokernelSequence_exact _, mono_f := inferInstanceAs (Mono j) }).epi_g
  L₂_exact := ShortComplex.cokernelSequence_exact _
  mono_L₂_f := inferInstanceAs (Mono j)

/-- **Hyperplane sections of subobjects** (Nitsure, arXiv:math/0504590v1, p. 12): if
`j : F ⟶ G` is a monomorphism and `μ` is a monomorphism on `G/F`, the induced map of
hyperplane sections `F_H ⟶ G_H` is a monomorphism. -/
theorem mono_hyperplaneCokernelMap {F G : (ProjectiveSpace R ι).Modules} (j : F ⟶ G) [Mono j]
    [Mono (μ.app (cokernel j))] : Mono (hyperplaneCokernelMap μ j) := by
  let SI := hyperplaneSnakeInput μ j
  have hz : IsZero SI.L₀.X₃ := isZero_kernel_of_mono (μ.app (cokernel j))
  exact SI.L₂'_exact.mono_g (hz.eq_of_src _ _)

end Ring

section Field

variable {k : Type u} [Field k] {ι : Type u}
  (μ : moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1)) ⟶
    𝟭 (ProjectiveSpace k ι).Modules)

/-- Hyperplane sections of coherent modules are coherent. -/
theorem hyperplane_affineLocallyFiniteType [Finite ι]
    {M : (ProjectiveSpace k ι).Modules} (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M) :
    affineLocallyFiniteType (ProjectiveSpace k ι) (cokernel (μ.app M)) :=
  (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel (μ.app M)
    (twistingTensor_affineLocallyFiniteType k ι (-1) M hM) hM

/-- **Hilbert function of a hyperplane section**: if `μ_M` is a monomorphism and `M` is
coherent, `χ(M_H(r)) = χ(M(r)) - χ(M(r - 1))` (Nitsure, arXiv:math/0504590v1, p. 12). -/
theorem projectiveHilbertFunction_hyperplane (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace k ι).Modules) [Mono (μ.app M)]
    (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M) (r : ℤ) :
    projectiveHilbertFunction k ι (cokernel (μ.app M)) r =
      projectiveHilbertFunction k ι M r - projectiveHilbertFunction k ι M (r - 1) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hT := tensor_shortExact_finiteLocallyFree (twistingSheaf k ι r) _
    (hyperplaneSequence_shortExact μ M)
  have h₁ := twistingTensor_affineLocallyFiniteType k ι r _
    (twistingTensor_affineLocallyFiniteType k ι (-1) M hM)
  have h₂ := twistingTensor_affineLocallyFiniteType k ι r M hM
  have h₃ := twistingTensor_affineLocallyFiniteType k ι r _
    (hyperplane_affineLocallyFiniteType μ hM)
  have hadd := projectiveEulerChar_add_of_shortExact k ι n e _ hT h₁ h₂ h₃
  have hc := projectiveEulerChar_congr k ι ((twistingTensorCompIso k ι r (-1)).app M)
  simp only [Functor.comp_obj] at hc
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.cokernelSequence_X₁, ShortComplex.cokernelSequence_X₂,
    ShortComplex.cokernelSequence_X₃, Functor.id_obj] at hadd
  unfold projectiveHilbertFunction
  rw [show r - 1 = r + -1 by ring, ← hc]
  omega

end Field

end AlgebraicGeometry.Scheme.Cohomology
