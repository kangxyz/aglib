/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
/-!
# Actual linear five-term cohomology and quotient Euler comparison

The connecting map is Mathlib's original Sheaf.H delta, proved linear for the
original scheme field action by its naturality. Actual long-exact-sequence
maps prove finite H0/H1 of the kernel and the quotient dimension identity.
H1 of the middle sheaf remains an explicit finite-dimensional input. This
module supplies no unconditional proper-curve product formula or proper H1
finiteness theorem.

Authoring basis3397a339b6a52fbba586dae127aa729d873b771d, Lean4.34.1,
Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, Quillen0.7
83629578a3d70787d41ec631f5234af8758716af.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.QuotientEuler` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Generic cohomology exactness and
H⁰-injectivity are imported from their unique implementation in `ExactSequences`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField Cohomology
namespace AlgebraicGeometry.Scheme.Cohomology.QuotientEuler.ExactDimensions
variable {k V W Z : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup Z] [Module k Z]
theorem rankNullity (f : V →ₗ[k] W) [Module.Finite k V] :
    Module.finrank k f.range + Module.finrank k f.ker = Module.finrank k V := by
  have h := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq] at h
  exact h

theorem exact_dimensions (f : V →ₗ[k] W) (g : W →ₗ[k] Z)
    (he : Function.Exact f g) [Module.Finite k W] :
    Module.finrank k g.range + Module.finrank k f.range = Module.finrank k W := by
  have h := rankNullity g
  rwa [LinearMap.exact_iff.mp he] at h

theorem range_finrank_of_injective (f : V →ₗ[k] W) (hf : Function.Injective f) :
    Module.finrank k f.range = Module.finrank k V :=
  (LinearEquiv.ofInjective f hf).finrank_eq.symm
end AlgebraicGeometry.Scheme.Cohomology.QuotientEuler.ExactDimensions

namespace AlgebraicGeometry.Scheme.Cohomology.QuotientEuler
universe u
variable {k : Type u} [Field k] (X : FScheme k)
local instance : HasExt.{u + 1}
    (Sheaf (Opens.grothendieckTopology (X.left : TopCat)) AddCommGrpCat.{u}) :=
  structureSheafHasExt X.left
local instance (Y : Scheme.{u}) : (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf
  Y).PreservesZeroMorphisms where
  map_zero := by intros; rfl
/-- The endomorphism of the additive short complex given by a structural field scalar. -/
def moduleScalarSequence (S : ShortComplex X.left.Modules) (a : k) :
    S.map (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left) ⟶
      S.map (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left) where
  τ₁ := moduleScalar X S.X₁ a
  τ₂ := moduleScalar X S.X₂ a
  τ₃ := moduleScalar X S.X₃ a
  comm₁₂ := moduleScalar_naturality X S.f a
  comm₂₃ := moduleScalar_naturality X S.g a

/-- The structural-field-linear H⁰-to-H¹ connecting map of a supplied short exact module
sequence. -/
def moduleConnecting (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    moduleCohomology k X S.X₃ 0 →ₗ[k] moduleCohomology k X S.X₁ 1 := by
  let F := AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left
  let A := S.map F
  have hA : A.ShortExact := AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf hS
  let d : Sheaf.H.{u + 1,u,u,u} (moduleAddSheaf X.left S.X₃) 0 →+
      Sheaf.H.{u + 1,u,u,u} (moduleAddSheaf X.left S.X₁) 1 :=
    @Sheaf.H.δ.{u + 1,u,u,u} X.left.Opens inferInstance
      (Opens.grothendieckTopology X.left) inferInstance (structureSheafHasExt X.left) A hA 0 1 rfl
  refine {toAddHom := d, map_smul' := ?_}
  intro a z
  change d (Sheaf.H.map (moduleScalar X S.X₃ a) 0 z) =
    Sheaf.H.map (moduleScalar X S.X₁ a) 1 (d z)
  exact @Sheaf.H.δ_naturality.{u + 1,u,u,u} X.left.Opens inferInstance
    (Opens.grothendieckTopology X.left) inferInstance (structureSheafHasExt X.left)
    0 1 rfl A A hA hA (moduleScalarSequence X S a) z
theorem moduleConnecting_exact_right (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    Function.Exact (moduleConnecting X S hS) (moduleCohomologyMap X S.f 1) := by
  let : (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left).PreservesZeroMorphisms :=
    ⟨by intros; rfl⟩
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (@Sheaf.H.longSequence_exact₁'.{u + 1,u,u,u} X.left.Opens inferInstance
      (Opens.grothendieckTopology X.left) inferInstance (structureSheafHasExt X.left)
      (S.map (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left))
        (AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf hS) 0 1 rfl)

theorem moduleConnecting_exact_left (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    Function.Exact (moduleCohomologyMap X S.g 0) (moduleConnecting X S hS) := by
  let : (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left).PreservesZeroMorphisms :=
    ⟨by intros; rfl⟩
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (@Sheaf.H.longSequence_exact₃'.{u + 1,u,u,u} X.left.Opens inferInstance
      (Opens.grothendieckTopology X.left) inferInstance (structureSheafHasExt X.left)
      (S.map (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left))
        (AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf hS) 0 1 rfl)

/-- The short complex consisting of a module-sheaf map followed by its actual cokernel
projection. -/
def quotientSequence {M N : X.left.Modules} (f : M ⟶ N) : ShortComplex X.left.Modules :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
theorem quotientSequence_shortExact {M N : X.left.Modules} (f : M ⟶ N) [Mono f] :
    (quotientSequence X f).ShortExact := {
      exact := ShortComplex.exact_cokernel f
      mono_f := by change Mono f; infer_instance
      epi_g := by change Epi (cokernel.π f); infer_instance }

theorem moduleH1Map_surjective (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology k X S.X₃ 1)] :
    Function.Surjective (moduleCohomologyMap X S.f 1) := by
  let : (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left).PreservesZeroMorphisms :=
    ⟨by intros; rfl⟩
  intro y
  exact @Sheaf.H.longSequence_exact₂.{u + 1,u,u,u} X.left.Opens inferInstance
    (Opens.grothendieckTopology X.left) inferInstance (structureSheafHasExt X.left)
    (S.map (AlgebraicGeometry.Scheme.Modules.toAdditiveSheaf X.left))
      (AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf hS) 1 y
    (by exact @Subsingleton.elim (moduleCohomology k X S.X₃ 1) inferInstance _ _)

theorem moduleH0Kernel_finite (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Module.Finite k (moduleCohomology k X S.X₂ 0)] :
    Module.Finite k (moduleCohomology k X S.X₁ 0) := by
  let := hS.mono_f
  exact Module.Finite.of_injective (moduleCohomologyMap X S.f 0) (moduleH0Map_injective X S.f)

theorem moduleH1Kernel_finite (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Module.Finite k (moduleCohomology k X S.X₃ 0)]
    [Module.Finite k (moduleCohomology k X S.X₂ 1)]
    [Subsingleton (moduleCohomology k X S.X₃ 1)] :
    Module.Finite k (moduleCohomology k X S.X₁ 1) :=
  Module.Finite.of_exact (moduleConnecting_exact_right X S hS) (moduleH1Map_surjective X S hS)
theorem moduleEulerQuotient_dim (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Module.Finite k (moduleCohomology k X S.X₂ 0)]
    [Module.Finite k (moduleCohomology k X S.X₃ 0)]
    [Module.Finite k (moduleCohomology k X S.X₂ 1)]
    [Subsingleton (moduleCohomology k X S.X₃ 1)] :
    (Module.finrank k (moduleCohomology k X S.X₃ 0) : ℤ) =
      (Module.finrank k (moduleCohomology k X S.X₂ 0) : ℤ) -
        (Module.finrank k (moduleCohomology k X S.X₁ 0) : ℤ) +
          (Module.finrank k (moduleCohomology k X S.X₁ 1) : ℤ) -
            (Module.finrank k (moduleCohomology k X S.X₂ 1) : ℤ) := by
  let : Module.Finite k (moduleCohomology k X S.X₁ 0) := moduleH0Kernel_finite X S hS
  let : Module.Finite k (moduleCohomology k X S.X₁ 1) := moduleH1Kernel_finite X S hS
  let := hS.mono_f
  let φ := moduleCohomologyMap X S.f 0
  let ψ := moduleCohomologyMap X S.g 0
  let δ := moduleConnecting X S hS
  let η := moduleCohomologyMap X S.f 1
  have hO := ExactDimensions.exact_dimensions φ ψ (moduleCohomologyMap_exact X S hS 0)
  have hQ := ExactDimensions.exact_dimensions ψ δ (moduleConnecting_exact_left X S hS)
  have hI := ExactDimensions.exact_dimensions δ η (moduleConnecting_exact_right X S hS)
  have hφ : Module.finrank k φ.range = Module.finrank k (moduleCohomology k X S.X₁ 0) :=
    ExactDimensions.range_finrank_of_injective φ (moduleH0Map_injective X S.f)
  have hη : Module.finrank k η.range = Module.finrank k (moduleCohomology k X S.X₂ 1) := by
    have hrange : η.range = ⊤ := LinearMap.range_eq_top.mpr (moduleH1Map_surjective X S hS)
    rw [hrange]
    exact (LinearEquiv.ofTop
      (⊤ : Submodule k (moduleCohomology k X S.X₂ 1)) rfl).finrank_eq
  rw [hφ] at hO
  rw [hη] at hI
  have hn : Module.finrank k (moduleCohomology k X S.X₃ 0) +
      Module.finrank k (moduleCohomology k X S.X₁ 0) +
        Module.finrank k (moduleCohomology k X S.X₂ 1) =
          Module.finrank k (moduleCohomology k X S.X₂ 0) +
            Module.finrank k (moduleCohomology k X S.X₁ 1) := by omega
  have hz : (Module.finrank k (moduleCohomology k X S.X₃ 0) : ℤ) +
      (Module.finrank k (moduleCohomology k X S.X₁ 0) : ℤ) +
        (Module.finrank k (moduleCohomology k X S.X₂ 1) : ℤ) =
          (Module.finrank k (moduleCohomology k X S.X₂ 0) : ℤ) +
            (Module.finrank k (moduleCohomology k X S.X₁ 1) : ℤ) := by exact_mod_cast hn
  omega
end AlgebraicGeometry.Scheme.Cohomology.QuotientEuler

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {K : Type u} [Field K] (X : FScheme K)

/-- The actual six-term exact sequence gives the Euler difference after finiteness is known. -/
theorem moduleEuler_of_shortExact (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Module.Finite K (moduleCohomology K X S.X₁ 0)]
    [Module.Finite K (moduleCohomology K X S.X₁ 1)]
    [Module.Finite K (moduleCohomology K X S.X₂ 0)]
    [Module.Finite K (moduleCohomology K X S.X₂ 1)]
    [Module.Finite K (moduleCohomology K X S.X₃ 0)]
    [Subsingleton (moduleCohomology K X S.X₃ 1)] :
    (Module.finrank K (moduleCohomology K X S.X₂ 0) : ℤ) -
      Module.finrank K (moduleCohomology K X S.X₂ 1) =
    ((Module.finrank K (moduleCohomology K X S.X₁ 0) : ℤ) -
      Module.finrank K (moduleCohomology K X S.X₁ 1)) +
      Module.finrank K (moduleCohomology K X S.X₃ 0) := by
  have h : (Module.finrank K (moduleCohomology K X S.X₁ 0) : ℤ) -
      Module.finrank K (moduleCohomology K X S.X₂ 0) +
      Module.finrank K (moduleCohomology K X S.X₃ 0) -
      Module.finrank K (moduleCohomology K X S.X₁ 1) +
      Module.finrank K (moduleCohomology K X S.X₂ 1) -
      Module.finrank K (moduleCohomology K X S.X₃ 1) = 0 :=
    Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six
    (moduleCohomologyMap X S.f 0) (moduleCohomologyMap X S.g 0)
    (moduleCohomologyConnecting X S hS 0)
    (moduleCohomologyMap X S.f 1) (moduleCohomologyMap X S.g 1)
    (moduleH0Map_injective_of_shortExact X S hS) (moduleCohomologyMap_exact X S hS 0)
    (moduleCohomologyConnecting_exact_left X S hS 0)
    (moduleCohomologyConnecting_exact_right X S hS 0)
    (moduleCohomologyMap_exact X S hS 1) (fun x => ⟨0, Subsingleton.elim _ _⟩)
  have hz : Module.finrank K (moduleCohomology K X S.X₃ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hz] at h
  omega

section FiniteClosedSupport
variable {ι : Type} [Finite ι]

/-- Finiteness transfers both ways across an actual finite closed-support quotient. -/
theorem moduleH0H1_finite_iff_of_finiteClosedSupport
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hQ : ∀ x, x ∉ Set.range p → CategoryTheory.Limits.IsZero (moduleAdditiveStalk X S.X₃ x))
    [∀ i, Module.Finite K (moduleAdditiveStalk X S.X₃ (p i))] :
    (Module.Finite K (moduleCohomology K X S.X₁ 0) ∧
      Module.Finite K (moduleCohomology K X S.X₁ 1)) ↔
    (Module.Finite K (moduleCohomology K X S.X₂ 0) ∧
      Module.Finite K (moduleCohomology K X S.X₂ 1)) := by
  let := finiteClosedSupportModuleH0_finite X S.X₃ p hp hclosed hQ
  let := finiteClosedSupportModuleCohomology_positive X S.X₃ p hp hclosed hQ 0
  exact moduleH0H1_finite_iff X S hS

/-- Actual finite-support stalk dimensions give the Euler difference; middle finiteness is
  proved first. -/
theorem moduleEuler_of_finiteClosedSupport
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact) [Fintype ι]
    (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hQ : ∀ x, x ∉ Set.range p → CategoryTheory.Limits.IsZero (moduleAdditiveStalk X S.X₃ x))
    [∀ i, Module.Finite K (moduleAdditiveStalk X S.X₃ (p i))]
    [Module.Finite K (moduleCohomology K X S.X₁ 0)]
    [Module.Finite K (moduleCohomology K X S.X₁ 1)] :
    (Module.finrank K (moduleCohomology K X S.X₂ 0) : ℤ) -
      Module.finrank K (moduleCohomology K X S.X₂ 1) =
    ((Module.finrank K (moduleCohomology K X S.X₁ 0) : ℤ) -
      Module.finrank K (moduleCohomology K X S.X₁ 1)) +
      ∑ i, (Module.finrank K (moduleAdditiveStalk X S.X₃ (p i)) : ℤ) := by
  let := finiteClosedSupportModuleH0_finite X S.X₃ p hp hclosed hQ
  let := finiteClosedSupportModuleCohomology_positive X S.X₃ p hp hclosed hQ 0
  let := moduleCohomology_finite_middle X S hS 0
  let := moduleCohomology_finite_middle X S hS 1
  rw [moduleEuler_of_shortExact X S hS,
    finiteClosedSupportModuleH0_finrank X S.X₃ p hp hclosed hQ]
  simp

end FiniteClosedSupport

end AlgebraicGeometry.Scheme.Cohomology
