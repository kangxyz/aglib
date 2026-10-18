/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.StageModelNaturality

/-!
# Exactness for the original geometric-kernel homomorphism

This realizes the EXISTING `Stacks0BTX F` interface in
`R5Lab/AlgebraicGeometry/FiniteEtale/FundamentalGroup/GeometricKernel.lean`
on governing/source entry `817791c41777784df55e392d45673d08e139898f`.
The forward map is literally the pre-existing `geometricKernelHom`.

Object descent to finite field stages, finite purely inseparable invariance,
and actual Hom descent supply all model data. A kernel element fixes each
selected base-cover point. Its restrictions commute on a common finite
separable field stage, so they extend to an actual natural automorphism of
the original geometric fibre functor. Evaluation on the identity base cover
proves the right inverse. The proved model-embedding criterion gives the
left inverse. No Galois-category, model-existence, arrow-descent, exactness,
characteristic, Noetherian, or connectedness premise is retained.

The exported Stacks interface retains its original qcqs/geometrically
connected/rational-section quantifiers; the proof actually only needs qcqs
and the displayed rational section. Existing compactness and Hausdorffness
supply the inverse continuity for the same homomorphism.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
universe u

section AlgebraicExtension
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (CommRingCat.of K)) (o : Spec (CommRingCat.of K) ⟶ X)
  (ho : o ≫ p = 𝟙 _)

/-- An explicit natural automorphism of the existing geometric fibre functor,
constructed by compatible finite-stage restrictions of the given kernel element. -/
def actualKernelInverse (n : ProjectionKernel (Spec.algebraMap K Ω) p o ho) :
    BaseChangeGroup (Spec.algebraMap K Ω) p o ho :=
  kernelAutFromStageModels (Spec.algebraMap K Ω) p o ho (exists_stageModel K Ω p) n
    (stageModel_components_compatible K Ω p o ho n)

/-- The constructed inverse maps back to the given element under the original map. -/
@[simp] theorem kernelHom_actualKernelInverse (n : ProjectionKernel (Spec.algebraMap K Ω) p o ho) :
    kernelHom (Spec.algebraMap K Ω) p o ho (actualKernelInverse K Ω p o ho n) = n :=
  kernelHom_kernelAutFromStageModels (Spec.algebraMap K Ω) p o ho
    (exists_stageModel K Ω p) n (stageModel_components_compatible K Ω p o ho n)

/-- Original evaluation at every finite base stage recovers its actual restriction. -/
theorem actualKernelInverse_stage (n : ProjectionKernel (Spec.algebraMap K Ω) p o ho)
    (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K))) (q : Fiber (Spec.algebraMap K Ω) Z) :
    pointedMap (geometricStage (Spec.algebraMap K Ω) p o ho Z q)
      (actualKernelInverse K Ω p o ho n) = kernelStageAut (Spec.algebraMap K Ω) p o ho n Z q :=
  pointedMap_kernelAutFromStageModels (Spec.algebraMap K Ω) p o ho
    (exists_stageModel K Ω p) n (stageModel_components_compatible K Ω p o ho n) Z q

@[simp] theorem actualKernelInverse_kernelHom (a : BaseChangeGroup (Spec.algebraMap K Ω) p o ho) :
    actualKernelInverse K Ω p o ho (kernelHom (Spec.algebraMap K Ω) p o ho a) = a := by
  apply kernelHom_injective_of_stageModels (Spec.algebraMap K Ω) p o ho (exists_stageModel K Ω p)
  exact kernelHom_actualKernelInverse K Ω p o ho _

theorem kernelHom_bijective_actual : Function.Bijective (kernelHom (Spec.algebraMap K Ω) p o ho) :=
  ⟨kernelHom_injective_of_stageModels (Spec.algebraMap K Ω) p o ho (exists_stageModel K Ω p),
    fun n ↦ ⟨actualKernelInverse K Ω p o ho n, kernelHom_actualKernelInverse K Ω p o ho n⟩⟩

end AlgebraicExtension

section AlgebraicClosure
variable (F : Type u) [Field F] {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (CommRingCat.of F)) (o : Spec (CommRingCat.of F) ⟶ X)
  (h : o ≫ p = 𝟙 _)

/-- Bijectivity of the literal original geometric-to-arithmetic-kernel map. -/
theorem geometricKernelHom_bijective_actual : Function.Bijective (geometricKernelHom F p o h) :=
  kernelHom_bijective_actual F (AlgebraicClosure F) p o h

/-- The actual topological group isomorphism, with original forward homomorphism. -/
def actualGeometricKernelContinuousEquiv : GeometricGroup F p o h ≃ₜ* ArithmeticKernel F p o h :=
  kernelContinuousEquiv (algebraicClosurePoint F) p o h (geometricKernelHom_bijective_actual F p
    o h)

@[simp] theorem actualGeometricKernelContinuousEquiv_apply (a : GeometricGroup F p o h) :
    actualGeometricKernelContinuousEquiv F p o h a = geometricKernelHom F p o h a := rfl

@[simp] theorem actualGeometricKernelContinuousEquiv_symm (n : ArithmeticKernel F p o h) :
    (actualGeometricKernelContinuousEquiv F p o h).symm n =
      actualKernelInverse F (AlgebraicClosure F) p o h n := by
  apply geometricKernelHom_injective_actual F p o h
  exact (actualGeometricKernelContinuousEquiv F p o h).apply_symm_apply n |>.trans
    (kernelHom_actualKernelInverse F (AlgebraicClosure F) p o h n).symm

@[simp] theorem geometricHom_actualKernelInverse (n : ArithmeticKernel F p o h) :
    geometricHom F p o h (actualKernelInverse F (AlgebraicClosure F) p o h n) = n.val :=
  congrArg Subtype.val (kernelHom_actualKernelInverse F (AlgebraicClosure F) p o h n)

end AlgebraicClosure

/-- Realization of the original `Stacks0BTX F` interface, with all its original
quantifiers and the same literal geometric-kernel homomorphism. The connectedness
input is admitted by the interface but unnecessary for this kernel argument. -/
theorem stacks0BTX_actual (F : Type u) [Field F] : Stacks0BTX F := by
  constructor
  intro X p o h hqc hqs _
  let := hqc
  let := hqs
  exact geometricKernelHom_bijective_actual F p o h

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5d99e6175e2ef726c7b7945169eed5b4b774346bb061372cfead0ca5b1c04666.
Definitions, hypotheses and universes are retained modulo native names. -/
