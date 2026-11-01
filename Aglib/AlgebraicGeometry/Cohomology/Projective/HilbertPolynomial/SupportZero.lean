/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportDimension

/-!
# The zero-dimensional base case for Hilbert support induction

Every point of a space of dimension at most zero is a generic point of a
component. Thus a monomorphism between stalk-isomorphic coherent modules
supported in dimension at most zero has zero cokernel. The statement
includes the empty support and uses the original module stalks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace TopologicalSpace

/-- In dimension at most zero, each point is generic in an irreducible
component. No separation or nonemptiness hypothesis is needed. -/
theorem mem_genericPoints_of_topologicalKrullDim_nonpos
    {T : Type u} [TopologicalSpace T] (hT : topologicalKrullDim T ≤ 0) (x : T) :
    x ∈ genericPoints T := by
  let S : IrreducibleCloseds T :=
    ⟨closure ({x} : Set T), isIrreducible_singleton.closure, isClosed_closure⟩
  have hmax : IsMax S := (Order.krullDim_nonpos_iff_forall_isMax.mp hT) S
  change Maximal IsIrreducible (closure ({x} : Set T))
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Y hY hXY
  let Z : IrreducibleCloseds T := ⟨closure Y, hY.closure, isClosed_closure⟩
  have hSZ : S ≤ Z := hXY.trans subset_closure
  exact subset_closure.trans (hmax hSZ)

end TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A monomorphism between modules with isomorphic stalks, with coherent
source supported in dimension at most zero, has zero original cokernel. -/
theorem isZero_cokernel_of_supportDimension_nonpos
    {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (hM : affineLocallyFiniteType X M)
    (he : ∀ x : X, Nonempty ((moduleStalk X x).obj N ≅ (moduleStalk X x).obj M))
    (hd : topologicalKrullDim (support M) ≤ 0) : IsZero (cokernel f) := by
  apply (isZero_iff_stalks _).mpr
  intro x
  by_cases hx : x ∈ support M
  · have hg := mem_genericPoints_of_topologicalKrullDim_nonpos hd (⟨x, hx⟩ : support M)
    exact (Coherent.Support.moduleStalk_isZero_iff X (cokernel f) x).mp
      (isZero_stalk_cokernel_of_genericPoint_support f hM he ⟨x, hx⟩ hg)
  · have hc : x ∉ support (cokernel f) := fun h =>
      hx (support_cokernel_subset_of_stalkIso f he h)
    exact not_not.mp hc

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace

/-- A monomorphism into an original projective tensor twist has zero
cokernel when the coherent coefficient has support dimension at most zero. -/
theorem isZero_cokernel_mono_twist_of_supportDimension_nonpos
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    (M : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M) (a : ℤ)
    (f : M ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj M)
    [Mono f] (hd : topologicalKrullDim (support M) ≤ 0) : IsZero (cokernel f) :=
  isZero_cokernel_of_supportDimension_nonpos f hM
    (nonempty_twistingTensor_stalkIso k ι M a) hd

end AlgebraicGeometry.Scheme.Cohomology
