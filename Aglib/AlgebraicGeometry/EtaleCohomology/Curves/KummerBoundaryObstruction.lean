/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.FieldExtensionBoundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FieldExtensionRoots

/-! # Lifting the actual rational boundary obstruction

A target boundary divisor with n-divisible original Picard class descends to
the actual rational boundary divisor. Proper roots-H2 injectivity reflects its
Picard divisibility, and the original divisor/Picard kernel constructs a
rational function whose divisor differs from that boundary by n times a
native divisor. No affine-unit power-surjectivity or cohomological residue
exactness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  (X : FScheme k) [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
  [SmoothOfRelativeDimension 1 X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
  [IsIntegral (pullback X.hom (Spec.algebraMap k K))]
  [IsNoetherian (pullback X.hom (Spec.algebraMap k K))]
  [∀ y : ClosedPoint (pullback X.hom (Spec.algebraMap k K)),
    IsDiscreteValuationRing
      ((pullback X.hom (Spec.algebraMap k K)).presheaf.stalk y.val)]
  (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1)
  (hdim' : topologicalKrullDim
    (show Scheme from pullback X.hom (Spec.algebraMap k K)) ≤ 1)
  (n : ℕ) (hn : 0 < n) (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))

include hN hdim hn hk in
/-- Proper roots-H2 injectivity constructs a rational function matching the
actual target boundary divisor modulo n, with the literal principal-divisor
sign retained. Target algebraic closure is not needed for this obstruction
step; it is only needed later for proper H1 surjectivity. -/
theorem exists_principal_congruent_boundary (V : X.left.Opens) [Nonempty V]
    (B : Divisor (pullback X.hom (Spec.algebraMap k K)))
    (hB : ∀ y ∈ B.support, y.val ∉ (pullback.fst X.hom (Spec.algebraMap k K)) ⁻¹ᵁ V)
    (hdiv : ∃ c : PicardGroup (pullback X.hom (Spec.algebraMap k K)),
      n • c = DivisorClass.divisorToPicard _ hdim' B) :
    ∃ (f : X.left.functionFieldˣ) (D : Divisor X.left),
      principal X.left (Additive.ofMul f) =
        fieldRestriction X.hom (Spec.algebraMap k K) B - n • D := by
  let B₀ := fieldRestriction X.hom (Spec.algebraMap k K) B
  have hrecover := fieldExtension_fieldRestriction_of_boundary
    X.hom (Spec.algebraMap k K) hdim.le V B hB
  have hclass := pullbackClass_divisor_fieldExtension
    X.hom (Spec.algebraMap k K) hdim.le hdim' B₀
  have hclass' : pullbackClass (pullback.fst X.hom (Spec.algebraMap k K))
      (DivisorClass.divisorToPicard X.left hdim.le B₀) =
      DivisorClass.divisorToPicard _ hdim' B :=
    hclass.trans (congrArg (DivisorClass.divisorToPicard _ hdim') hrecover)
  obtain ⟨c, hc⟩ := (normalProperCurve_fieldExtension_nsmul_preimage_iff
    k K X hN hdim n hn hk (DivisorClass.divisorToPicard X.left hdim.le B₀)).mpr
      (by simpa only [hclass'] using hdiv)
  obtain ⟨D, hD⟩ := DivisorClass.divisorToPicard_surjective X.left hdim.le c
  have hp : B₀ - n • D ∈ (principal X.left).range := by
    rw [← DivisorClass.divisorToPicard_ker X.left hdim.le]
    change DivisorClass.divisorToPicard X.left hdim.le (B₀ - n • D) = 0
    rw [map_sub, map_nsmul, hD, hc, sub_self]
  obtain ⟨f, hf⟩ := hp
  exact ⟨f.toMul, D, hf⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
