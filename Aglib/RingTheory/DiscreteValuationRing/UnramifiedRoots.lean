/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Adjoin
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# An actual unramified extension adjoining prime-to-residue-characteristic roots

The construction starts with the literal finite subalgebra `R[ζ]` inside an
algebraic closure of the fraction field. The relation `ζⁿ = 1` and invertibility
of `n` make this subalgebra formally unramified: it is a quotient of the actual
standard étale algebra for `Xⁿ - 1` with inverted derivative. Its localization
at a prime above the maximal ideal is the desired unramified discrete valuation
ring. No completeness or perfectness of the residue field is required.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/UnramifiedRoots.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f67d314bb6ff7cc64cee57b192d1cf80dc2a003ac246563d464335702b9572df`.
-/

@[expose] public section

open _root_.Algebra.RootsOfUnity
  (RootAlgebra root rootAlgebra_finite rootAlgebra_formallyUnramified)

noncomputable section

namespace Algebra.RootsOfUnity.UnramifiedExtension

open Polynomial IsLocalRing

universe u v

section DVRConstruction

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (n : ℕ) (hnR : IsUnit (n : R))

include hnR

/-- An invertible root level is positive, including in mixed characteristic. -/
theorem level_ne_zero : n ≠ 0 := by
  intro h
  simpa [h] using hnR.ne_zero

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Its image in the fraction field is nonzero. -/
theorem level_cast_ne_zero : (n : K) ≠ 0 := by
  simpa using (hnR.map (algebraMap R K)).ne_zero

/-- An actual primitive root in the algebraic closure of the fraction field. -/
def primitiveRoot : AlgebraicClosure K :=
  letI : NeZero (n : K) := ⟨level_cast_ne_zero R K n hnR⟩
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n).choose

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem primitiveRoot_spec : IsPrimitiveRoot (primitiveRoot R K n hnR) n := by
  let : NeZero (n : K) := ⟨level_cast_ne_zero R K n hnR⟩
  exact (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n).choose_spec

/-- The explicit finite domain obtained by adjoining this primitive root. -/
abbrev FiniteRootRing := RootAlgebra R (primitiveRoot R K n hnR)

instance finiteRootRing_finite : Module.Finite R (FiniteRootRing R K n hnR) :=
  rootAlgebra_finite R (level_ne_zero R n hnR) (primitiveRoot_spec R K n hnR).pow_eq_one

instance finiteRootRing_formallyUnramified :
    Algebra.FormallyUnramified R (FiniteRootRing R K n hnR) :=
  rootAlgebra_formallyUnramified R (level_ne_zero R n hnR) hnR
    (primitiveRoot_spec R K n hnR).pow_eq_one

instance finiteRootRing_faithful : FaithfulSMul R (FiniteRootRing R K n hnR) := by
  apply (faithfulSMul_iff_algebraMap_injective R (FiniteRootRing R K n hnR)).mpr
  have h : Function.Injective (algebraMap R (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq R K (AlgebraicClosure K)]
    exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective R K)
  intro x y hxy
  exact h (congrArg Subtype.val hxy)

/-- Finite unramified domain extensions of Dedekind domains are Dedekind,
so the explicit root subalgebra has all the required one-dimensional structure. -/
instance finiteRootRing_dedekind : IsDedekindDomain (FiniteRootRing R K n hnR) :=
  IsDedekindDomain.of_formallyUnramified R (FiniteRootRing R K n hnR)

/-- Choose an actual maximal ideal of the finite root algebra above the original
maximal ideal, using the integral lying-over theorem. -/
def primeOver : Ideal (FiniteRootRing R K n hnR) :=
  (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := FiniteRootRing R K n hnR) (maximalIdeal R)).choose

theorem primeOver_spec : (primeOver R K n hnR).IsMaximal ∧
    (primeOver R K n hnR).LiesOver (maximalIdeal R) :=
  (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := FiniteRootRing R K n hnR) (maximalIdeal R)).choose_spec

instance primeOver_isMaximal : (primeOver R K n hnR).IsMaximal :=
  (primeOver_spec R K n hnR).1

instance primeOver_liesOver : (primeOver R K n hnR).LiesOver (maximalIdeal R) :=
  (primeOver_spec R K n hnR).2

theorem primeOver_ne_bot : primeOver R K n hnR ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) _

/-- The actual local ring for the required unramified extension. -/
abbrev ExtensionRing := Localization.AtPrime (primeOver R K n hnR)

instance extensionRing_dvr : IsDiscreteValuationRing (ExtensionRing R K n hnR) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (FiniteRootRing R K n hnR) (primeOver_ne_bot R K n hnR) (ExtensionRing R K n hnR)

/-- The base ring embeds in the constructed local root ring. -/
instance extensionRing_faithful : FaithfulSMul R (ExtensionRing R K n hnR) := by
  apply (faithfulSMul_iff_algebraMap_injective R (ExtensionRing R K n hnR)).mpr
  rw [IsScalarTower.algebraMap_eq R (FiniteRootRing R K n hnR) (ExtensionRing R K n hnR)]
  exact (IsLocalization.injective (ExtensionRing R K n hnR)
    (primeOver R K n hnR).primeCompl_le_nonZeroDivisors).comp
      (FaithfulSMul.algebraMap_injective R (FiniteRootRing R K n hnR))

/-- The original local ring maps locally to the selected localization above its
maximal ideal. -/
instance extensionRing_isLocalHom : IsLocalHom (algebraMap R (ExtensionRing R K n hnR)) := by
  apply ((local_hom_TFAE (algebraMap R (ExtensionRing R K n hnR))).out 1 5).mpr
  rw [IsScalarTower.algebraMap_eq R (FiniteRootRing R K n hnR) (ExtensionRing R K n hnR),
    ← Ideal.comap_comap]
  change ((maximalIdeal (ExtensionRing R K n hnR)).under (FiniteRootRing R K n hnR)).under R = _
  rw [IsLocalization.AtPrime.under_maximalIdeal (ExtensionRing R K n hnR) (primeOver R K n hnR)]
  exact Ideal.LiesOver.over.symm

/-- The constructed local ring remains formally unramified. -/
theorem extensionRing_formallyUnramified :
    Algebra.FormallyUnramified R (ExtensionRing R K n hnR) := inferInstance

/-- The maximal ideal is obtained by extension of the original maximal ideal.
This is the concrete ramification-index-one statement. -/
theorem map_maximalIdeal :
    (maximalIdeal R).map (algebraMap R (ExtensionRing R K n hnR)) =
      maximalIdeal (ExtensionRing R K n hnR) :=
  Algebra.FormallyUnramified.map_maximalIdeal

/-- Every original uniformizer stays irreducible in the actual extension DVR. -/
theorem irreducible_map {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (ExtensionRing R K n hnR) π) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [← map_maximalIdeal R K n hnR, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- The actual map of residue fields induced by the local ring embedding. -/
def residueEmbedding : ResidueField R →+* ResidueField (ExtensionRing R K n hnR) :=
  ResidueField.map (algebraMap R (ExtensionRing R K n hnR))

theorem residueEmbedding_injective : Function.Injective (residueEmbedding R K n hnR) :=
  (residueEmbedding R K n hnR).injective

/-- The chosen primitive root considered as an element of the finite algebra. -/
def primitiveRootInFiniteRing : FiniteRootRing R K n hnR := root R (primitiveRoot R K n hnR)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem primitiveRootInFiniteRing_spec : IsPrimitiveRoot (primitiveRootInFiniteRing R K n hnR) n :=
  (primitiveRoot_spec R K n hnR).of_map_of_injective
    (f := (FiniteRootRing R K n hnR).val) Subtype.val_injective

/-- The chosen primitive root inside the constructed unramified DVR itself. -/
def primitiveRootInRing : ExtensionRing R K n hnR :=
  algebraMap (FiniteRootRing R K n hnR) (ExtensionRing R K n hnR)
    (primitiveRootInFiniteRing R K n hnR)

theorem primitiveRootInRing_spec : IsPrimitiveRoot (primitiveRootInRing R K n hnR) n :=
  (primitiveRootInFiniteRing_spec R K n hnR).map_of_injective
    (IsLocalization.injective (ExtensionRing R K n hnR)
      (primeOver R K n hnR).primeCompl_le_nonZeroDivisors)

/-- The actual fraction field of the constructed unramified DVR. -/
abbrev ExtensionField := FractionRing (ExtensionRing R K n hnR)

/-- The induced field embedding from the original fraction field. -/
def fractionEmbedding : K →+* ExtensionField R K n hnR :=
  IsFractionRing.lift (K := K) (g := algebraMap R (ExtensionField R K n hnR)) (by
    rw [IsScalarTower.algebraMap_eq R (ExtensionRing R K n hnR) (ExtensionField R K n hnR)]
    exact (IsFractionRing.injective (ExtensionRing R K n hnR) (ExtensionField R K n hnR)).comp
      (FaithfulSMul.algebraMap_injective R (ExtensionRing R K n hnR)))

@[simp] theorem fractionEmbedding_algebraMap (r : R) :
    fractionEmbedding R K n hnR (algebraMap R K r) =
      algebraMap R (ExtensionField R K n hnR) r :=
  IsFractionRing.lift_algebraMap _ r

instance extensionField_algebra : Algebra K (ExtensionField R K n hnR) :=
  (fractionEmbedding R K n hnR).toAlgebra

instance extensionField_scalarTower : IsScalarTower R K (ExtensionField R K n hnR) :=
  IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun r => (fractionEmbedding_algebraMap R K n hnR r).symm)

/-- The primitive root in the actual extension fraction field. -/
def primitiveRootInField : ExtensionField R K n hnR :=
  algebraMap (ExtensionRing R K n hnR) (ExtensionField R K n hnR)
    (primitiveRootInRing R K n hnR)

theorem primitiveRootInField_spec : IsPrimitiveRoot (primitiveRootInField R K n hnR) n :=
  (primitiveRootInRing_spec R K n hnR).map_of_injective
    (IsFractionRing.injective (ExtensionRing R K n hnR) (ExtensionField R K n hnR))

/-- The actual extension field contains all nth roots, with a primitive root
provided by the construction above. -/
instance extensionField_hasEnoughRoots : HasEnoughRootsOfUnity (ExtensionField R K n hnR) n where
  prim := ⟨primitiveRootInField R K n hnR, primitiveRootInField_spec R K n hnR⟩
  cyc := by
    let : NeZero n := ⟨level_ne_zero R n hnR⟩
    exact rootsOfUnity.isCyclic (ExtensionField R K n hnR) n

/-- The level stays invertible in the constructed DVR. -/
theorem extensionRing_level_isUnit : IsUnit (n : ExtensionRing R K n hnR) := by
  simpa using hnR.map (algebraMap R (ExtensionRing R K n hnR))

end DVRConstruction

end Algebra.RootsOfUnity.UnramifiedExtension
