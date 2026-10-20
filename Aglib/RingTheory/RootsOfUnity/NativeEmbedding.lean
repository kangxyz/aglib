/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootCoordinates
public import Aglib.RingTheory.RootsOfUnity.Coordinates

/-!
# The native linear map on actual roots

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.NativeEmbedding`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic
open Field.absoluteGaloisGroup.RootsOfUnity
namespace Field.absoluteGaloisGroup.RootsOfUnity.NativeEmbedding
universe u
variable {F K : Type u} [Field F] [Field K] [CharZero F] [CharZero K]
variable (i : F →+* K) (n : ℕ) [NeZero n]
/-- Literal root embedding for the already existing native coefficient module. -/
abbrev nativeRootEmbedding : Mu F n ≃ₗ[ℤ] Mu K n :=
  (Cyclotomic.RootCoordinates.rootEmbeddingLinear i n).restrictScalars ℤ


theorem nativeRootEmbedding_primitive :
    nativeRootEmbedding i n (Coordinates.generator F n) =
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootRatio i n :
        ZMod n).val • Coordinates.generator K n := by
  ext
  change FieldEmbeddingBaseChange.closureEmbedding i
    (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot F n) =
    _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot K n ^
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootRatio i n :
      ZMod n).val
  exact (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootRatio_spec i
    n).symm


/-- Native root transport commutes with the independently proved actual restriction. -/
theorem nativeRootEmbedding_smul (g : Field.absoluteGaloisGroup K) (x : Mu F n) :
    nativeRootEmbedding i n
      (FieldEmbeddingBaseChange.absoluteRestriction
      i g • x) =
      g • nativeRootEmbedding i n x := by
  ext
  exact
    FieldEmbeddingBaseChange.absoluteRestriction_commutes
    i g
    ((x.toMul : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)

end Field.absoluteGaloisGroup.RootsOfUnity.NativeEmbedding
