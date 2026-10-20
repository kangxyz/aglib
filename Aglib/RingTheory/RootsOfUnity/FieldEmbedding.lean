/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootCoordinates
public import Aglib.RingTheory.RootsOfUnity.Galois

/-!
# Root transport under a field embedding

The additive form of the existing actual root embedding uses the same chosen
compatible embedding of algebraic closures. Its equivariance is the literal
absolute-Galois restriction identity. Both fields retain characteristic zero,
and the level remains positive. Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.FieldEmbedding`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The common carrier and action are reused
as `Mu` and `rootAction` from the common root coefficient owner.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.FieldEmbedding

open AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {F K : Type u} [Field F] [Field K] (i : F →+* K)
variable [CharZero F] [CharZero K] (n : ℕ) [NeZero n]

/-- The additive form of the native map on actual roots of unity. -/
abbrev rootEmbeddingEquiv : Mu F n ≃+ Mu K n :=
  (Cyclotomic.RootCoordinates.rootEmbedding i n).toAdditive

omit [CharZero K] in
@[simp] theorem rootEmbeddingEquiv_value (z : Mu F n) :
    (((rootEmbeddingEquiv i n z).toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      FieldEmbeddingBaseChange.closureEmbedding i
        ((z.toMul : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) := rfl

/-- Root transport intertwines the two actual absolute-Galois actions. -/
theorem rootEmbeddingEquiv_galois (g : Field.absoluteGaloisGroup K) (z : Mu F n) :
    rootEmbeddingEquiv i n
        (rootAction F n (FieldEmbeddingBaseChange.absoluteRestriction i g) z) =
      rootAction K n g (rootEmbeddingEquiv i n z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact FieldEmbeddingBaseChange.absoluteRestriction_commutes i g _

end Field.absoluteGaloisGroup.RootsOfUnity.FieldEmbedding
