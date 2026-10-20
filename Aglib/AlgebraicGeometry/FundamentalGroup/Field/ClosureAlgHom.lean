/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Embedding

/-!
# The chosen closure embedding as an algebra map

Source: `R5Lab.Aglib.FieldTheory.AbsoluteGaloisGroup.NativeLift`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange
universe u
variable {F K : Type u} [Field F] [Field K] [Algebra F K]
/-- The algebra-homomorphism view of the existing chosen closure embedding. -/
def closureAlgHom : AlgebraicClosure F →ₐ[F] AlgebraicClosure K where
  __ := _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange.closureEmbedding
    (algebraMap F K)
  commutes' x := DFunLike.congr_fun
    (_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange.closureEmbedding_comp
    (algebraMap F K)) x

end AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange
