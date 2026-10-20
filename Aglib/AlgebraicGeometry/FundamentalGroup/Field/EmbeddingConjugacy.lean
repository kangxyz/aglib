/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ClosureEmbedding

/-!
# Actual point-extension conjugacy for compatible closure embeddings

Both incoming copies are one equation for the same field algebra and
the same two displayed compatible closure embeddings. Their actual point
maps use the lower closure-embedding implementation, without a Kummer or
characteristic-zero dependency.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.EmbeddingConjugacy`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d2a6d3b84509f636cc8472c1315e8204d00987d3a906e9d88a432732c11bc516`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open Field.absoluteGaloisGroup.RootsOfUnity

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.ClosureEmbedding

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable (i j : FieldPullbackIndependence.Embedding (K := F) (L := K))
theorem pointExtension_conjugator :
    pointExtension j = pointExtension i ≫
      pointEnd F (FieldPullbackIndependence.conjugator i j) := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (FieldPullbackIndependence.conjugator_commutes i j x).symm

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.ClosureEmbedding
