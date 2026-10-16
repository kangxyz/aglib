/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict

/-! # Inherited exactness of strict perfect complexes

The chosen conflations are exactly the short exact sequences in the ambient
category of module-sheaf complexes. The degree-zero inclusion preserves them.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/VectorBundleInclusion.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `1a315778b76b2796196f270c3d80f1e10310824bcaf37d1774354e7a74df4b57`.
Admitted subset: strictExactStructure, vectorBundleInclusion_additive and
  vectorBundleExactInclusion.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable (X : Scheme.{u})

/-- The actual inherited exact structure on strict perfect complexes. -/
abbrev strictExactStructure : CategoryTheory.ExactCategory.ExactStructure (StrictPerfect X) :=
  ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
    (strictPerfect X)

instance vectorBundleInclusion_additive : (vectorBundleInclusion X).Additive := by
  unfold vectorBundleInclusion
  infer_instance

/-- Placing vector bundles in degree zero preserves every ambient conflation,
including sequences which split only locally. -/
def vectorBundleExactInclusion :
    CategoryTheory.ExactCategory.ExactFunctor (vectorBundleExactStructure X) (strictExactStructure
      X) where
  toFunctor := vectorBundleInclusion X
  map_conflation S hS := by
    have hs : (S.map (finiteLocallyFree X).ι).ShortExact := hS
    let := hs.mono_f
    let := hs.epi_g
    exact hs.map (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)


end AlgebraicGeometry.Scheme.Modules.Complex
