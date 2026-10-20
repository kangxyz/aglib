/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne

/-!
# The codimension-one local-to-generic triangle

This is the actual stalk-specialization triangle of the original integral scheme,
extracted from the R5 source with the same basename at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.CodimensionOnePoint

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- The original local-to-generic map is compatible with both stalk spectra. -/
theorem generic_triangle (x : CodimensionOnePoint X) :
    Spec.map (CommRingCat.ofHom (algebraMap x.localRing X.functionField)) ≫
      X.fromSpecStalk x.1 = X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)

end AlgebraicGeometry.Scheme.CodimensionOnePoint
