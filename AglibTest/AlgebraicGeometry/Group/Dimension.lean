/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension

/-! # General smooth group dimension, without properness or a curve premise -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : FScheme k) [GrpObj G]
    [Smooth G.hom] [PreconnectedSpace G.left] :
    topologicalKrullDim G.left = Module.finrank k (Cotangent.Space η[G]) :=
  Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected G

example {k : Type u} [Field k] [IsAlgClosed k] (G : FScheme k) [GrpObj G]
    [Smooth G.hom] : SmoothOfRelativeDimension (Module.finrank k (Cotangent.Space η[G])) G.hom :=
  Group.smoothOfRelativeDimension_finrank_identityCotangent_of_isAlgClosed G
