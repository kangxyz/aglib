/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.AffineDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeIso

/-! # Original finite group degree in the selected native coordinates -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

variable {k : Type u} [Field k]

/-- The original finite-scheme degree is the dimension of the same coordinate Hopf algebra. -/
theorem finiteSchemeDegree_eq_finrank_coordinateHopf (G : Grp (FScheme k)) [IsFinite G.X.hom] :
    Hom.finiteSchemeDegree k G.X.hom = Module.finrank k (coordinateHopf G) := by
  let e : (specGroup (coordinateHopf G)).X.left ≅ G.X.left :=
    (Over.forget (Base k)).mapIso ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso G))
  have he : e.hom ≫ G.X.hom = (specGroup (coordinateHopf G)).X.hom :=
    Over.w (coordinateSpecIso G).hom.hom.hom
  calc
    Hom.finiteSchemeDegree k G.X.hom =
        Hom.finiteSchemeDegree k (specGroup (coordinateHopf G)).X.hom :=
      (Hom.finiteSchemeDegree_iso _ _ e he).symm
    _ = Module.finrank k (coordinateHopf G) := by
      rw [specGroup_hom]
      exact Hom.finiteSchemeDegree_spec k (coordinateHopf G)

end AlgebraicGeometry.Scheme.Group.CartierDuality
