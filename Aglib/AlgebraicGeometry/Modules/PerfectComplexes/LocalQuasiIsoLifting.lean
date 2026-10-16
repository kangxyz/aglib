/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalNullHomotopy
public import Aglib.Algebra.Homology.MappingCone.NullHomotopy
public import Aglib.Algebra.Homology.MappingCone.Acyclicity

/-!
# Local lifting through quasi-isomorphisms

A map from an actual strict perfect complex lifts through an arbitrary
quasi-isomorphism near each point, up to the original chain homotopy. The
proof uses the actual acyclic cone and local nullhomotopy, with no injective
replacement or global projectivity premise.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalQuasiIsoLifting.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `db71c57024ab73a5264ab112f4d0932f98e889dac4887d0b15f459cdf94137da`.
Selected declaration ranges: 57–74.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

theorem exists_local_quasiIso_lift {X : Scheme.{u}} {P K L : CochainComplex X.Modules ℤ}
    (hP : strictPerfect X P) (s : K ⟶ L) [QuasiIso s] (f : P ⟶ L) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj K,
        Nonempty (Homotopy ((@restrict Y X j hj).map f) (g ≫ (@restrict Y X j hj).map s)) := by
  obtain ⟨Y, j, hj, y, hy, ⟨h⟩⟩ := exists_local_nullHomotopy hP
    (f ≫ mappingCone.inr s) (CochainComplex.mappingCone_acyclic_of_quasiIso s) x
  let := hj
  let R := Scheme.Modules.restrictFunctor j
  let e := mappingCone.mapHomologicalComplexIso s R
  have he : (restrict j).map f ≫ mappingCone.inr ((restrict j).map s) =
      (restrict j).map (f ≫ mappingCone.inr s) ≫ e.hom := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun k ↦ (restrict j).map f ≫ k) (mappingCone.map_inr s R).symm
  let h' : Homotopy ((restrict j).map f ≫ mappingCone.inr ((restrict j).map s)) 0 :=
    (Homotopy.ofEq he).trans ((h.compRight e.hom).trans (Homotopy.ofEq (by simp)))
  obtain ⟨g, hg⟩ := exists_lift_of_cone_nullHomotopy ((restrict j).map s) ((restrict j).map f) h'
  exact ⟨Y, j, hj, y, hy, g, hg⟩

end AlgebraicGeometry.Scheme.Modules.Complex
