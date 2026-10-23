/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChange
public import Aglib.AlgebraicGeometry.Stalk.DiscretePullbackSections

/-!
# Original generic direct-image unit coordinates

On a quasi-compact etale test the actual generic base change is Artinian.
Its global units are tuples in the original test's stalk rings, and the
original Gm direct-image unit is the tuple of original germs. No replacement
by reduced generic fields or by a Zariski direct image occurs here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- Actual units on the whole generic pullback in the original test's stalk rings. -/
def genericBaseChangeUnitCoordinates :
    Γ(pullback U.hom (genericArtinMap X), ⊤)ˣ ≃*
      ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
        (U.left.presheaf.stalk ((pullback.fst U.hom (genericArtinMap X)) p))ˣ := by
  let : IsArtinianScheme (pullback U.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  let : ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      IsIso ((pullback.fst U.hom (genericArtinMap X)).stalkMap p) :=
    genericArtinBaseChange_stalkMap_isIso U.hom
  exact Scheme.globalUnitsTargetStalkProduct (pullback.fst U.hom (genericArtinMap X))

/-- The actual scheme pullback is the original tuple of unit germs. -/
theorem genericBaseChangeUnitCoordinates_pullback (a : Γ(U.left, ⊤)ˣ)
    (p : (pullback U.hom (genericArtinMap X) : Scheme.{u})) :
    genericBaseChangeUnitCoordinates U
      (Units.map (pullback.fst U.hom (genericArtinMap X)).appTop.hom.toMonoidHom a) p =
      Units.map (U.left.presheaf.germ ⊤
        ((pullback.fst U.hom (genericArtinMap X)) p) trivial).hom.toMonoidHom a := by
  let : IsArtinianScheme (pullback U.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  let : ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      IsIso ((pullback.fst U.hom (genericArtinMap X)).stalkMap p) :=
    genericArtinBaseChange_stalkMap_isIso U.hom
  exact Scheme.globalUnitsTargetStalkProduct_appTop
    (pullback.fst U.hom (genericArtinMap X)) a p

/-- Coordinates of a section of the original small-etale direct image of Gm. -/
def genericDirectImageUnitCoordinates
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U)) :
    ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      (U.left.presheaf.stalk ((pullback.fst U.hom (genericArtinMap X)) p))ˣ :=
  genericBaseChangeUnitCoordinates U
    (unitsSections (genericArtinLocus X) ((siteBaseChange (genericArtinMap X)).op.obj (op U))
      a).toMul

/-- The original Gm unit has exactly its original unit-germ coordinates. -/
theorem genericDirectImageUnitCoordinates_unit (a : (gm X).obj.obj (op U))
    (p : (pullback U.hom (genericArtinMap X) : Scheme.{u})) :
    genericDirectImageUnitCoordinates U ((genericArtinUnit X).hom.app (op U) a) p =
      Units.map (U.left.presheaf.germ ⊤
        ((pullback.fst U.hom (genericArtinMap X)) p) trivial).hom.toMonoidHom
          (unitsSections X (op U) a).toMul := by
  have h := gmUnit_sections (genericArtinMap X) (op U) a
  have h' := congrArg (fun b => genericBaseChangeUnitCoordinates U b p) h
  exact h'.trans (genericBaseChangeUnitCoordinates_pullback U _ p)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
