/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChange
public import Aglib.AlgebraicGeometry.Stalk.DiscreteSectionsNaturality

/-!
# Actual etale restriction of generic direct-image unit coordinates

The comparison here retains the original direct-image presheaf map and the
original morphism on the geometric base changes. Its coordinates are actual
stalk units on those nonreduced Artinian schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Original generic direct-image sections in the actual pullback's stalk-unit coordinates. -/
def genericDirectImageSourceCoordinates (U : X.Etale) [QuasiCompact U.hom]
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U)) :
    ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      ((pullback U.hom (genericArtinMap X)).presheaf.stalk p)ˣ := by
  let : IsArtinianScheme (pullback U.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  exact Scheme.globalUnitsStalkProduct (pullback U.hom (genericArtinMap X))
    (unitsSections (genericArtinLocus X) ((siteBaseChange (genericArtinMap X)).op.obj (op U))
      a).toMul

/-- The literal direct-image restriction acts by the actual base-change stalk maps. -/
theorem genericDirectImageSourceCoordinates_restrict {U V : X.Etale}
    [QuasiCompact U.hom] [QuasiCompact V.hom] (f : V ⟶ U)
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U))
    (q : (pullback V.hom (genericArtinMap X) : Scheme.{u})) :
    genericDirectImageSourceCoordinates V
      (((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.map f.op a) q =
      Units.map (((siteBaseChange (genericArtinMap X)).map f).left.stalkMap q).hom.toMonoidHom
        (genericDirectImageSourceCoordinates U a
          (((siteBaseChange (genericArtinMap X)).map f).left q)) := by
  let : IsArtinianScheme (pullback U.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  let : IsArtinianScheme (pullback V.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := V.left) V.hom
  have h := unitsSections_naturality (genericArtinLocus X)
    (((siteBaseChange (genericArtinMap X)).map f).op) a
  have h' := congrArg (fun b =>
    Scheme.globalUnitsStalkProduct (pullback V.hom (genericArtinMap X)) b q) h
  exact h'.trans (Scheme.globalUnitsStalkProduct_naturality
    (P := pullback U.hom (genericArtinMap X))
    (Q := pullback V.hom (genericArtinMap X))
    ((siteBaseChange (genericArtinMap X)).map f).left _ q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
