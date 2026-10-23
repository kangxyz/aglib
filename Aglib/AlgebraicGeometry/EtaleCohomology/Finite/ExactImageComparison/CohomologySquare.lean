/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.SquareTransport
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.SquareComparison

/-! # The original cohomology comparison commutes with base change

The vertical maps in this square are the original cohomology pullbacks. The
statement is a commuting square, not an invertibility assertion for these maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

section Congruence

variable {X S : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]

/-- Equality transport of a scheme map retains its original cohomology pullback. -/
theorem cohomologyPullback_eqToHom {k l : X ⟶ S} (h : k = l)
    (F : AbelianSheaf.{u, u + 1} S) (q : ℕ) (a : Sheaf.H.{wS} F q) :
    Sheaf.H.map ((eqToHom (congrArg (fun t : X ⟶ S => inverseImage t) h)).app F) q
        (cohomologyPullback k F q a) = cohomologyPullback l F q a := by
  subst l
  simp only [eqToHom_refl, NatTrans.id_app, Sheaf.H.map_id_apply]

end Congruence

variable {X S X' S' : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original inverse-image square transports the two composite cohomology pullbacks. -/
theorem cohomologyPullback_square (F : AbelianSheaf.{u, u + 1} S) (q : ℕ)
    (a : Sheaf.H.{wS} F q) :
    Sheaf.H.map ((inverseImageSquareIso f f' g g' h).hom.app F) q
        (cohomologyPullback f' ((inverseImage g).obj F) q (cohomologyPullback g F q a)) =
      cohomologyPullback g' ((inverseImage f).obj F) q (cohomologyPullback f F q a) := by
  apply functor_map_square_element (Sheaf.functorH (Scheme.smallEtaleTopology X') q)
    ((inverseImageComp g f').hom.app F)
    ((eqToHom (congrArg (fun t : X' ⟶ S => inverseImage t) h)).app F)
    ((inverseImageComp f g').hom.app F)
    ((inverseImageSquareIso f f' g g' h).hom.app F)
    (a := cohomologyPullback (f' ≫ g) F q a)
    (c := cohomologyPullback (g' ≫ f) F q a)
  · exact congr_app (inverseImageSquareIso_comp_hom f f' g g' h) F
  · exact cohomologyPullback_comp g f' F q a
  · exact cohomologyPullback_eqToHom h F q a
  · exact cohomologyPullback_comp f g' F q a

end AlgebraicGeometry.Scheme.EtaleCohomology
