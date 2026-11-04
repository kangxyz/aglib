/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange

/-! The original Kummer roots pullback of a represented character. -/

open CategoryTheory
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.Group

universe u wX wY

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)] [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)]

/-- The original roots pullback is the represented pullback followed by the original roots
coefficient isomorphism. -/
theorem rootsH1Pullback_eq_represented (a : Sheaf.H.{wX} (mu X n) 1) :
    letI : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
      RootsFiniteEtale.rootsScheme_etale X n hn hi
    rootsCohomologyPullback.{u, wX, wY} f n hn hi 1 a =
      coefficientMap (representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom)
        (representedH1Pullback.{u, wX, wY} f (MultiplicativeGroup.rootsGroupScheme X n) a) := by
  let G := MultiplicativeGroup.rootsGroupScheme X n
  let : Etale G.X.hom := RootsFiniteEtale.rootsScheme_etale X n hn hi
  let e := representedSheafBaseChangeIso f G
  let r := representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
  have he : (rootsPullbackIso f n hn hi).hom = e.hom ≫ r := rfl
  change Sheaf.H.map (rootsPullbackIso f n hn hi).hom 1 (h1Pullback f (mu X n) a) =
    Sheaf.H.map r 1 (Sheaf.H.map e.hom 1 (h1Pullback f (mu X n) a))
  let v : Sheaf.H.{wY} ((inverseImage f).obj (representedSheaf G)) 1 :=
    h1Pullback f (mu X n) a
  have h₁ := congrArg (fun q => Sheaf.H.map q 1 v) he
  have h₂ := Sheaf.H.map_comp_apply e.hom r v
  exact h₁.trans h₂

/-- The original roots pullback commutes with an original represented character. -/
theorem rootsH1Pullback_representedCharacter
    {G : Grp (Over X)} [IsCommMonObj G.X] [Etale G.X.hom]
    (χ : G ⟶ MultiplicativeGroup.rootsGroupScheme X n)
    (a : Sheaf.H.{wX} (representedSheaf G) 1) :
    rootsCohomologyPullback.{u, wX, wY} f n hn hi 1
        (coefficientMap (representedSheafMap χ) a) =
      coefficientMap
        (representedSheafMap ((Over.pullback f).mapGrp.map χ ≫
          (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom))
        (representedH1Pullback.{u, wX, wY} f G a) := by
  let : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n hn hi
  let a' : Sheaf.H.{wX} (mu X n) 1 := coefficientMap (representedSheafMap χ) a
  let z := representedH1Pullback.{u, wX, wY} f G a
  let r := (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
  let c := (Over.pullback f).mapGrp.map χ
  let h := rootsH1Pullback_eq_represented f n hn hi a'
  let h' := representedH1Pullback_coefficientMap f χ a
  change rootsCohomologyPullback f n hn hi 1 a' = coefficientMap (representedSheafMap (c ≫ r)) z
  refine h.trans ((congrArg (coefficientMap (representedSheafMap r)) h').trans ?_)
  change Sheaf.H.map (representedSheafMap r) 1 (Sheaf.H.map (representedSheafMap c) 1 z) =
    Sheaf.H.map (representedSheafMap (c ≫ r)) 1 z
  exact (Sheaf.H.map_comp_apply (representedSheafMap c)
    (representedSheafMap r) z).symm.trans
    (congrArg (fun q => Sheaf.H.map q 1 z) (representedSheafMap_comp c r).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
