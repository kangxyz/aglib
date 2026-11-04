/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointPicardChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverSectionPullback

/-! The original degree-one Picard adjunct at a represented terminal point. -/

open CategoryTheory CategoryTheory.Limits Opposite
open GroupCohomology.Kummer.Coefficients

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

open DerivedCategory Scheme.RelativePicard Scheme.Modules.Invertible RepresentedKernel

universe u dX dS w s e

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- The original represented integer section gives its original terminal Picard
value on the degree-one adjunct of the specified original line-bundle class. -/
abbrev gmDerivedAdjunctH1OfRepresentedChartValue
    {G : Grp (Over S)} [IsCommMonObj G.X]
    (i : representedSheaf G ⟶ Kummer.normalizedPicardEtaleSheaf p o ho)
    (x : Over.mk (𝟙 S) ⟶ G.X) (c : Sheaf.H.{w} (gm X) 1)
    (L : PicardGroup X) (hL : (picardCohomologyEquiv X).symm c = L)
    (h : i.hom.app (op (etaleTerminal S)) (ULift.up (Additive.ofMul x)) =
      normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj (etaleTerminal S))
        (pullbackClass (pullback.fst p (𝟙 S)) L)) :=
  let A := representedSheaf G
  let E := (constantIntegerHomGlobalSectionsIso S).hom.app A
  let a := representedIntegerSection G x
  let e₀ : E a = ULift.up (Additive.ofMul x) := representedIntegerSection_one G x
  let N := normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj (etaleTerminal S))
  let e₁ := congrArg ((globalSections S).map i) e₀
  let e₂ := congrArg (fun b => N (pullbackClass (pullback.fst p (𝟙 S)) b)) hL
  gmDerivedAdjunct_h1_of_terminalValue p o ho c i a (e₁.trans (h.trans e₂.symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
