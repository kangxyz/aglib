/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModuleCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.AllCovers
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.RaisedComparison

/-! # Original module cohomology under Zariski--étale comparison

The source is the native Zariski additive sheaf of the original module. The
comparison uses the actual value-universe map and native restriction iso.
There are no separatedness, quasi-compactness or noetherianity assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge

local instance moduleComparisonEnoughSmall (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Sheaf.LargeCohomology.enoughInjectivesLarge _

local instance moduleComparisonEnoughRaised (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :=
  Sheaf.LargeCohomology.enoughInjectivesRaised.{u, u, u + 1} _

local instance moduleComparisonAbWRaised (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Sheaf.LargeCohomology.abWEqualsLocallyBijectiveRaised.{u, u, u + 1} _

local instance moduleComparisonTypeWRaised (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective (Type (u + 1)) :=
  Sheaf.LargeCohomology.typeWEqualsLocallyBijectiveRaised.{u, u, u + 1} _

variable (X : Scheme.{u})
  [HasExt.{e} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} X)]

/-- The original native Zariski module cohomology equals original étale cohomology. -/
def moduleCohomologyComparison (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Sheaf.H.{e} (Scheme.Cohomology.moduleAddSheaf X F) n ≃+
      Sheaf.H.{e'} (additiveCoefficient X F) n :=
  (valueLiftCohomologyAddEquiv.{e, u + 2, u, u, 0, u + 1}
    (CoverBasis.all (Opens.grothendieckTopology X)) isTerminalTop trivial
    (Scheme.Cohomology.moduleAddSheaf X F) n).trans
      ((((Sheaf.functorH (Opens.grothendieckTopology X) n).mapIso
        (zariskiModuleIso X F).symm).addCommGroupIsoToAddEquiv).trans
          (zariskiRestrictionCohomologyAddEquiv.{u, u + 2, e'} X F n))

/-- Naturality for any pair of additive coefficient arrows identified by the
actual restriction iso; the arrows need not be linear module morphisms. -/
theorem moduleCohomologyComparison_naturality_of_square
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : Scheme.Cohomology.moduleAddSheaf X F ⟶ Scheme.Cohomology.moduleAddSheaf X G)
    (g : additiveCoefficient X F ⟶ additiveCoefficient X G)
    (h : (zariskiRestriction X).map g ≫ (zariskiModuleIso X G).hom =
      (zariskiModuleIso X F).hom ≫
        (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).map f)
    (n : ℕ) (x : Sheaf.H.{e} (Scheme.Cohomology.moduleAddSheaf X F) n) :
    moduleCohomologyComparison X G n (Sheaf.H.map f n x) =
      Sheaf.H.map g n (moduleCohomologyComparison X F n x) := by
  have h' :
      (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).map f ≫
        (zariskiModuleIso X G).inv =
      (zariskiModuleIso X F).inv ≫ (zariskiRestriction X).map g := by
    apply (cancel_mono (zariskiModuleIso X G).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp
  change zariskiRestrictionCohomologyMap.{u, u + 2, e'} X (additiveCoefficient X G) n
    (Sheaf.H.map (zariskiModuleIso X G).inv n
      (valueLiftCohomologyMap.{e, u + 2, u, u, u, u + 1} isTerminalTop
        (Scheme.Cohomology.moduleAddSheaf X G) n (Sheaf.H.map f n x))) = _
  have hv := valueLiftCohomologyMap_naturality.{e, u + 2, u, u, u, u + 1}
    (isTerminalTop (α := X.Opens)) f n x
  rw [hv]
  have hh := congrArg (fun k => Sheaf.H.map k n
    (valueLiftCohomologyMap.{e, u + 2, u, u, u, u + 1}
      (isTerminalTop (α := X.Opens)) (Scheme.Cohomology.moduleAddSheaf X F) n x)) h'
  simp only [Sheaf.H.map_comp_apply] at hh
  rw [hh]
  exact zariskiRestrictionCohomologyMap_naturality X g n _

/-- In particular, the original comparison commutes with every native module map. -/
theorem moduleCohomologyComparison_naturality
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{e} (Scheme.Cohomology.moduleAddSheaf X F) n) :
    moduleCohomologyComparison X G n
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n x) =
    Sheaf.H.map (additiveCoefficientMap X g) n (moduleCohomologyComparison X F n x) :=
  moduleCohomologyComparison_naturality_of_square X
    ((SheafOfModules.toSheaf X.ringCatSheaf).map g) (additiveCoefficientMap X g)
    (zariskiModuleIso_naturality X g) n x

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
