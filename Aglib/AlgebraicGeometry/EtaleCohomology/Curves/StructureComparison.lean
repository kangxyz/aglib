/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.StructureComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.AllCovers
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.RaisedComparison

/-! # Original structure cohomology under Zariski--etale comparison

This combines the canonical comparison map with the actual structure-coefficient
isomorphisms and the proved change of value universe. The resulting map does not
change either original structure sheaf or identify distinct Ext universes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] HasExt.standard hasSheafifyLarge
  Scheme.Modules.isQuasicoherent_unit

local instance zariskiEnoughSmall (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Sheaf.LargeCohomology.enoughInjectivesLarge _

local instance zariskiEnoughRaised (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :=
  Sheaf.LargeCohomology.enoughInjectivesRaised.{u, u, u + 1} _

local instance zariskiAbWRaised (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Sheaf.LargeCohomology.abWEqualsLocallyBijectiveRaised.{u, u, u + 1} _

local instance zariskiTypeWRaised (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective (Type (u + 1)) :=
  Sheaf.LargeCohomology.typeWEqualsLocallyBijectiveRaised.{u, u, u + 1} _

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The literal comparison is bijective on the published additive structure coefficient. -/
theorem structureRestrictionComparison_bijective (q : ℕ) : Function.Bijective
    (zariskiRestrictionCohomologyMap.{u, u + 2, w} X (additiveStructureSheaf X) q) := by
  let e := additiveUnitStructureIso X
  let eR := ((Sheaf.functorH (Opens.grothendieckTopology X) q).mapIso
    ((zariskiRestriction X).mapIso e)).addCommGroupIsoToAddEquiv
  let eH := ((Sheaf.functorH (smallEtaleTopology X) q).mapIso e).addCommGroupIsoToAddEquiv
  apply (Function.Bijective.of_comp_iff _ eR.bijective).mp
  have heq :
      (zariskiRestrictionCohomologyMap.{u, u + 2, w} X (additiveStructureSheaf X) q) ∘ eR =
      eH ∘ (zariskiRestrictionCohomologyMap.{u, u + 2, w} X
        (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q) := by
    funext x
    exact zariskiRestrictionCohomologyMap_naturality X e.hom q x
  rw [heq]
  exact eH.bijective.comp (zariskiRestrictionCohomologyMap_bijective X
    (SheafOfModules.unit X.ringCatSheaf) q)

/-- The canonical original map, with its bijectivity proved by affine QC acyclicity. -/
def structureRestrictionComparison (q : ℕ) :
    Sheaf.H.{u + 2} ((zariskiRestriction X).obj (additiveStructureSheaf X)) q ≃+
      Sheaf.H.{w} (additiveStructureSheaf X) q :=
  AddEquiv.ofBijective (zariskiRestrictionCohomologyMap X (additiveStructureSheaf X) q)
    (structureRestrictionComparison_bijective X q)

/-- Original Zariski structure cohomology and original etale structure cohomology. -/
def structureCohomologyComparison (q : ℕ) :
    Sheaf.H.{u + 1} (Scheme.structureAddSheaf X) q ≃+
      Sheaf.H.{w} (additiveStructureSheaf X) q :=
  (valueLiftCohomologyAddEquiv.{u + 1, u + 2, u, u, 0, u + 1}
      (CoverBasis.all (Opens.grothendieckTopology X)) isTerminalTop trivial
      (Scheme.structureAddSheaf X) q).trans
    ((((Sheaf.functorH (Opens.grothendieckTopology X) q).mapIso
      (zariskiStructureIso X).symm).addCommGroupIsoToAddEquiv).trans
        (structureRestrictionComparison X q))


variable {k : Type u} [Field k] (Y : FScheme k)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)]

/-- The comparison respects the two original structural scalar morphisms. -/
theorem structureCohomologyComparison_scalar (q : ℕ) (a : k)
    (x : Scheme.structureCohomology k Y q) :
    structureCohomologyComparison Y.left q
      (Sheaf.H.map (Scheme.structureScalar Y a) q x) =
    Sheaf.H.map (structureScalar Y.left (Scheme.constants Y a)) q
      (structureCohomologyComparison Y.left q x) := by
  let L := valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y.left)
  let e := zariskiStructureIso Y.left
  have he : L.map (Scheme.structureScalar Y a) ≫ e.inv =
      e.inv ≫ (zariskiRestriction Y.left).map
        (structureScalar Y.left (Scheme.constants Y a)) := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [zariskiStructureIso_scalar]
    simp [L]
  change zariskiRestrictionCohomologyMap Y.left (additiveStructureSheaf Y.left) q
      (Sheaf.H.map e.inv q
        (valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1} isTerminalTop
          (Scheme.structureAddSheaf Y.left) q (Sheaf.H.map (Scheme.structureScalar Y a) q x))) = _
  have hv := valueLiftCohomologyMap_naturality.{u + 1, u + 2, u, u, u, u + 1}
    (isTerminalTop (α := Y.left.Opens)) (Scheme.structureScalar Y a) q x
  rw [hv]
  have heH := congrArg (fun f => Sheaf.H.map f q
    (valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1}
      (isTerminalTop (α := Y.left.Opens)) (Scheme.structureAddSheaf Y.left) q x)) he
  simp only [Sheaf.H.map_comp_apply, L] at heH
  rw [heH]
  exact zariskiRestrictionCohomologyMap_naturality Y.left
    (structureScalar Y.left (Scheme.constants Y a)) q _

attribute [local instance] structureCohomologyModule

/-- The comparison is linear for the installed original structural field actions. -/
def structureCohomologyLinearComparison (q : ℕ) :
    Scheme.structureCohomology k Y q ≃ₗ[k]
      Sheaf.H.{w} (additiveStructureSheaf Y.left) q where
  __ := structureCohomologyComparison Y.left q
  map_smul' a x := structureCohomologyComparison_scalar Y q a x

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
