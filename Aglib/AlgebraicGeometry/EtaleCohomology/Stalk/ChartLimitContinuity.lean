/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCohomologyDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitCohomologyCocone
/-! # Original strict-local limit cohomology is a genuine colimit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

section FixedCoefficient
universe uI vI
variable {I : Type uI} [Category.{vI} I] [IsConnected I]
  (Y : I ⥤ Scheme.{u}ᵒᵖ) (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (G : AbelianSheaf.{u, u + 1} b.pt.unop)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b G))]

/-- Transport an actual fixed-system cohomology colimit to the original pullback apex. -/
def fixedCoefficientColimit (n : ℕ)
    (h : IsColimit (diagramCohomologyCocone Y c (pullbackCoefficientSystem Y b G) n)) :
    IsColimit (pullbackLimitCohomologyCocone Y b c l hl G n) := by
  let E : AddCommGrpCat.of (Sheaf.H.{e}
      (colimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b G))) n) ≅
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage l.unop).obj G) n) :=
    pullbackLimitCohomologyIso.{u, e, uI, vI} Y b c l hl G n
  change IsColimit ((diagramCohomologyCocone Y c
    (pullbackCoefficientSystem Y b G) n).extend E.hom)
  exact @IsColimit.extendIso I _ AddCommGrpCat.{e} _
    (diagramCohomologyFunctor Y (pullbackCoefficientSystem Y b G) n)
    (diagramCohomologyCocone Y c (pullbackCoefficientSystem Y b G) n) _
    E.hom (inferInstance : IsIso E.hom) h
end FixedCoefficient

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)
  [QuasiCompact f] [QuasiSeparated f]
  [hExt : ∀ U : GeometricEtaleNeighborhood R Ω,
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance chartContinuityConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)
local instance chartContinuityStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  hExt U
local instance chartContinuityLimitExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))
local instance chartContinuityStageCompact (U : GeometricEtaleNeighborhood R Ω) :
    CompactSpace ((chartCoefficientDiagram R Ω j f).obj U).unop :=
  inferInstanceAs
    (CompactSpace ((chartGeometricBaseChangedDiagram R Ω j f).obj (op U)).left)
local instance chartContinuityStageQs (U : GeometricEtaleNeighborhood R Ω) :
    QuasiSeparatedSpace ((chartCoefficientDiagram R Ω j f).obj U).unop :=
  inferInstanceAs
    (QuasiSeparatedSpace ((chartGeometricBaseChangedDiagram R Ω j f).obj (op U)).left)
local instance chartContinuityMapAffine {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    IsAffineHom ((chartCoefficientDiagram R Ω j f).map a).unop :=
  inferInstanceAs (IsAffineHom ((chartGeometricBaseChangedDiagram R Ω j f).map a.op).left)

/-- Actual geometric continuity of the original fixed-coefficient cocone. -/
def chartLimitCohomologyCoconeIsColimit :
    IsColimit (chartLimitCohomologyCocone R Ω j f F q) :=
  fixedCoefficientColimit
     (chartCoefficientDiagram R Ω j f)
      (chartCoefficientBaseCone R Ω j f) (chartCoefficientLimitCocone R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
      (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
        (chartGeometricBaseChangedCone R Ω j f)
        ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) F q
    (isColimitDiagramCohomologyOfQcqsStages (chartCoefficientDiagram R Ω j f)
      (chartCoefficientLimitCocone R Ω j f) (chartCoefficientLimitIsColimit R Ω j f)
      (chartPullbackCoefficientSystem R Ω j f F) q)
end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
