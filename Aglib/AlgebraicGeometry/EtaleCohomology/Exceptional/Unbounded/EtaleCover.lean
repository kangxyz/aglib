/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedDirectImage
public import Aglib.Algebra.Homology.DerivedCategory.JointConservativity

/-! # Native unbounded étale inverse images jointly detect isomorphisms

Homology is used only to detect invertibility of an actual derived morphism.
There is no assertion of derived-forget faithfulness or equality detection,
and no properness, torsion, boundedness or cohomological-dimension hypothesis.
-/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
universe u v dS dU
variable (Λ : Type (u + 1)) [Ring Λ] {S : Scheme.{u}} {ι : Type v}
  (U : ι → S.Etale)
  (hU : ∀ s : S, ∃ (i : ι) (x : (U i).left), (U i).hom x = s)
  [hS : HasDerivedCategory.{dS} (ModuleSheaf S Λ)]
  [chartModels : ∀ i, HasDerivedCategory.{dU} (ModuleSheaf (U i).left Λ)]

/-- Keep the original base model at the literal over-category codomain of each chart. -/
local instance unboundedEtaleCoverBaseModel (i : ι) :
    HasDerivedCategory.{dS} (ModuleSheaf ((Functor.fromPUnit S).obj (U i).right) Λ) := hS

/-- Keep each independently supplied chart model at the literal domain projection. -/
local instance unboundedEtaleCoverChartModel (i : ι) :
    HasDerivedCategory.{dU} (ModuleSheaf ((𝟭 Scheme.{u}).obj (U i).left) Λ) := chartModels i

include hU in
/-- Joint conservativity on the original unbounded module derived categories,
with independent native source and chart models. -/
theorem isIso_of_moduleUnboundedDerived_etale_inverseImages
    {K L : DerivedCategory (ModuleSheaf S Λ)} (a : K ⟶ L)
    (ha : ∀ i, IsIso ((moduleUnboundedDerivedInverseImage Λ (U i).hom).map a)) :
    IsIso a := by
  exact Functor.isIso_of_mapDerivedCategory_family
    (fun i => moduleInverseImage (U i).hom Λ)
    (fun a ha => isIso_of_module_etale_inverseImages Λ U hU a ha) a ha

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
