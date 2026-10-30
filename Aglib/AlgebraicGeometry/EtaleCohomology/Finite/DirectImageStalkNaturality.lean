/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageStalkStages

/-! # Coefficient naturality of the original direct-image stage comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {F G : AbelianSheaf.{u, u + 1} X} (α : F ⟶ G)

/-- The actual original direct-image coefficient map agrees with the actual
coefficient map on the base-changed stage colimit. -/
@[reassoc]
theorem directImageStalkStagesIso_naturality :
    (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.map ((directImage f).map α).hom ≫
      (directImageStalkStagesIso R Ω f G).hom =
        (directImageStalkStagesIso R Ω f F).hom ≫
          colim.map (Functor.whiskerLeft (baseChangedEtaleDiagram R Ω f).op α.hom) := by
  exact (directImageStalkStagesComparison R Ω f).hom.naturality α

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
