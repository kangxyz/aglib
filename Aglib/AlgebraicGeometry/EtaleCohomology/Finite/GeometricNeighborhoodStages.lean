/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback

/-! # Actual small-étale stages in the base-changed geometric neighborhood system -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original small-étale objects of the geometric neighborhood diagram. -/
abbrev etaleDiagram : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ (Spec (.of R)).Etale :=
  toPointElements R Ω ⋙ Functor.Elements.π (pointSmallEtale (Spec.algebraMap R Ω)).fiber

/-- The actual objects used by the original direct image, pulled back along f. -/
abbrev baseChangedEtaleDiagram : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ X.Etale :=
  etaleDiagram R Ω ⋙ siteBaseChange f

/-- Forgetting the small-étale structure gives the actual limiting Over diagram. -/
lemma baseChangedEtaleDiagram_forget :
    baseChangedEtaleDiagram R Ω f ⋙ Scheme.Etale.forget X = baseChangedDiagram R Ω f := rfl

/-- The limiting cone has the actual original small-étale stages as its legs. -/
abbrev baseChangedEtaleCone : Cone (baseChangedEtaleDiagram R Ω f ⋙ Scheme.Etale.forget X) :=
  baseChangedCone R Ω f

/-- The actual cone over the original small-étale stages is limiting as schemes. -/
def baseChangedEtaleConeIsLimit :
    IsLimit ((Over.forget X).mapCone (baseChangedEtaleCone R Ω f)) :=
  baseChangedConeIsLimit R Ω f

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
