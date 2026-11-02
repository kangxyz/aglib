/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFunctor
public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections

/-! # Actual base-changed geometric-neighborhood limits and represented sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Finite-presentation represented sections descend along the actual
base-changed neighborhood cone, with no finite-presentation hypothesis on f. -/
def baseChangedRepresentedSectionsIsColimit [QuasiCompact f] [QuasiSeparated f]
    (Y : Over X) [LocallyOfFinitePresentation Y.hom] :
    IsColimit (Continuity.representedSectionsCocone
      (baseChangedDiagram R Ω f) (baseChangedCone R Ω f) Y) := by
  have hcompact (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      CompactSpace ((diagram R Ω).obj i) :=
    inferInstanceAs (CompactSpace (Spec (.of i.unop.algebra)))
  have hqs (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      QuasiSeparatedSpace ((diagram R Ω).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of i.unop.algebra)))
  have haffine {i j : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ j) :
      IsAffineHom ((diagram R Ω).map a) :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom a.unop.val.toRingHom)))
  have hsourcecompact (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      CompactSpace ((baseChangedDiagram R Ω f).obj i).left :=
    Scheme.FixedBaseChange.obj_compactSpace (diagram R Ω) (structureMap R Ω) f i
  have hsourceqs (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      QuasiSeparatedSpace ((baseChangedDiagram R Ω f).obj i).left :=
    Scheme.FixedBaseChange.obj_quasiSeparatedSpace (diagram R Ω) (structureMap R Ω) f i
  have hsourceaffine {i j : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ j) :
      IsAffineHom ((baseChangedDiagram R Ω f).map a).left :=
    Scheme.FixedBaseChange.map_isAffineHom (diagram R Ω) (structureMap R Ω) f a
  exact Continuity.representedSectionsCoconeIsColimit
    (baseChangedDiagram R Ω f) (baseChangedCone R Ω f) (baseChangedConeIsLimit R Ω f) Y

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
