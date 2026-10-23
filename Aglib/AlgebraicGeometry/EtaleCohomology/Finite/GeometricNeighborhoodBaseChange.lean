/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFunctor
public import Aglib.AlgebraicGeometry.Limits.FixedBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections

/-! # Actual base-changed geometric-neighborhood limits and represented sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The literal structural maps of the geometric neighborhood diagram. -/
def structureMap : diagram R Ω ⟶ (Functor.const _).obj (Spec (.of R)) where
  app i := Spec.algebraMap R i.unop.algebra
  naturality {i j} f := by
    change (etaleMap R Ω f.unop).left ≫ (etaleObject R Ω j.unop).hom =
      (etaleObject R Ω i.unop).hom ≫ 𝟙 _
    exact (etaleMap R Ω f.unop).w.trans (Category.comp_id _).symm

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The native pullback system, as actual objects over the fixed source. -/
def baseChangedDiagram : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ Over X :=
  Over.lift (diagram R Ω) (structureMap R Ω) ⋙ Over.pullback f

/-- The native pullback cone; its point is the actual strict-local base change. -/
def baseChangedCone : Cone (baseChangedDiagram R Ω f) :=
  (Over.pullback f).mapCone
    (Over.liftCone (diagram R Ω) (structureMap R Ω) (specCone R Ω)
      (Spec.algebraMap R (GeometricEtaleColimit R Ω))
      (fun i => π_structure R Ω i.unop))

/-- The underlying actual scheme cone is a limit, without a continuity premise. -/
def baseChangedConeIsLimit : IsLimit ((Over.forget X).mapCone (baseChangedCone R Ω f)) :=
  Scheme.FixedBaseChange.isLimitCone (diagram R Ω) (structureMap R Ω) f
    (specCone R Ω) (Spec.algebraMap R (GeometricEtaleColimit R Ω))
    (fun i => π_structure R Ω i.unop) (specConeIsLimit R Ω)

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
