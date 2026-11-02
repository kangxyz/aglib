/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodLimit
public import Aglib.AlgebraicGeometry.Limits.FixedBaseChange

/-! # The original geometric neighborhood limit after fixed base change

The same native spectrum cone is pulled back over the supplied fixed scheme.
No new colimit or local model is introduced. The historical namespace is
preserved so existing cohomological consumers use this same implementation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The literal structural maps of the geometric neighborhood diagram. -/
def structureMap : diagram R Ω ⟶ (Functor.const _).obj (Spec (.of R)) where
  app i := Spec.algebraMap R i.unop.algebra
  naturality {i j} g := by
    change Spec.map (CommRingCat.ofHom g.unop.val.toRingHom) ≫
      Spec.algebraMap R j.unop.algebra = Spec.algebraMap R i.unop.algebra ≫ 𝟙 _
    rw [Category.comp_id, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact g.unop.val.comp_algebraMap

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

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
