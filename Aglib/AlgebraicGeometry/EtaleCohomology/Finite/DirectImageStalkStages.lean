/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodStages
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-! # Original direct-image stalks as actual base-changed stage colimits -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (F : AbelianSheaf.{u, u + 1} X)

/-- The original direct image uses these actual base-changed stage sections. -/
abbrev directImageStageSections : (GeometricEtaleNeighborhood R Ω)ᵒᵖᵒᵖ ⥤
    AddCommGrpCat.{u + 1} := (baseChangedEtaleDiagram R Ω f).op ⋙ F.obj

/-- The coefficient functor of the original base-changed stage sections. -/
abbrev directImageStageSectionsFunctor :
    AbelianSheaf.{u, u + 1} X ⥤
      ((GeometricEtaleNeighborhood R Ω)ᵒᵖᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (baseChangedEtaleDiagram R Ω f).op

/-- The two original final functors give one whole natural stalk comparison. -/
def directImageStalkStagesComparison :
    directImage f ⋙ sheafToPresheaf (Scheme.smallEtaleTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1} ⋙
        (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber ≅
      directImageStageSectionsFunctor R Ω f ⋙ colim :=
  Functor.isoWhiskerLeft
      (directImage f ⋙ sheafToPresheaf (Scheme.smallEtaleTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}) (stalkComparison R Ω).symm ≪≫
    Functor.isoWhiskerLeft (directImageStageSectionsFunctor R Ω f)
      (Functor.Final.colimIso (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse)

/-- Reindexing the original stalk by the actual finite-presentation neighborhoods
requires no finiteness assumption on the source map. -/
def directImageStalkStagesIso :
    (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.obj ((directImage f).obj F).obj ≅
      colimit (directImageStageSections R Ω f F) :=
  (directImageStalkStagesComparison R Ω f).app F

/-- Each component is the original two-final-functor comparison. -/
theorem directImageStalkStagesIso_eq_original :
    directImageStalkStagesIso R Ω f F =
      (stalkIso R Ω ((directImage f).obj F).obj).symm ≪≫
        Functor.Final.colimitIso (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse
          (directImageStageSections R Ω f F) := rfl

/-- Every original geometric germ is carried to its literal base-changed stage leg. -/
@[reassoc (attr := simp)]
lemma germ_directImageStalkStagesIso_hom (i : GeometricEtaleNeighborhood R Ω) :
    (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
      (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj F).obj ≫
        (directImageStalkStagesIso R Ω f F).hom =
          colimit.ι (directImageStageSections R Ω f F) (op (op i)) := by
  let E := stalkIso R Ω ((directImage f).obj F).obj
  let K := Functor.Final.colimitIso
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse
    (directImageStageSections R Ω f F)
  have h := ι_stalkIso_hom R Ω ((directImage f).obj F).obj i
  exact (congrArg (fun q :
    (sectionDiagram R Ω ((directImage f).obj F).obj).obj i ⟶
      (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.obj ((directImage f).obj F).obj =>
        q ≫ (E.inv ≫ K.hom)) h.symm).trans
    ((Category.assoc (colimit.ι (sectionDiagram R Ω ((directImage f).obj F).obj) i)
      E.hom (E.inv ≫ K.hom)).trans
      ((congrArg (fun q =>
        colimit.ι (sectionDiagram R Ω ((directImage f).obj F).obj) i ≫ q)
        (E.hom_inv_id_assoc K.hom)).trans
        (Functor.Final.ι_colimitIso_hom
          (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse
          (directImageStageSections R Ω f F) i)))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
