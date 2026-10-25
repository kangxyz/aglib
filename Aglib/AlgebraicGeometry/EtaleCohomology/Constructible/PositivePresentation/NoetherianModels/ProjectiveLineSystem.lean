/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Mathlib.AlgebraicGeometry.Noetherian
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineObjects

/-! # The actual Noetherian coefficient-ring system for the native P1

The fixed projective line over the universe-lifted integer ring is pulled
back to the native finite-generated integer subalgebras of the original
ring. Its specified cone is an actual limit. Every stage is Noetherian and
separated, and each stage and the limit retain an actual native-P1 iso.
The initial stage has the two original affine coordinate opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels.ProjectiveLineSystem

universe u

attribute [local instance] ULift.algebra'

/-- The original integer coefficients, placed in the geometric universe. -/
abbrev integerBase := ULift.{u} ℤ

instance integerBase_noetherian : IsNoetherianRing integerBase.{u} :=
  isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

/-- The fixed native polynomial projective line over these integer coefficients. -/
abbrev baseLine : Scheme.{u} :=
  ProjectiveSpace integerBase.{u} (ULift.{u} (Fin 2))

/-- Its original polynomial structure map. -/
abbrev baseMap : baseLine.{u} ⟶ Spec (.of integerBase.{u}) :=
  ProjectiveSpace.toSpec integerBase.{u} (ULift.{u} (Fin 2))

/-- The fixed native projective-line structure map is proper. -/
instance baseMap_proper : IsProper baseMap.{u} :=
  ProjectiveSpace.isProper_toSpec integerBase (ULift.{u} (Fin 2))

variable (R : Type u) [CommRing R]

/-- The literal finite-generated integer-subalgebra base-change diagram. -/
def diagram : (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  Scheme.FiniteTypeSubalgebraLimit.schemeDiagram integerBase R baseMap

/-- The native original cone; its point is the literal original pullback. -/
def cone : Cone (diagram R) :=
  Scheme.FiniteTypeSubalgebraLimit.schemeCone integerBase R baseMap

/-- The original ring-inclusion cocone supplies this actual scheme limit. -/
def coneIsLimit : IsLimit (cone R) :=
  Scheme.FiniteTypeSubalgebraLimit.schemeConeIsLimit integerBase R baseMap

instance transition_affine {s t : (Finset R)ᵒᵖ} (a : s ⟶ t) :
    IsAffineHom ((diagram R).map a) :=
  inferInstanceAs (IsAffineHom
    ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram integerBase R baseMap).map a))

/-- Each original finite-generated integer subalgebra is Noetherian. -/
instance stageRing_noetherian (s : Finset R) :
    IsNoetherianRing (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s) :=
  Algebra.FiniteType.isNoetherianRing integerBase _

/-- The original proper structural map at each literal model stage. -/
def stageStructure (s : (Finset R)ᵒᵖ) :
    (diagram R).obj s ⟶
      Spec (.of (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s.unop)) :=
  pullback.fst (Spec.algebraMap integerBase
    (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s.unop)) baseMap

instance stageStructure_proper (s : (Finset R)ᵒᵖ) :
    IsProper (stageStructure R s) := by
  dsimp only [stageStructure]
  let P : MorphismProperty Scheme.{u} := @IsProper
  let : P.IsStableUnderBaseChange := IsProper.isStableUnderBaseChange
  exact MorphismProperty.pullback_fst (P := P) _ _
    (inferInstanceAs (IsProper baseMap))

/-- The literal model stage is Noetherian by its proper original structure map. -/
instance stage_noetherian (s : (Finset R)ᵒᵖ) : IsNoetherian ((diagram R).obj s) := {
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (stageStructure R s)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (stageStructure R s) }

/-- The original model stage is separated over the terminal affine base. -/
instance stage_separated (s : (Finset R)ᵒᵖ) : ((diagram R).obj s).IsSeparated := by
  constructor
  rw [← terminal.comp_from (stageStructure R s)]
  infer_instance

/-- Each actual model stage is the native P1 over its actual subalgebra ring. -/
def stageIso (s : Finset R) :
    ProjectiveLine.projectiveP1
      (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s) ≅ (diagram R).obj (op s) :=
  ProjectiveSpace.finUliftIso _ 2 ≪≫
    ProjectiveSpace.baseChangeIso
      (algebraMap integerBase (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s))
      (ULift.{u} (Fin 2)) ≪≫
    pullbackSymmetry baseMap (Spec.algebraMap integerBase
      (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R s))

/-- The actual original limit point is the literal native P1 over R. -/
def pointIso : ProjectiveLine.projectiveP1 R ≅ (cone R).pt :=
  ProjectiveSpace.finUliftIso R 2 ≪≫
    ProjectiveSpace.baseChangeIso (algebraMap integerBase R) (ULift.{u} (Fin 2)) ≪≫
    pullbackSymmetry baseMap (Spec.algebraMap integerBase R)

/-- The original proper structure map of the literal limit pullback. -/
def pointStructure : (cone R).pt ⟶ Spec (.of R) :=
  pullback.fst (Spec.algebraMap integerBase R) baseMap

instance pointStructure_proper : IsProper (pointStructure R) := by
  dsimp only [pointStructure]
  let P : MorphismProperty Scheme.{u} := @IsProper
  let : P.IsStableUnderBaseChange := IsProper.isStableUnderBaseChange
  exact MorphismProperty.pullback_fst (P := P) _ _
    (inferInstanceAs (IsProper baseMap))

instance point_separated : (cone R).pt.IsSeparated := by
  constructor
  rw [← terminal.comp_from (pointStructure R)]
  infer_instance

/-- Every original affine-etale generator has an affine structural map to
the limit, using the original separated structure map to Spec R. -/
theorem generator_affine (U : (cone R).pt.AffineEtale) :
    IsAffineHom ((Scheme.AffineEtale.Spec (cone R).pt).obj U).hom := by
  let V := (Scheme.AffineEtale.Spec (cone R).pt).obj U
  have : IsAffine V.left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  have hmap : IsAffineHom (V.hom ≫ pointStructure R) :=
    @isAffineHom_of_isAffine V.left (Spec (.of R)) (V.hom ≫ pointStructure R)
      (inferInstanceAs (IsAffine V.left)) inferInstance
  exact @IsAffineHom.of_comp V.left (cone R).pt (Spec (.of R)) V.hom
    (pointStructure R) hmap inferInstance

/-- The fixed first stage of the original subalgebra system. -/
def initialStage : (Finset R)ᵒᵖ := op ∅

/-- The original map from this stage to the fixed integer projective line. -/
def initialBaseProjection : (diagram R).obj (initialStage R) ⟶ baseLine :=
  pullback.snd (Spec.algebraMap integerBase
    (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R ∅)) baseMap

instance initialBaseProjection_affine : IsAffineHom (initialBaseProjection R) := by
  dsimp only [initialBaseProjection]
  let P : MorphismProperty Scheme.{u} := @IsAffineHom
  let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.pullback_snd (P := P) _ _
    (inferInstanceAs (IsAffineHom (Spec.algebraMap integerBase
      (Algebra.FiniteTypeSubalgebraLimit.stage integerBase R ∅))))

/-- The two original affine coordinate opens at the fixed first model stage. -/
def initialChartOpen (b : Fin 2) : ((diagram R).obj (initialStage R)).Opens :=
  initialBaseProjection R ⁻¹ᵁ
    ProjectiveSpace.coordinateOpen integerBase (ULift.{u} (Fin 2)) (ULift.up b)

theorem initialChart_affine (b : Fin 2) : IsAffineOpen (initialChartOpen R b) :=
  (ProjectiveSpace.isAffineOpen_coordinateOpen integerBase (ULift.{u} (Fin 2))
    (ULift.up b)).preimage (initialBaseProjection R)

/-- The two unchanged original coordinate opens cover the actual first stage. -/
theorem initialCharts_cover : initialChartOpen R 0 ⊔ initialChartOpen R 1 = ⊤ := by
  have hcover :
      ProjectiveSpace.coordinateOpen integerBase (ULift.{u} (Fin 2)) (ULift.up 0) ⊔
        ProjectiveSpace.coordinateOpen integerBase (ULift.{u} (Fin 2)) (ULift.up 1) = ⊤ := by
    apply top_unique
    rw [← ProjectiveSpace.iSup_coordinateOpen_eq_top integerBase (ULift.{u} (Fin 2))]
    apply iSup_le
    rintro ⟨b⟩
    fin_cases b
    · exact le_sup_left
    · exact le_sup_right
  change _ ⁻¹ᵁ _ ⊔ _ ⁻¹ᵁ _ = ⊤
  rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]

end NoetherianModels.ProjectiveLineSystem
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
