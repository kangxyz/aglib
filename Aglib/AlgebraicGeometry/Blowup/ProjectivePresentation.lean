/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Epimorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteType
public import Aglib.AlgebraicGeometry.Modules.Coherent.Projective.Presentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource

/-!
# Tautological presentations after arbitrary base change of a blowup

The line on the literal fibre product is the pullback of the invertible
image ideal on the original blowup. Its degree-one quotient has the full
pulled-back ideal module as source. No flatness or Cartier property of the
image ideal after this base change is used.

A closed projective embedding of the new base supplies a common negative
twist presentation of that module. Pulling this presentation to the literal
fibre product and cancelling the common line produces finitely many actual
generating sections of the twisted tautological line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

variable {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)

/-- The actual map from the inverse-image centre to the original centre. -/
def centreMap : (I.comap B.map).subscheme ⟶ I.subscheme :=
  (I.comap B.map).subschemeMap I B.map (I.le_map_comap B.map)

@[reassoc]
theorem centreMap_ι :
    centreMap B ≫ I.subschemeι = (I.comap B.map).subschemeι ≫ B.map :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem centre_isPullback :
    IsPullback (centreMap B) (I.comap B.map).subschemeι I.subschemeι B.map :=
  (isPullback_of_isClosedImmersion (I.comap B.map).subschemeι I.subschemeι
    (centreMap B) B.map (centreMap_ι B).symm (by simp)).flip

/-- The original invertible image ideal, before any additional base change. -/
def tautologicalLine : LineBundle B.Y :=
  ⟨idealModule (I.comap B.map).subschemeι, B.cartier⟩

/-- The canonical degree-one quotient onto the original tautological line. -/
def tautologicalQuotient :
    (Modules.pullback B.map).obj (idealModule I.subschemeι) ⟶
      (tautologicalLine B).val :=
  idealPullbackMap I.subschemeι (I.comap B.map).subschemeι B.map
    (centreMap B) (centreMap_ι B)

instance tautologicalQuotient_epi : Epi (tautologicalQuotient B) :=
  idealPullbackMap_epi_of_isPullback _ _ _ _ _ (centre_isPullback B)

variable {W : Scheme.{u}} (f : W ⟶ X)

/-- The invertible module on the literal base-changed blowup. -/
def pulledTautologicalLine : LineBundle (Limits.pullback B.map f) :=
  pullbackLineBundle (Limits.pullback.fst B.map f) (tautologicalLine B)

/-- The full degree-one module on the new base, retaining possible torsion. -/
def degreeOneModule : W.Modules :=
  (Modules.pullback f).obj (idealModule I.subschemeι)

/-- Pullback of the original quotient through the original fibre-product square. -/
def pulledTautologicalQuotient :
    (Modules.pullback (Limits.pullback.snd B.map f)).obj (degreeOneModule (I := I) f) ⟶
      (pulledTautologicalLine B f).val :=
  (pullbackComp (Limits.pullback.snd B.map f) f).hom.app _ ≫
    (pullbackCongr (Limits.pullback.condition (f := B.map) (g := f)).symm).hom.app _ ≫
      (pullbackComp (Limits.pullback.fst B.map f) B.map).inv.app _ ≫
        (Modules.pullback (Limits.pullback.fst B.map f)).map (tautologicalQuotient B)

instance pulledTautologicalQuotient_epi : Epi (pulledTautologicalQuotient B f) := by
  dsimp only [pulledTautologicalQuotient]
  infer_instance

/-- The degree-one module is coherent in the finite-type sense when the
original base is locally Noetherian. The new base and its map are arbitrary. -/
theorem degreeOneModule_affineLocallyFiniteType [IsLocallyNoetherian X] :
    affineLocallyFiniteType W (degreeOneModule (I := I) f) := by
  apply affineLocallyFiniteType_pullback f
  apply I.affineLocallyFG_iff_affineLocallyFiniteType.mp
  intro U
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

variable {A : Type u} [CommRing A] {ι : Type u}
  (j : W ⟶ ProjectiveSpace A ι)

/-- The common negative twist, pulled through the literal projection. -/
def sourceTwistLine (N : ℕ) : LineBundle (Limits.pullback B.map f) :=
  pullbackLineBundle (Limits.pullback.snd B.map f)
    (pullbackLineBundle j (ProjectiveSpace.twistingLineBundle A ι (-(N : ℤ))))

/-- The tautological line with the dual of the common negative twist. -/
def twistedTautologicalLine (N : ℕ) : LineBundle (Limits.pullback B.map f) :=
  tensorLineBundle _ (dualLineBundle _ (sourceTwistLine B f j N))
    (pulledTautologicalLine B f)

/-- The original common-twist presentation on the projective base. -/
theorem exists_baseTwistPresentation [IsLocallyNoetherian X] [Finite ι]
    [IsClosedImmersion j] (bound : ℕ) :
    ∃ N : ℕ, bound < N ∧ ∃ (J : Type u) (_ : Finite J)
      (π : (∐ fun _ : J => (Modules.pullback j).obj
        (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f),
        Epi π := by
  obtain ⟨N, hN, J, hJ, π, hπ, _⟩ :=
    Coherent.Projective.exists_uniformNegativeTwistEpimorphism A ι j
      (degreeOneModule (I := I) f) (degreeOneModule_affineLocallyFiniteType (I := I) f) bound
  exact ⟨N, hN, J, hJ, π, hπ⟩

/-- Pull the specified original base presentation through the literal square
and compose with the canonical degree-one quotient. -/
def commonTwistQuotient (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f) :
    (∐ fun _ : J => (sourceTwistLine B f j N).val) ⟶
      (pulledTautologicalLine B f).val :=
  (PreservesCoproduct.iso (Modules.pullback (Limits.pullback.snd B.map f))
    (fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ))))).inv ≫
    (Modules.pullback (Limits.pullback.snd B.map f)).map π ≫
      pulledTautologicalQuotient B f

instance commonTwistQuotient_epi (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f) [Epi π] :
    Epi (commonTwistQuotient B f j N π) := by
  let T : W.Modules ⥤ (Limits.pullback B.map f).Modules :=
    Modules.pullback (Limits.pullback.snd B.map f)
  let : Epi (T.map π) := T.map_epi π
  let : Epi (pulledTautologicalQuotient B f) := pulledTautologicalQuotient_epi B f
  change Epi ((PreservesCoproduct.iso T
    (fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ))))).inv ≫
      T.map π ≫ pulledTautologicalQuotient B f)
  infer_instance

/-- The original base presentation supplies a finite quotient by copies of
one common line on the unchanged fibre product. -/
theorem exists_commonTwistQuotient [IsLocallyNoetherian X] [Finite ι]
    [IsClosedImmersion j] (bound : ℕ) :
    ∃ N : ℕ, bound < N ∧ ∃ (J : Type u) (_ : Finite J)
      (ρ : (∐ fun _ : J => (sourceTwistLine B f j N).val) ⟶
        (pulledTautologicalLine B f).val), Epi ρ := by
  obtain ⟨N, hN, J, hJ, π, hπ⟩ := exists_baseTwistPresentation (I := I) f j bound
  let : Finite J := hJ
  let : Epi π := hπ
  exact ⟨N, hN, J, hJ, commonTwistQuotient B f j N π, inferInstance⟩

/-- The original indexed row of a specified finite coproduct quotient. -/
def lineQuotientRow {T : Scheme.{u}} (L K : LineBundle T) {J : Type u}
    (ρ : (∐ fun _ : J => L.val) ⟶ K.val) : J → (L.val ⟶ K.val) :=
  fun t => Sigma.ι (fun _ : J => L.val) t ≫ ρ

/-- Reassembling the original row recovers the specified quotient exactly. -/
theorem lineQuotientRow_desc {T : Scheme.{u}} (L K : LineBundle T) {J : Type u}
    (ρ : (∐ fun _ : J => L.val) ⟶ K.val) :
    Sigma.desc (lineQuotientRow L K ρ) = ρ := by
  apply Sigma.hom_ext
  intro t
  exact Sigma.ι_comp_desc _ _

instance lineQuotientRow_epi {T : Scheme.{u}} (L K : LineBundle T) {J : Type u}
    (ρ : (∐ fun _ : J => L.val) ⟶ K.val) [Epi ρ] :
    Epi (Sigma.desc (lineQuotientRow L K ρ)) := by
  rw [lineQuotientRow_desc]
  infer_instance

private theorem finite_family_of_line_quotient {T : Scheme.{u}}
    (L K : LineBundle T) {J : Type u}
    (ρ : (∐ fun _ : J => L.val) ⟶ K.val) [Epi ρ] :
    ∃ s : J → (SheafOfModules.unit T.ringCatSheaf ⟶
      (tensorLineBundle T (dualLineBundle T L) K).val), Epi (Sigma.desc s) := by
  let : Epi (Sigma.desc (lineQuotientRow L K ρ)) := lineQuotientRow_epi L K ρ
  exact ⟨fun t => ProjectiveSpace.FromSections.LineSource.sectionOfHom L.val K.val L.property
      (lineQuotientRow L K ρ t),
    ProjectiveSpace.FromSections.LineSource.sectionFamily_epi L.val K.val L.property
      (lineQuotientRow L K ρ)⟩

/-- The twisted tautological line on the literal base change has a finite
epimorphic family of actual global sections. No flatness is required. -/
theorem exists_finite_twistedTautologicalFamily [IsLocallyNoetherian X] [Finite ι]
    [IsClosedImmersion j] (bound : ℕ) :
    ∃ N : ℕ, bound < N ∧ ∃ (J : Type u) (_ : Finite J)
      (s : J → (SheafOfModules.unit (Limits.pullback B.map f).ringCatSheaf ⟶
        (twistedTautologicalLine B f j N).val)), Epi (Sigma.desc s) := by
  obtain ⟨N, hN, J, hJ, ρ, hρ⟩ := exists_commonTwistQuotient B f j bound
  let : Epi ρ := hρ
  obtain ⟨s, hs⟩ := finite_family_of_line_quotient
    (sourceTwistLine B f j N) (pulledTautologicalLine B f) ρ
  exact ⟨N, hN, J, hJ, s, hs⟩

/-- The actual coordinate map of the original common-twist quotient row. -/
def coordinateMap (N : ℕ) {J : Type u} [Finite J]
    (ρ : (∐ fun _ : J => (sourceTwistLine B f j N).val) ⟶
      (pulledTautologicalLine B f).val) [Epi ρ] :
    Limits.pullback B.map f ⟶ ProjectiveSpace A J := by
  let L : LineBundle (Limits.pullback B.map f) := sourceTwistLine B f j N
  let K : LineBundle (Limits.pullback B.map f) := pulledTautologicalLine B f
  let d := lineQuotientRow L K ρ
  let : Epi (Sigma.desc d) := lineQuotientRow_epi L K ρ
  exact ProjectiveSpace.FromSections.LineSource.mapOfFamily L.val K.val L.property
    (Limits.pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι) K.property d

/-- The canonical coordinate map retains the exact original structural morphism. -/
theorem coordinateMap_toSpec (N : ℕ) {J : Type u} [Finite J]
    (ρ : (∐ fun _ : J => (sourceTwistLine B f j N).val) ⟶
      (pulledTautologicalLine B f).val) [Epi ρ] :
    coordinateMap B f j N ρ ≫ ProjectiveSpace.toSpec A J =
      Limits.pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι := by
  let : Epi (Sigma.desc
      (lineQuotientRow (sourceTwistLine B f j N) (pulledTautologicalLine B f) ρ)) :=
    lineQuotientRow_epi _ _ ρ
  exact ProjectiveSpace.FromSections.LineSource.mapOfFamily_toSpec
    (sourceTwistLine B f j N).val (pulledTautologicalLine B f).val
    (sourceTwistLine B f j N).property
    (Limits.pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι)
    (pulledTautologicalLine B f).property
    (lineQuotientRow (sourceTwistLine B f j N) (pulledTautologicalLine B f) ρ)

/-- The actual coordinate map of the original base presentation. -/
def coordinateMapOfPresentation (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f) [Epi π] :
    Limits.pullback B.map f ⟶ ProjectiveSpace A J :=
  coordinateMap B f j N (commonTwistQuotient B f j N π)

/-- The original base presentation retains the exact structure triangle. -/
theorem coordinateMapOfPresentation_toSpec (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f) [Epi π] :
    coordinateMapOfPresentation B f j N π ≫ ProjectiveSpace.toSpec A J =
      Limits.pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι :=
  coordinateMap_toSpec B f j N (commonTwistQuotient B f j N π)

/-- The constructed base presentation supplies its canonical projective
coordinate map with the original triangle. Closed immersion remains separate. -/
theorem exists_projectiveCoordinates [IsLocallyNoetherian X] [Finite ι]
    [IsClosedImmersion j] (bound : ℕ) :
    ∃ N : ℕ, bound < N ∧ ∃ (J : Type u) (hJ : Finite J)
      (π : (∐ fun _ : J => (Modules.pullback j).obj
        (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f)
      (hπ : Epi π),
      let : Finite J := hJ
      let : Epi π := hπ
      coordinateMapOfPresentation B f j N π ≫ ProjectiveSpace.toSpec A J =
        Limits.pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι := by
  obtain ⟨N, hN, J, hJ, π, hπ⟩ := exists_baseTwistPresentation (I := I) f j bound
  let : Finite J := hJ
  let : Epi π := hπ
  exact ⟨N, hN, J, hJ, π, hπ, coordinateMapOfPresentation_toSpec B f j N π⟩

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation
