/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Epimorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource

/-!
# Projective coordinates after blowing up an actual coordinate ideal

An epimorphic finite family from a line module to an ideal module yields
an actual morphism to projective space on the native blowup. The blowup is
proper over a locally Noetherian source and is unchanged on every open where
the original ideal is the unit ideal. The construction retains the original
coordinate morphisms, their pulled inclusions, and the base map.

No integrality, reducedness, regularity, or dimension bound is imposed.
This is the coordinate-ideal step, not the theorem extending an arbitrary
map on a prescribed dense open: constructing the global line-source family
from that open map remains a separate denominator-extension obligation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {X Y : Scheme.{u}}

/-- The original map between the actual closed base-ideal subschemes. -/
def baseIdealSourceMap (J : X.IdealSheafData) (β : Y ⟶ X) :
    (J.comap β).subscheme ⟶ J.subscheme :=
  IdealSheafData.subschemeMap (J.comap β) J β (J.le_map_comap β)

@[reassoc]
theorem baseIdealSourceMap_comm (J : X.IdealSheafData) (β : Y ⟶ X) :
    baseIdealSourceMap J β ≫ J.subschemeι = (J.comap β).subschemeι ≫ β :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- This is the actual cartesian square, not an assumed comparison of modules. -/
theorem baseIdealSourceMap_isPullback (J : X.IdealSheafData) (β : Y ⟶ X) :
    IsPullback (baseIdealSourceMap J β) (J.comap β).subschemeι J.subschemeι β := by
  apply IsPullback.flip
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
    (J.comap β).subschemeι J.subschemeι (baseIdealSourceMap J β) β
    (baseIdealSourceMap_comm J β).symm
  rw [J.ker_subschemeι, (J.comap β).ker_subschemeι]

/-- The canonical map onto the actual inverse-image ideal module. -/
def baseIdealPullbackMap (J : X.IdealSheafData) (β : Y ⟶ X) :
    (Scheme.Modules.pullback β).obj (Hom.idealModule J.subschemeι) ⟶
      Hom.idealModule (J.comap β).subschemeι :=
  Hom.idealPullbackMap J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)

/-- This original comparison is epimorphic along every actual morphism. -/
instance baseIdealPullbackMap_epi (J : X.IdealSheafData) (β : Y ⟶ X) :
    Epi (baseIdealPullbackMap J β) :=
  Hom.idealPullbackMap_epi_of_isPullback J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)
    (baseIdealSourceMap_isPullback J β)

/-- The actual inclusion triangle of the same canonical epimorphism. -/
@[reassoc]
theorem baseIdealPullbackMap_inclusion (J : X.IdealSheafData) (β : Y ⟶ X) :
    baseIdealPullbackMap J β ≫ Hom.idealInclusion (J.comap β).subschemeι =
      (Scheme.Modules.pullback β).map (Hom.idealInclusion J.subschemeι) ≫
        (pullbackUnitIso β).hom :=
  Hom.idealPullbackMap_inclusion J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)

section LineSource

variable (D : X.Modules) (J : X.IdealSheafData)
variable {I : Type u} (d : I → (D ⟶ Hom.idealModule J.subschemeι))

/-- Pull the original coordinate into the actual image ideal, not into an
unjustified identification of that ideal with the tensor pullback. -/
def lineSourcePulledCoordinate (β : Y ⟶ X) (i : I) :
    (Scheme.Modules.pullback β).obj D ⟶ Hom.idealModule (J.comap β).subschemeι :=
  (Scheme.Modules.pullback β).map (d i) ≫ baseIdealPullbackMap J β

/-- The actual image-ideal coordinate row remains epimorphic under arbitrary
base change, including nonflat blowdown morphisms. -/
instance lineSourcePulledCoordinate_epi [Epi (Sigma.desc d)] (β : Y ⟶ X) :
    Epi (Sigma.desc (lineSourcePulledCoordinate D J d β)) := by
  let F := Scheme.Modules.pullback β
  let : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction β)
  have : Epi (F.map (Sigma.desc d)) := inferInstance
  have hrow : Epi (Sigma.desc (fun i ↦ F.map (d i))) := by
    rw [← sigmaComparison_map_desc F (fun _ : I ↦ D)
      (Hom.idealModule J.subschemeι) d]
    infer_instance
  have heq : Sigma.desc (lineSourcePulledCoordinate D J d β) =
      Sigma.desc (fun i ↦ F.map (d i)) ≫ baseIdealPullbackMap J β := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, lineSourcePulledCoordinate, F]
  rw [heq]
  infer_instance

/-- The pulled coordinate has exactly the original numerator after inclusion
in the structure module, without replacing the scalar or the coordinate. -/
@[reassoc]
theorem lineSourcePulledCoordinate_inclusion (β : Y ⟶ X) (i : I) :
    lineSourcePulledCoordinate D J d β i ≫ Hom.idealInclusion (J.comap β).subschemeι =
      (Scheme.Modules.pullback β).map (d i ≫ Hom.idealInclusion J.subschemeι) ≫
        (pullbackUnitIso β).hom := by
  rw [lineSourcePulledCoordinate, Category.assoc, baseIdealPullbackMap_inclusion,
    ← Category.assoc, ← Functor.map_comp]

variable {R : Type u} [CommRing R] [Finite I] [Epi (Sigma.desc d)]
variable (hD : IsLocallyRankOne X D) (p : X ⟶ Spec (.of R))

/-- The projective map on the actual native blowup of the coordinate ideal. -/
def lineSourceBlowupMap : (Blowup.blowupDatum J).Y ⟶ ProjectiveSpace R I :=
  ProjectiveSpace.FromSections.LineSource.mapOfFamily
    ((Scheme.Modules.pullback (Blowup.blowupDatum J).map).obj D)
    (Hom.idealModule (J.comap (Blowup.blowupDatum J).map).subschemeι)
    (pullback_locallyRankOne _ D hD) ((Blowup.blowupDatum J).map ≫ p)
    (Blowup.blowupDatum J).cartier
    (lineSourcePulledCoordinate D J d (Blowup.blowupDatum J).map)

/-- The structural triangle is the original map to the original affine base. -/
@[reassoc]
theorem lineSourceBlowupMap_toSpec :
    lineSourceBlowupMap D J d hD p ≫ ProjectiveSpace.toSpec R I =
      (Blowup.blowupDatum J).map ≫ p :=
  ProjectiveSpace.FromSections.LineSource.mapOfFamily_toSpec _ _ _ _ _ _

/-- Each native homogeneous coordinate recovers the original pulled map, on
the whole blowup rather than only at a generic point. -/
theorem lineSourceBlowupMap_recoveredCoordinate (i : I) :
    ProjectiveSpace.FromSections.LineSource.recoveredCoordinate
      ((Scheme.Modules.pullback (Blowup.blowupDatum J).map).obj D)
      (Hom.idealModule (J.comap (Blowup.blowupDatum J).map).subschemeι)
      (pullback_locallyRankOne _ D hD) ((Blowup.blowupDatum J).map ≫ p)
      (Blowup.blowupDatum J).cartier
      (lineSourcePulledCoordinate D J d (Blowup.blowupDatum J).map) i =
      lineSourcePulledCoordinate D J d (Blowup.blowupDatum J).map i :=
  ProjectiveSpace.FromSections.LineSource.recoveredCoordinate_eq _ _ _ _ _ _ i

include D d hD in
/-- The constructed projective map has a proper blowdown and an isomorphism
on the entire protected open. Only the coordinate-data construction is an
input; properness and admissibility are proved for the actual blowup. -/
theorem exists_proper_lineSource_coordinate_map [IsLocallyNoetherian X]
    (U : X.Opens) (hU : J.comap U.ι = ⊤) :
    ∃ g : (Blowup.blowupDatum J).Y ⟶ ProjectiveSpace R I,
      IsProper (Blowup.blowupDatum J).map ∧
      IsIso ((Blowup.blowupDatum J).map ∣_ U) ∧
      g ≫ ProjectiveSpace.toSpec R I = (Blowup.blowupDatum J).map ≫ p := by
  refine ⟨lineSourceBlowupMap D J d hD p,
    (Blowup.blowupDatum J).isProper_of_isLocallyNoetherian, ?_,
    lineSourceBlowupMap_toSpec D J d hD p⟩
  let B := Blowup.blowupDatum J
  let : IsIso (pullback.snd B.map U.ι) := B.pullback_snd_isIso_of_comap_eq_top U.ι hU
  rw [← (isPullback_morphismRestrict B.map U).flip.isoPullback_hom_snd]
  infer_instance

end LineSource

end AlgebraicGeometry.Scheme.RationalCoordinates
