/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules


public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.DualMapToPullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightInsertion


/-!
# AlgebraicGeometry / Blowup / Differentials / PairIdeal / OpenCentre

Source: `IntegralTrace/PairIdealRawOpenTransport.lean`.
Incoming SHA256: `95a01181178bff0fe417dcf0273c622e1a9a48b0b95d8ca1912cde6b78e160ae`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

section OpenCentre

variable (R : Type u) [CommRing R] (I : Ideal R) (X : Scheme.{u}) (p : X)
  (j : Spec (.of R) ⟶ X)
  (hcentre : (X.fromSpecResidueField p).ker.comap j = Blowup.affineCenter R I)

/-- The original canonical blowup comparison of the actual affine open centre. -/
def pairIdeal_openComparison : canonicalBlowup I ⟶ pointBlowup X p :=
  Blowup.BaseChange.map j hcentre (pointBlowupDatum X p)
    (Blowup.blowupDatum (Blowup.affineCenter R I))

/-- The same canonical comparison retains the original blowdown triangle. -/
theorem pairIdeal_openComparison_triangle :
    pairIdeal_openComparison R I X p j hcentre ≫ pointBlowdown X p = blowdown I ≫ j :=
  Blowup.BaseChange.map_triangle j hcentre (pointBlowupDatum X p)
    (Blowup.blowupDatum (Blowup.affineCenter R I))

/-- Openness follows from actual flat base change of the original open immersion. -/
theorem pairIdeal_openComparison_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (pairIdeal_openComparison R I X p j hcentre) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Blowup.BaseChange.isPullback_of_flat j inferInstance hcentre
      (pointBlowupDatum X p) (Blowup.blowupDatum (Blowup.affineCenter R I))).flip
    inferInstance

local notation "q" => pairIdeal_openComparison R I X p j hcentre
local notation "JY" => Scheme.IdealSheafData.comap
  (Scheme.Hom.ker (Scheme.fromSpecResidueField X p)) (pointBlowdown X p)
local notation "JZ" => Scheme.IdealSheafData.comap (Blowup.affineCenter R I) (blowdown I)

/-- The literal inverse-image centre, with no replacement exceptional scheme. -/
theorem pairIdeal_openCentre_comap : (JY).comap q = JZ := by
  rw [← Scheme.IdealSheafData.comap_comp,
    pairIdeal_openComparison_triangle, Scheme.IdealSheafData.comap_comp, hcentre]

/-- The native map between the literal original centre subschemes. -/
def pairIdeal_openCentreMap : (JZ).subscheme ⟶ (JY).subscheme :=
  Scheme.IdealSheafData.subschemeMap JZ JY q
    (by rw [← pairIdeal_openCentre_comap R I X p j hcentre]; exact (JY).le_map_comap q)

/-- The centre map retains the original inclusions into the original blowups. -/
theorem pairIdeal_openCentreMap_inclusion :
    pairIdeal_openCentreMap R I X p j hcentre ≫ (JY).subschemeι = (JZ).subschemeι ≫ q :=
  Scheme.IdealSheafData.subschemeMap_subschemeι JZ JY q _

variable (hp : IsClosed ({p} : Set X))

/-- The original literal-fibre comparison followed by the native ideal pullback map. -/
def pairIdeal_openIdealMap :
    (pullback q).obj (pointIdealLine X p hp).val ⟶ (centreIdealLine I).val :=
  (pullback q).map (pointIdealCentreIso X p hp).hom ≫
    idealPullbackMap (JY).subschemeι (JZ).subschemeι q
      (pairIdeal_openCentreMap R I X p j hcentre)
      (pairIdeal_openCentreMap_inclusion R I X p j hcentre)

/-- The actual ideal map preserves the original inclusion and structural unit. -/
theorem pairIdeal_openIdealMap_inclusion :
    pairIdeal_openIdealMap R I X p j hcentre hp ≫ idealInclusion (JZ).subschemeι =
      (pullback q).map (idealInclusion (pointExceptionalι X p)) ≫
        (pullbackUnitIso q).hom := by
  let A₀ : (pointBlowup X p).Modules := idealModule (pointExceptionalι X p)
  let A₁ : (pointBlowup X p).Modules := idealModule (JY).subschemeι
  let U₀ : (pointBlowup X p).Modules := SheafOfModules.unit (pointBlowup X p).ringCatSheaf
  let B₀ : (canonicalBlowup I).Modules := idealModule (JZ).subschemeι
  let V₀ : (canonicalBlowup I).Modules := SheafOfModules.unit (canonicalBlowup I).ringCatSheaf
  let F : (pointBlowup X p).Modules ⥤ (canonicalBlowup I).Modules := pullback q
  let c : A₀ ⟶ A₁ := (pointIdealCentreIso X p hp).hom
  let i : A₁ ⟶ U₀ := idealInclusion (JY).subschemeι
  let i₀ : A₀ ⟶ U₀ := idealInclusion (pointExceptionalι X p)
  let k : F.obj A₁ ⟶ B₀ := idealPullbackMap (JY).subschemeι (JZ).subschemeι q
    (pairIdeal_openCentreMap R I X p j hcentre)
    (pairIdeal_openCentreMap_inclusion R I X p j hcentre)
  let i' : B₀ ⟶ V₀ := idealInclusion (JZ).subschemeι
  let u : F.obj U₀ ⟶ V₀ := (pullbackUnitIso q).hom
  have hk : k ≫ i' = F.map i ≫ u :=
    idealPullbackMap_inclusion (JY).subschemeι (JZ).subschemeι q
      (pairIdeal_openCentreMap R I X p j hcentre)
      (pairIdeal_openCentreMap_inclusion R I X p j hcentre)
  have hc : c ≫ i = i₀ := pointIdealCentreIso_hom_inclusion X p hp
  calc
    (show F.obj A₀ ⟶ V₀ from (F.map c ≫ k) ≫ i') =
        (show F.obj A₀ ⟶ V₀ from F.map c ≫ (k ≫ i')) := Category.assoc _ _ _
    _ = (show F.obj A₀ ⟶ V₀ from F.map c ≫ (F.map i ≫ u)) :=
      congrArg (fun z : F.obj A₁ ⟶ V₀ => F.map c ≫ z) hk
    _ = (show F.obj A₀ ⟶ V₀ from (F.map c ≫ F.map i) ≫ u) :=
      (Category.assoc _ _ _).symm
    _ = (show F.obj A₀ ⟶ V₀ from F.map (c ≫ i) ≫ u) :=
      congrArg (fun z : F.obj A₀ ⟶ F.obj U₀ => z ≫ u) (F.map_comp c i).symm
    _ = (show F.obj A₀ ⟶ V₀ from F.map i₀ ≫ u) :=
      congrArg (fun z : A₀ ⟶ U₀ => F.map z ≫ u) hc

/-- The original dual ideal maps forward into the pulled-back original dual line. -/
def pairIdeal_openDualMap :
    (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val ⟶
      (pullback q).obj (dualLineBundle (pointBlowup X p) (pointIdealLine X p hp)).val :=
  dualMapToPullback q (pointIdealLine X p hp) (centreIdealLine I).val
    (pairIdeal_openIdealMap R I X p j hcentre hp)

/-- The original positive sections satisfy the proved forward coefficient equation. -/
theorem pairIdeal_openDualMap_section :
    InternalHom.transpose (canonicalBlowup I) (idealInclusion (JZ).subschemeι) ≫
        pairIdeal_openDualMap R I X p j hcentre hp =
      (pullbackUnitIso q).inv ≫
        (pullback q).map
          (InternalHom.transpose (pointBlowup X p) (idealInclusion (pointExceptionalι X p))) :=
  transpose_dualMapToPullback q (pointIdealLine X p hp) (centreIdealLine I).val
    (pairIdeal_openIdealMap R I X p j hcentre hp)
    (idealInclusion (pointExceptionalι X p)) (idealInclusion (JZ).subschemeι)
    (pairIdeal_openIdealMap_inclusion R I X p j hcentre hp)

end OpenCentre

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
