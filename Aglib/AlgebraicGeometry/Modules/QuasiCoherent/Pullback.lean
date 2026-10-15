/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
/-!
# Arbitrary pullback of actual coherent sheaves

Actual module-sheaf pullback transports local presentations on inverse-image
opens, retaining both generator and relation index types. Hence it preserves
finite presentation without flatness, and coherence on locally noetherian
schemes. Exactness requires flatness and is treated separately.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- A global presentation on the slice site gives the actual presentation
on the corresponding open subscheme. -/
def presentationOverToRestrict (M : Y.Modules) (U : Y.Opens)
    (P : (M.over U).Presentation) : (M.restrict U.ι).Presentation :=
  (P.map (Scheme.Modules.overEquiv U).functor
    (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm).ofIsIso
      ((Scheme.Modules.overFunctorEquiv U).app M).hom

instance presentationOverToRestrict_isFinite (M : Y.Modules) (U : Y.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationOverToRestrict M U P).IsFinite := by
  dsimp [presentationOverToRestrict]
  infer_instance

/-- The actual inverse-image-open presentation is obtained by applying
geometric pullback to the generators and relations, using its right exactness. -/
def presentationPullbackRestrict (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (P : (M.over U).Presentation) :
    (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι).Presentation := by
  have : PreservesColimitsOfSize.{u,u} (Scheme.Modules.pullback (f ∣_ U)) := inferInstance
  exact ((presentationOverToRestrict M U P).map (Scheme.Modules.pullback (f ∣_ U))
    (pullbackUnitIso (f ∣_ U)).symm).ofIsIso
      ((pullbackRestrictIso f U).app M).inv

instance presentationPullbackRestrict_isFinite (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationPullbackRestrict f M U P).IsFinite := by
  dsimp [presentationPullbackRestrict]
  infer_instance

/-- Transport an actual presentation on an open subscheme back to its
slice site, using the geometric equivalence rather than an abstract model. -/
def presentationRestrictToOver (M : Y.Modules) (U : Y.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact (P.map E.inverse
    (U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm).ofIsIso e.hom

instance presentationRestrictToOver_isFinite (M : Y.Modules) (U : Y.Opens)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (presentationRestrictToOver M U P).IsFinite := by
  dsimp [presentationRestrictToOver]
  infer_instance

/-- Pull back the actual local presentations on the inverse-image open cover. -/
def quasicoherentDataPullback (f : X ⟶ Y) (M : Y.Modules)
    (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    SheafOfModules.QuasicoherentData.{u, u, u, u} ((Scheme.Modules.pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := (Opens.coversTop_iff X _).mpr
    (((Opens.coversTop_iff Y q.X).mp q.coversTop).comap f.base.hom)
  presentation i := presentationRestrictToOver _ _
    (presentationPullbackRestrict f M (q.X i) (q.presentation i))

instance quasicoherentDataPullback_isFinitePresentation (f : X ⟶ Y) (M : Y.Modules)
    (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) [q.IsFinitePresentation] :
    (quasicoherentDataPullback f M q).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp [quasicoherentDataPullback]
    infer_instance

/-- Actual geometric pullback preserves quasicoherence on arbitrary schemes. -/
instance quasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  (quasicoherentDataPullback f M
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData.some)).isQuasicoherent

/-- Actual geometric pullback preserves finite local presentation along
arbitrary scheme morphisms. No flatness is used or needed for this statement. -/
instance finitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  exact SheafOfModules.IsFinitePresentation.mk (M := (Scheme.Modules.pullback f).obj M)
    ⟨quasicoherentDataPullback f M q, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules


