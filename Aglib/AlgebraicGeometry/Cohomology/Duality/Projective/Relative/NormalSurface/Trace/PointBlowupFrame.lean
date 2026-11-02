/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.PointBlowupGeneration
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.AffineEvaluation
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.StalkGorenstein
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.GenericPoint

/-!
# Conditional original canonical frame on the localized point blowup

The native finite self-injective dimension of the original parent stalk gives
its own canonical frame. The local-spectrum coefficient comparison, original
pullback unit and actual Cartesian square turn the original inverse-trace
adjoint into one literal map from the unit sheaf. Generation of the SAME full
exceptional restriction makes this map epi. Full support of the original
global canonical coefficient and the native pullback-stalk comparison then
make this SAME map an isomorphism.

This is conditional on exceptional generation. No canonical object on an
arbitrary local model, finite later stalk over the original base, new generic
frame, exceptional inverse-line identification, or cone is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Modules.standardHasDerivedCategory restrictionModuleDerived

/-- Finite self-injective dimension at the original point frames the pullback
of the same global canonical coefficient to its local spectrum. -/
def normalSurfaceCanonicalLocalSpectrumIsoOfSelfInjectiveDimension
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {P : Scheme.{u}} [IsIntegral P]
    (j : P ⟶ ProjectiveSpace R ι) [IsClosedImmersion j]
    [IsDominant (j ≫ toSpec R ι)]
    (hP : NormalStalks P) (hdP : topologicalKrullDim P ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι j).Finite)
    (x : P) (d : ℕ)
    [HasInjectiveDimensionLE
      (ModuleCat.of (P.presheaf.stalk x) (P.presheaf.stalk x)) d] :
    (Modules.pullback (P.fromSpecStalk x)).obj (normalSurfaceCanonicalModule R ι j n) ≅
      SheafOfModules.unit (Spec (P.presheaf.stalk x)).ringCatSheaf := by
  let W := normalSurfaceCanonicalModule R ι j n
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι j n e (n : ℤ)
  let : W.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType
    (affineLocallyFiniteType_of_finitePresentation W)
  let E := normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension
    R ι j hP hdP n e hfin x d
  exact (canonicalLocalSpectrumCoefficientIso P x W).symm ≪≫
    (tilde.functor (P.presheaf.stalk x)).mapIso E.toModuleIso ≪≫ tildeSelf

/-- The actual localized global canonical coefficient has nonzero stalk at
every original local-blowup point. The original global support is transported
through the native scalar-extension unit and geometric pullback-stalk iso. -/
theorem localizedCanonical_mem_support
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (P : Scheme.{u}) [IsIntegral P] (x : P) (hx : IsClosed ({x} : Set P))
    [IsIntegral (pointBlowup P x)]
    (hdS : ringKrullDim (P.presheaf.stalk x) = 2)
    (ι : Type u) (j : pointBlowup P x ⟶ ProjectiveSpace R ι)
    [IsClosedImmersion j] [IsDominant (j ≫ toSpec R ι)]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι j).Finite)
    (t : source (P.presheaf.stalk x) hdS) :
    t ∈ support ((Modules.pullback (stalkBlowupComparison P x hx)).obj
      (normalSurfaceCanonicalModule R ι j n)) := by
  let B := source (P.presheaf.stalk x) hdS
  let Z := pointBlowup P x
  let a : B ⟶ Z := stalkBlowupComparison P x hx
  let W := normalSurfaceCanonicalModule R ι j n
  let : IsIso (a.stalkMap t) := localizedCanonical_stalkMap_isIso P x hx t
  let φ := (a.stalkMap t).hom
  let eR := (asIso (a.stalkMap t)).commRingCatIsoToRingEquiv
  let : (ModuleCat.restrictScalars φ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eR
  let N := (moduleStalk B t).obj ((Modules.pullback a).obj W)
  let E : (moduleStalk Z (a t)).obj W ≅ (ModuleCat.restrictScalars φ).obj N :=
    asIso ((ModuleCat.extendRestrictScalarsAdj φ).unit.app
      ((moduleStalk Z (a t)).obj W)) ≪≫
    (ModuleCat.restrictScalars φ).mapIso ((pullbackModuleStalkIso a t).app W).symm
  have hW : a t ∈ support W := by
    rw [normalSurfaceCanonicalModule_support R ι j n e hfin]
    trivial
  intro ht
  let : Subsingleton N := AddCommGrpCat.subsingleton_of_isZero ht
  let : Subsingleton ((ModuleCat.restrictScalars φ).obj N) :=
    inferInstanceAs (Subsingleton N)
  exact hW (AddCommGrpCat.isZero_iff_subsingleton.mpr E.toLinearEquiv.injective.subsingleton)

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (P : Scheme.{u}) [IsIntegral P] [IsLocallyNoetherian P]
  (x : P) (hx : IsClosed ({x} : Set P))
  [IsIntegral (pointBlowup P x)]
  (ιP ιZ : Type u)
  (jP : P ⟶ ProjectiveSpace R ιP) [IsClosedImmersion jP]
  [IsDominant (jP ≫ toSpec R ιP)]
  (jZ : pointBlowup P x ⟶ ProjectiveSpace R ιZ) [IsClosedImmersion jZ]
  [IsDominant (jZ ≫ toSpec R ιZ)]
  (hb : jZ ≫ toSpec R ιZ = pointBlowdown P x ≫ (jP ≫ toSpec R ιP))
  (hP : NormalStalks P) (hdP : topologicalKrullDim P ≤ 2)
  (hZ : NormalStalks (pointBlowup P x))
  (hdZ : topologicalKrullDim (pointBlowup P x) ≤ 2)
  (nP nZ : ℕ) (eP : ιP ≃ Fin (nP + 1)) (eZ : ιZ ≃ Fin (nZ + 1))
  (hfinP : (genericImageBaseMap R ιP jP).Finite)
  (hfinZ : (genericImageBaseMap R ιZ jZ).Finite)
  (hdR : ringKrullDim R = 2)
  (hdS : ringKrullDim (P.presheaf.stalk x) = 2)
  (hNagata : IsNagataRing.{u, 0} (P.presheaf.stalk x))
  (hRat : RationalSingularities.NormalModificationH1Vanishing (P.presheaf.stalk x))
  [Algebra R (P.residueField x)]
  (hres : P.fromSpecResidueField x ≫ (jP ≫ toSpec R ιP) =
    Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x))))
  (d : ℕ) [HasInjectiveDimensionLE
    (ModuleCat.of (P.presheaf.stalk x) (P.presheaf.stalk x)) d]

/-- The literal original inverse-trace adjoint, preceded by the frame of the
original parent stalk, the native unit comparison, and the actual square iso. -/
def normalSurfacePointBlowupFramedCanonicalPullback :
    SheafOfModules.unit (source (P.presheaf.stalk x) hdS).ringCatSheaf ⟶
      (Modules.pullback (stalkBlowupComparison P x hx)).obj
        (normalSurfaceCanonicalModule R ιZ jZ nZ) := by
  let : IsProper (pointBlowdown P x) :=
    (pointBlowupDatum P x).isProper_of_isLocallyNoetherian
  let : IsIso (moduleDerivedPushforwardUnit P (pointBlowdown P x)) :=
    RationalSingularities.isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
      P hP x hx (pointBlowupDatum P x) hNagata hdS hRat hdZ
  let : IsIso (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
    jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ) :=
    normalSurfaceProperCanonicalTrace_isIso_of_structureUnit R ιP ιZ
      (pointBlowdown P x) jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
  let a : source (P.presheaf.stalk x) hdS ⟶ pointBlowup P x :=
    stalkBlowupComparison P x hx
  let p := map (P.presheaf.stalk x) hdS
  let eS := normalSurfaceCanonicalLocalSpectrumIsoOfSelfInjectiveDimension
    R ιP jP hP hdP nP eP hfinP x d
  let σ := ordinaryTracePullbackSquareIso a p (pointBlowdown P x)
    (P.fromSpecStalk x) (stalkBlowupComparison_isPullback P x hx)
  exact (pullbackUnitIso p).inv ≫ (Modules.pullback p).map eS.inv ≫
    σ.inv.app (normalSurfaceCanonicalModule R ιP jP nP) ≫
    (Modules.pullback a).map (ordinaryTracePullback (pointBlowdown P x)
      (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
        jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ))

include hdR hres in
/-- CONDITIONAL: the original full exceptional generation premise makes the
same framed original inverse-trace adjoint epi. -/
theorem normalSurfacePointBlowupFramedCanonicalPullback_epi_of_exceptional_generation
    (hgen : Epi (globalSectionsEval
      ((Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
        ((Modules.pullback (stalkBlowupComparison P x hx)).obj
          (normalSurfaceCanonicalModule R ιZ jZ nZ))))) :
    Epi (normalSurfacePointBlowupFramedCanonicalPullback R P x hx ιP ιZ jP jZ hb
      hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ hdS hNagata hRat d) := by
  let : IsProper (pointBlowdown P x) :=
    (pointBlowupDatum P x).isProper_of_isLocallyNoetherian
  let : IsIso (moduleDerivedPushforwardUnit P (pointBlowdown P x)) :=
    RationalSingularities.isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
      P hP x hx (pointBlowupDatum P x) hNagata hdS hRat hdZ
  let : IsIso (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
    jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ) :=
    normalSurfaceProperCanonicalTrace_isIso_of_structureUnit R ιP ιZ
      (pointBlowdown P x) jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
  let : Epi (ordinaryTracePullback (pointBlowdown P x)
      (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
        jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ)) :=
    normalSurfacePointBlowupCanonicalPullback_epi_of_exceptional_generation
      R P x hx ιP ιZ jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
      hdR hdS hNagata hRat hres hgen
  let a : source (P.presheaf.stalk x) hdS ⟶ pointBlowup P x :=
    stalkBlowupComparison P x hx
  let p := map (P.presheaf.stalk x) hdS
  let eS := normalSurfaceCanonicalLocalSpectrumIsoOfSelfInjectiveDimension
    R ιP jP hP hdP nP eP hfinP x d
  let σ := ordinaryTracePullbackSquareIso a p (pointBlowdown P x)
    (P.fromSpecStalk x) (stalkBlowupComparison_isPullback P x hx)
  let φ := ordinaryTracePullback (pointBlowdown P x)
    (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
      jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ)
  have hφ : Epi ((Modules.pullback a).map φ) := (Modules.pullback a).map_epi φ
  change Epi ((pullbackUnitIso p).inv ≫ ((Modules.pullback p).mapIso eS).inv ≫
    (σ.app (normalSurfaceCanonicalModule R ιP jP nP)).inv ≫ (Modules.pullback a).map φ)
  exact epi_comp'
    (@IsIso.epi_of_iso _ _ _ _ (pullbackUnitIso p).inv (Iso.isIso_inv (pullbackUnitIso p)))
    (epi_comp' (inferInstanceAs (Epi ((Modules.pullback p).mapIso eS).inv))
      (epi_comp' (inferInstanceAs
        (Epi (σ.app (normalSurfaceCanonicalModule R ιP jP nP)).inv)) hφ))

include hdR hres in
/-- CONDITIONAL: the same original unit-module map is an isomorphism, by its
epimorphy and the full support of the actual pulled-back canonical coefficient. -/
theorem normalSurfacePointBlowupFramedCanonicalPullback_isIso_of_exceptional_generation
    (hgen : Epi (globalSectionsEval
      ((Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
        ((Modules.pullback (stalkBlowupComparison P x hx)).obj
          (normalSurfaceCanonicalModule R ιZ jZ nZ))))) :
    IsIso (normalSurfacePointBlowupFramedCanonicalPullback R P x hx ιP ιZ jP jZ hb
      hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ hdS hNagata hRat d) := by
  let B := source (P.presheaf.stalk x) hdS
  let : IsIntegral B := source_isIntegral _ hdS
  let φ := normalSurfacePointBlowupFramedCanonicalPullback R P x hx ιP ιZ jP jZ hb
    hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ hdS hNagata hRat d
  let : Epi φ :=
    normalSurfacePointBlowupFramedCanonicalPullback_epi_of_exceptional_generation
      R P x hx ιP ιZ jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
      hdR hdS hNagata hRat hres d hgen
  exact isIso_unitHom_of_epi_of_generic_mem_support φ
    (localizedCanonical_mem_support R P x hx hdS ιZ jZ nZ eZ hfinZ (genericPoint B))

include hdR hres in
/-- The conditional frame is the inverse of the SAME framed original
inverse-trace adjoint, not an independently selected local frame. -/
def normalSurfacePointBlowupCanonicalIsoOfExceptionalGeneration
    (hgen : Epi (globalSectionsEval
      ((Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
        ((Modules.pullback (stalkBlowupComparison P x hx)).obj
          (normalSurfaceCanonicalModule R ιZ jZ nZ))))) :
    (Modules.pullback (stalkBlowupComparison P x hx)).obj
        (normalSurfaceCanonicalModule R ιZ jZ nZ) ≅
      SheafOfModules.unit (source (P.presheaf.stalk x) hdS).ringCatSheaf := by
  let φ := normalSurfacePointBlowupFramedCanonicalPullback R P x hx ιP ιZ jP jZ hb
    hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ hdS hNagata hRat d
  let : IsIso φ :=
    normalSurfacePointBlowupFramedCanonicalPullback_isIso_of_exceptional_generation
      R P x hx ιP ιZ jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
      hdR hdS hNagata hRat hres d hgen
  exact (asIso φ).symm

end AlgebraicGeometry.Scheme.Cohomology
