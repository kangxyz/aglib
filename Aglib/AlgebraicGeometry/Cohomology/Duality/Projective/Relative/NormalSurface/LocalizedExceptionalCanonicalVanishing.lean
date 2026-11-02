/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.ExceptionalCoefficientVanishing
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CartierRestriction
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Original canonical coefficients on a localized point blowup

The coefficient is pulled back from the original global canonical module.
Residue finiteness comes from the original proper model, not from finiteness
of the later local ring over the original base. All stalk comparisons retain
the native scalar-extension unit and geometric pullback-stalk isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] restrictionModuleDerived

/-- A closed residue of the original proper model is finite over the original
base through the supplied, unchanged structural triangle. -/
theorem localizedCanonical_residue_finite
    (R : Type u) [CommRing R] (P : Scheme.{u})
    (f : P ⟶ Spec (.of R)) [IsProper f] (x : P)
    (hx : IsClosed ({x} : Set P))
    [Algebra R (P.residueField x)]
    (hbase : P.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x)))) :
    Module.Finite R (P.residueField x) := by
  let : IsClosedImmersion (P.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hp : IsProper (Spec.map (CommRingCat.ofHom
      (algebraMap R (P.residueField x)))) := by
    rw [← hbase]
    infer_instance
  let : IsProper (Spec.map (CommRingCat.ofHom
      (algebraMap R (P.residueField x)))) := hp
  have hf : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R (P.residueField x)))) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)

/-- The original finite residue algebra over a local base has the original
local algebra map; no alternative residue scalar action is chosen. -/
theorem localizedCanonical_residue_isLocalHom
    (R k : Type u) [CommRing R] [IsLocalRing R] [Field k]
    [Algebra R k] [Module.Finite R k] : IsLocalHom (algebraMap R k) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap R k)).out 1 5).mpr
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact IsLocalRing.eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)

private theorem pullback_stalk_regular_of_stalkMap_isIso
    {Y X : Scheme.{u}} (a : Y ⟶ X) (M : X.Modules) (y : Y)
    (ha : IsIso (a.stalkMap y))
    (hM : ∀ r : X.presheaf.stalk (a y), r ≠ 0 →
      IsSMulRegular ((moduleStalk X (a y)).obj M) r)
    (b : Y.presheaf.stalk y) (hb : b ≠ 0) :
    IsSMulRegular ((moduleStalk Y y).obj ((Modules.pullback a).obj M)) b := by
  let : IsIso (a.stalkMap y) := ha
  let φ := (a.stalkMap y).hom
  let eR := (asIso (a.stalkMap y)).commRingCatIsoToRingEquiv
  let : (ModuleCat.restrictScalars φ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eR
  let N := (moduleStalk Y y).obj ((Modules.pullback a).obj M)
  let e : (moduleStalk X (a y)).obj M ≅ (ModuleCat.restrictScalars φ).obj N :=
    asIso ((ModuleCat.extendRestrictScalarsAdj φ).unit.app
      ((moduleStalk X (a y)).obj M)) ≪≫
    (ModuleCat.restrictScalars φ).mapIso ((pullbackModuleStalkIso a y).app M).symm
  have hr : eR.symm b ≠ 0 := by
    intro h
    apply hb
    have := congrArg eR h
    simpa only [RingEquiv.apply_symm_apply, map_zero] using this
  have hreg := (e.toLinearEquiv.isSMulRegular_congr (eR.symm b)).mp (hM _ hr)
  change Function.Injective (fun m => b • m)
  change Function.Injective (fun m => φ (eR.symm b) • m) at hreg
  intro m₁ m₂ h
  apply hreg
  change φ (eR.symm b) • m₁ = φ (eR.symm b) • m₂
  simpa only [show φ (eR.symm b) = b from eR.apply_symm_apply b] using h

open Blowup Blowup.RegularPoint
open RationalSingularities.MaximalIdealBlowup

/-- The original local-spectrum blowup comparison preserves each actual local ring. -/
theorem localizedCanonical_stalkMap_isIso (P : Scheme.{u}) (x : P)
    (hx : IsClosed ({x} : Set P))
    (t : (blowupDatum (affineCenter (P.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (P.presheaf.stalk x)))).Y) :
    IsIso ((stalkBlowupComparison P x hx).stalkMap t) := by
  let : IsPreimmersion (stalkBlowupComparison P x hx) :=
    MorphismProperty.of_isPullback (stalkBlowupComparison_isPullback P x hx).flip
      (inferInstanceAs (IsPreimmersion (P.fromSpecStalk x)))
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ t

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (P : Scheme.{u}) (x : P) (hx : IsClosed ({x} : Set P))
  (hdS : ringKrullDim (P.presheaf.stalk x) = 2)
  [IsIntegral P]
  [IsIntegral (pointBlowup P x)]
  (ι : Type u) (j : pointBlowup P x ⟶ ProjectiveSpace R ι)
  [IsClosedImmersion j] [IsDominant (j ≫ toSpec R ι)]
  (hZ : NormalStalks (pointBlowup P x))
  (hdZ : topologicalKrullDim (pointBlowup P x) ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι j).Finite)

include hZ hdZ e hfin in
omit [IsIntegral P] in
/-- Nonzero local scalars act regularly on the actual pullback of the original
canonical module, through its original geometric stalk comparison. -/
theorem localizedCanonical_stalk_regular
    (t : source (P.presheaf.stalk x) hdS)
    (b : (source (P.presheaf.stalk x) hdS).presheaf.stalk t) (hb : b ≠ 0) :
    IsSMulRegular ((moduleStalk (source (P.presheaf.stalk x) hdS) t).obj
      ((Modules.pullback (stalkBlowupComparison P x hx)).obj
        (normalSurfaceCanonicalModule R ι j n))) b := by
  exact pullback_stalk_regular_of_stalkMap_isIso
    (Y := source (P.presheaf.stalk x) hdS) (X := pointBlowup P x)
    (stalkBlowupComparison P x hx) (normalSurfaceCanonicalModule R ι j n) t
    (localizedCanonical_stalkMap_isIso P x hx t)
    (normalSurfaceCanonical_stalk_regular R ι j hZ hdZ n e hfin _) b hb

include hZ hdZ e hfin in
/-- The local Cartier section is monic for the actual localized global canonical
coefficient; no comparison of independently chosen canonical modules is used. -/
theorem localizedCanonical_cartierSection_mono :
    Mono ((cartierTensorSection (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).app
      ((Modules.pullback (stalkBlowupComparison P x hx)).obj
        (normalSurfaceCanonicalModule R ι j n))) := by
  let : IsIntegral (source (P.presheaf.stalk x) hdS) := source_isIntegral _ hdS
  exact Modules.cartierTensorSection_mono_of_stalk_regular
    (X := source (P.presheaf.stalk x) hdS)
    (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)
    (datum (P.presheaf.stalk x)).cartier _
    (localizedCanonical_stalk_regular R P x hx hdS ι j hZ hdZ n e hfin)

include hZ hdZ e hfin in
/-- The original global canonical restriction, pulled back along the original
local-spectrum blowup comparison, has the actual positive exceptional twist. -/
def localizedExceptionalCanonicalRestrictionIso
    [IsNoetherianRing (P.presheaf.stalk x)] [IsIntegrallyClosed (P.presheaf.stalk x)]
    (hdR : ringKrullDim R = 2)
    (hNagata : IsNagataRing.{u, 0} (P.presheaf.stalk x))
    (hRat : RationalSingularities.NormalModificationH1Vanishing (P.presheaf.stalk x))
    (f : P ⟶ Spec (.of R)) [IsProper f]
    [Algebra R (P.residueField x)]
    (hf : j ≫ toSpec R ι = pointBlowdown P x ≫ f)
    (hres : P.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x))))
    (ιE : Type u)
    (jE : exceptionalCurve (P.presheaf.stalk x) hdS ⟶
      ProjectiveSpace (P.residueField x) ιE) [IsClosedImmersion jE]
    (m : ℕ) (eE : ιE ≃ Fin (m + 1)) (hm : 1 ≤ m)
    (hjE : jE ≫ toSpec (P.residueField x) ιE =
      RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap
        (P.presheaf.stalk x) hdS) :
    (Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
      ((Modules.pullback (stalkBlowupComparison P x hx)).obj
        (normalSurfaceCanonicalModule R ι j n)) ≅
    cmCurveCoefficientCanonicalModule (P.residueField x) ιE jE m
      (ModuleCat.derivedResidueCoefficientLine R (P.residueField x)) ⊗
        (exceptionalLine (P.presheaf.stalk x) hdS).val := by
  let S := P.presheaf.stalk x
  let a : source S hdS ⟶ pointBlowup P x := stalkBlowupComparison P x hx
  let i := exceptionalCurveInclusion S hdS
  let g := i ≫ a
  let eg := stalkCentreFibreIso P x hx
  have heg : eg.hom ≫ pointExceptionalι P x = g := stalkCentreFibreIso_hom_ι P x hx
  let : IsClosedImmersion (pointExceptionalι P x) := pointExceptionalι_isClosedImmersion P x hx
  let : IsIso eg.hom := inferInstance
  have hcomp : IsClosedImmersion (eg.hom ≫ pointExceptionalι P x) := inferInstance
  let : IsClosedImmersion g := heg ▸ hcomp
  let eI := identityBaseIdealIso (pointExceptionalι P x) g eg heg
  have hI : IsLocallyRankOne (pointBlowup P x) (idealModule g) :=
    isLocallyRankOne_of_iso _ eI (pointIdealLine P x hx).property
  let : Module.Finite R (P.residueField x) := localizedCanonical_residue_finite R P f x hx hres
  let : IsLocalHom (algebraMap R (P.residueField x)) :=
    localizedCanonical_residue_isLocalHom R (P.residueField x)
  have hs := (stalkBlowupComparison_isPullback P x hx).w
  change a ≫ pointBlowdown P x =
    RationalSingularities.MaximalIdealBlowup.map S hdS ≫ P.fromSpecStalk x at hs
  have htriangle :
      RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap S hdS ≫
        P.fromSpecResidueField x = g ≫ pointBlowdown P x := by
    calc
      _ = RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap S hdS ≫
          (residueSpectrumInclusion S ≫ P.fromSpecStalk x) := by
        exact congrArg (fun k =>
          RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap S hdS ≫ k)
            (pointResidueFactor P x).symm
      _ = (i ≫ RationalSingularities.MaximalIdealBlowup.map S hdS) ≫
          P.fromSpecStalk x := by
        rw [← Category.assoc, exceptionalStructureMap_triangle]
      _ = _ :=
        (Category.assoc i _ _).trans
          ((congrArg (fun k => i ≫ k) hs.symm).trans (Category.assoc i a _).symm)
  have hbase : (jE ≫ toSpec (P.residueField x) ιE) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x))) =
        g ≫ (j ≫ toSpec R ι) := by
    calc
      _ = (RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap S hdS ≫
          P.fromSpecResidueField x) ≫ f := by
        exact (congrArg (fun k => k ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x)))) hjE).trans
            ((congrArg (fun k =>
              RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap S hdS ≫ k)
                hres.symm).trans (Category.assoc _ _ f).symm)
      _ = (g ≫ pointBlowdown P x) ≫ f := congrArg (fun k => k ≫ f) htriangle
      _ = _ := by rw [Category.assoc, ← hf]
  have hdim : ∀ z : exceptionalCurve S hdS, IsClosed ({z} : Set _) →
      ringKrullDim ((pointBlowup P x).presheaf.stalk (g z)) = 2 := by
    intro z hz
    let : IsIso (a.stalkMap (i z)) := localizedCanonical_stalkMap_isIso P x hx (i z)
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (a.stalkMap (i z))).commRingCatIsoToRingEquiv).trans
        (exceptionalCurve_closedPoint_stalk_dimension S hdS hNagata hRat z hz)
  let eC := normalSurfaceCartierRestrictionIso R (P.residueField x) hdR ι ιE j
    hZ hdZ n e hfin g hI jE m eE hm hbase hdim
  let eL : (Modules.pullback g).obj (idealModule g) ≅ (exceptionalLine S hdS).val :=
    (Modules.pullback g).mapIso eI.symm ≪≫
      (pullbackComp i a).symm.app (idealModule (pointExceptionalι P x)) ≪≫
        (Modules.pullback i).mapIso (stalkPointIdealIso P x hx)
  exact (pullbackComp i a).app (normalSurfaceCanonicalModule R ι j n) ≪≫ eC ≪≫
    tensorSheafIso _ (Iso.refl _) eL

local notation "κₓ" => P.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (P.presheaf.stalk x)

include hZ hdZ e hfin in
/-- Genuine normal proper global geometry supplies both ideal-power H1 vanishing
and lifting through the literal local exceptional restriction unit for the
pullback of the ORIGINAL global canonical module. -/
theorem localizedExceptionalCanonicalVanishing
    [IsLocallyNoetherian P] (hP : NormalStalks P)
    (hdR : ringKrullDim R = 2)
    (hNagata : IsNagataRing.{u, 0} (P.presheaf.stalk x))
    (hRat : RationalSingularities.NormalModificationH1Vanishing (P.presheaf.stalk x))
    (f : P ⟶ Spec (.of R)) [IsProper f]
    [Algebra R (P.residueField x)]
    (hf : j ≫ toSpec R ι = pointBlowdown P x ≫ f)
    (hres : P.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (P.residueField x)))) :
    let M := (Modules.pullback (stalkBlowupComparison P x hx)).obj
      (normalSurfaceCanonicalModule R ι j n)
    (∀ q : ℕ, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (source (P.presheaf.stalk x) hdS)
        (ordinaryIdealPower (P.presheaf.stalk x) hdS q ⊗ M)) 1)) ∧
      Function.Surjective
        (((pullbackPushforwardAdjunction
          (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).unit.app M).val.app (op ⊤)) := by
  let S := P.presheaf.stalk x
  let : Field κₓ := Ideal.Quotient.field _
  let : Algebra R κₓ := inferInstanceAs (Algebra R (P.residueField x))
  let : IsIntegrallyClosed S := (hP x).2
  let W := normalSurfaceCanonicalModule R ι j n
  let a : source S hdS ⟶ pointBlowup P x := stalkBlowupComparison P x hx
  let M : (source S hdS).Modules := (Modules.pullback a).obj W
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι j n e (n : ℤ)
  let : M.IsFinitePresentation := Modules.finitePresentation_pullback a W
  let : Module.Finite R κₓ := localizedCanonical_residue_finite R P f x hx hres
  let : IsLocalHom (algebraMap R κₓ) := localizedCanonical_residue_isLocalHom R κₓ
  let V := ModuleCat.derivedResidueCoefficientLine R κₓ
  let : Module.Finite κₓ V := ModuleCat.derivedResidueCoefficientLine_finite R κₓ hdR
  obtain ⟨m, jE, hm, hjE, hstruct, ⟨eL⟩⟩ := exists_exceptionalTautologicalEmbedding S hdS
  let : IsClosedImmersion jE := hjE
  let jE' : exceptionalCurve S hdS ⟶
      ProjectiveSpace (P.residueField x) (ULift.{u} (Fin (m + 1))) := jE
  let : IsClosedImmersion jE' := hjE
  let eM := localizedExceptionalCanonicalRestrictionIso R P x hx hdS ι j hZ hdZ n e hfin
    hdR hNagata hRat f hf hres (ULift.{u} (Fin (m + 1))) jE' m Equiv.ulift hm hstruct
  let : Mono ((cartierTensorSection (exceptionalCurveInclusion S hdS)).app M) :=
    localizedCanonical_cartierSection_mono R P x hx hdS ι j hZ hdZ n e hfin
  exact ⟨fun q => exceptionalCoefficientIdealPower_h1_subsingleton
      S hdS hNagata hRat M (ULift.{u} (Fin (m + 1))) jE m Equiv.ulift hm hstruct eL V
      (ModuleCat.derivedResidueCoefficientLine_finrank R κₓ hdR) eM q,
    exceptionalCoefficientRestriction_sections_surjective
      S hdS hNagata hRat M (ULift.{u} (Fin (m + 1))) jE m Equiv.ulift hm hstruct eL V
      (ModuleCat.derivedResidueCoefficientLine_finrank R κₓ hdR) eM⟩

end AlgebraicGeometry.Scheme.Cohomology
