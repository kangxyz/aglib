/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OnePointRestriction
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ProperHenselian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.AlgebraicGeometry.Picard.KummerH1

/-!
# Original roots cohomology restriction across one point

The actual one-point Picard torsion restriction is bijective. The original
unit restriction makes every punctured global unit an nth power, since this
holds on the proper curve over algebraically closed constants. Actual Kummer
naturality then proves bijectivity of the original degree-one roots pullback.
No purity or torsion-cardinality formula is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction
open GroupCohomology.Kummer.Coefficients

universe u wX wV

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
  (hV : (V : Set X.left) = {x.val}ᶜ)

include hX hV in
/-- Positive power maps on the actual one-puncture global unit group are
surjective, through the original proper-to-open unit restriction. -/
theorem onePoint_globalUnits_pow_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun a : Γ(V.toScheme, ⊤)ˣ => a ^ n) := by
  have := hX.proper
  have := hX.isGeometricallyIntegral
  have := hX.isIntegral
  have hroot : Function.Surjective (fun a : Γ(X.left, ⊤)ˣ => a ^ n) :=
    Scheme.Modules.Invertible.TrivializedPower.globalUnits_pow_surjective X.left X.hom
      (constants_bijective_of_proper_geometricallyIntegral X).2 n hn
  let r := Units.map V.ι.appTop.hom.toMonoidHom
  have hr : Function.Surjective r := (globalUnits_appTop_bijective hX x V hV).surjective
  intro a
  obtain ⟨b, hb⟩ := hr a
  obtain ⟨c, hc⟩ := hroot b
  refine ⟨r c, ?_⟩
  exact (map_pow r c n).symm.trans ((congrArg r hc).trans hb)

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} X.left)]
  [HasExt.{wV} (AbelianSheaf.{u, u + 1} V.toScheme)]

include hX hV in
/-- The original degree-one roots restriction across one point is bijective.
The actual Kummer/Picard naturality square supplies the map comparison. -/
theorem rootsH1Restriction_bijective_of_onePoint
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Function.Bijective (GroupCohomology.Kummer.CoefficientBaseChange.h1Map V.ι n hn hinv) := by
  have : Nonempty V := nonempty_onePoint_complement hX x V hV
  have : IsProper X.hom := hX.proper
  have : GeometricallyIntegral X.hom := hX.isGeometricallyIntegral
  have : IsIntegral X.left := hX.isIntegral
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  have : IsNoetherian V.toScheme := Curve.isNoetherian_of_isOpenImmersion hX V.ι
  have (y : Scheme.ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk y.val) :=
    Curve.isDiscreteValuationRing_stalk_of_isOpenImmersion hX (𝟙 X.left) y
  have (y : Scheme.ClosedPoint V.toScheme) :
      IsDiscreteValuationRing (V.toScheme.presheaf.stalk y.val) :=
    Curve.isDiscreteValuationRing_stalk_of_isOpenImmersion hX V.ι y
  have hrootX : Function.Surjective (fun a : Γ(X.left, ⊤)ˣ => a ^ n) :=
    Scheme.Modules.Invertible.TrivializedPower.globalUnits_pow_surjective X.left X.hom
      (constants_bijective_of_proper_geometricallyIntegral X).2 n hn
  have hrootV : Function.Surjective (fun a : Γ(V.toScheme, ⊤)ˣ => a ^ n) :=
    onePoint_globalUnits_pow_surjective hX x V hV n hn
  let eX : Sheaf.H.{wX} (mu X.left n) 1 ≃+ Torsion.picardTorsion X.left n :=
    KummerH1.h1PicardTorsionEquiv X.left EtaleDescent.etaleLineBundleDescent
      (stacks03AJ X.left) n hn hinv hrootX
  let eV : Sheaf.H.{wV} (mu V.toScheme n) 1 ≃+ Torsion.picardTorsion V.toScheme n :=
    KummerH1.h1PicardTorsionEquiv V.toScheme EtaleDescent.etaleLineBundleDescent
      (stacks03AJ V.toScheme) n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible V.ι n hinv) hrootV
  let r : Sheaf.H.{wX} (mu X.left n) 1 →+ Sheaf.H.{wV} (mu V.toScheme n) 1 :=
    GroupCohomology.Kummer.CoefficientBaseChange.h1Map V.ι n hn hinv
  have hwhole : eV.toAddMonoidHom.comp r = (torsionPullback V.ι n).comp eX.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    exact KummerH1.h1PicardTorsionEquiv_pullback X.left V.ι
      EtaleDescent.etaleLineBundleDescent (stacks03AJ X.left) (stacks03AJ V.toScheme)
      n hn hinv hrootX hrootV a
  have htor : Function.Bijective (torsionPullback V.ι n) :=
    torsionPullback_bijective hX x V hV n hn
  change Function.Bijective r
  constructor
  · intro a b hab
    apply eX.injective
    apply htor.injective
    have h := congrArg eV hab
    change (eV.toAddMonoidHom.comp r) a = (eV.toAddMonoidHom.comp r) b at h
    rw [hwhole] at h
    exact h
  · intro b
    obtain ⟨a, ha⟩ := htor.surjective (eV b)
    refine ⟨eX.symm a, eV.injective ?_⟩
    have h := DFunLike.congr_fun hwhole (eX.symm a)
    exact h.trans ((congrArg (torsionPullback V.ι n) (eX.apply_symm_apply a)).trans ha)

include hX hV in
/-- Original degree-zero roots restriction is bijective, using the existing
connected constant-section pullback and the actual roots coefficient iso. -/
theorem rootsH0Restriction_bijective_of_onePoint
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Function.Bijective (Kummer.rootsCohomologyPullback V.ι n hn hinv 0) := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  have : Nonempty V := nonempty_onePoint_complement hX x V hV
  have : IsIntegral X.left := hX.isIntegral
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  have : IsNoetherian V.toScheme := Curve.isNoetherian_of_isOpenImmersion hX V.ι
  have : ConnectedSpace X.left := inferInstance
  have : ConnectedSpace V.toScheme := inferInstance
  have : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let A := ConstantFinite.value (ULift.{u} (ZMod n))
  have hA : IsAddTorsion A := _root_.isAddTorsion_of_finite
  have hR : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let e : (constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A ≅ mu X.left n :=
    Kummer.HenselianConstant.constantRootIsoOver k n hn hR X.hom
  have : IsIso (globalSectionsPullback V.ι (mu X.left n)) :=
    globalSectionsPullback_isIso_of_torsionConstantIso V.ι A hA (mu X.left n) e.symm
  have hz : Function.Bijective
      (cohomologyPullback.{u, wX, wV} V.ι (mu X.left n) 0) :=
    ProperHenselianH0.h0Pullback_bijective_of_sections V.ι (mu X.left n)
      (ConcreteCategory.bijective_of_isIso (globalSectionsPullback V.ι (mu X.left n)))
  let eH : AddCommGrpCat.of
      (Sheaf.H.{wV} ((inverseImage V.ι).obj (mu X.left n)) 0) ≅
      AddCommGrpCat.of (Sheaf.H.{wV} (mu V.toScheme n) 0) :=
    (Sheaf.functorH V.toScheme.smallEtaleTopology 0).mapIso
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso V.ι n hn hinv)
  have hc : Function.Bijective
      (Sheaf.H.map (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso
        V.ι n hn hinv).hom 0) :=
    eH.addCommGroupIsoToAddEquiv.bijective
  exact hc.comp hz

include hX hV in
/-- The original roots cohomology pullback is bijective in degrees zero and
one on the one-point complement. -/
theorem rootsCohomologyPullback_bijective_of_onePoint_of_le_one
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (q : ℕ) (hq : q ≤ 1) :
    Function.Bijective (Kummer.rootsCohomologyPullback V.ι n hn hinv q) := by
  rcases q with _ | q
  · exact rootsH0Restriction_bijective_of_onePoint hX x V hV n hn hunit hinv
  · have hq0 : q = 0 := by omega
    subst q
    exact rootsH1Restriction_bijective_of_onePoint hX x V hV n hn hinv

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
