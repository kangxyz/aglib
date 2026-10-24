/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.KummerFamilyValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperCurveH1Family
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.FiniteCover.Parameters
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-! # Finite values of the actual bounded Kummer charts

A single original chart class takes only finitely many values on the original
curve. The parameter chart is not assumed connected, and no proper base change
premise is used. The actual roots maps are normalized before applying the
fixed-coefficient proper-henselian finite-image theorem.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u
namespace AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [ConnectedSpace X.left]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) {g n : ℕ}

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  [ConnectedSpace X.left] in
/-- Invertibility transported by the original structural constants map. -/
theorem curve_levelInvertible (hunit : IsUnit (n : k)) : IsUnit (n : Γ(X.left, ⊤)) := by
  simpa only [map_natCast] using
    hunit.map (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom)

omit [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
include o in
/-- The literal roots coefficient on the original connected curve is finite
locally constant, using the actual rational geometric point. -/
theorem curve_roots_finiteLocallyConstant (hn : 0 < n) (hunit : IsUnit (n : k)) :
    IsFiniteLocallyConstant (mu X.left n) := by
  let : CategoryTheory.CommGrpObj (Scheme.Group.MultiplicativeGroup.rootsScheme X.left n) :=
    Scheme.Group.MultiplicativeGroup.rootsCommGroup X.left n
  let : IsFinite (Scheme.Group.MultiplicativeGroup.rootsGroupScheme X.left n).X.hom :=
    Scheme.Group.RootsFiniteEtale.rootsScheme_finite X.left n hn
  let : Etale (Scheme.Group.MultiplicativeGroup.rootsGroupScheme X.left n).X.hom :=
    Scheme.Group.RootsFiniteEtale.rootsScheme_etale X.left n hn (curve_levelInvertible X hunit)
  exact representedSheaf_isFiniteLocallyConstant (s := o)
    (Scheme.Group.MultiplicativeGroup.rootsGroupScheme X.left n)

/-- One actual Kummer chart has finitely many original geometric H1 values,
with both original fibre arrows retained. -/
theorem exists_finset_chart_roots_values (C : LocalKummerChart X o ho g n)
    (hn : 0 < n) (hunit : IsUnit (n : k)) :
    ∃ S : Finset (H1Etale.{u, u + 1, u + 2} X.left (mu X.left n)),
      ∀ (b : Spec (.of k) ⟶ C.base) (_hb : b ≫ C.structureMap = 𝟙 _)
        (a : X.left ⟶ C.totalSpace) (_haX : a ≫ C.curveMap = 𝟙 _)
        (_haT : a ≫ C.projection = X.hom ≫ b),
        Kummer.rootsCohomologyPullback a n hn (C.levelInvertible hunit) 1
          C.cohomologyClass ∈ S := by
  let : LocallyOfFiniteType C.structureMap := by
    dsimp only [LocalKummerChart.structureMap]
    infer_instance
  let hinv := curve_levelInvertible X hunit
  let c := coefficientMap (rootsPullbackIso C.curveMap n hn hinv).inv C.cohomologyClass
  obtain ⟨S, hS⟩ := ProperCurveH1Family.exists_finset_sectionPullback_values
    C.isPullback_curveMap (mu X.left n) c (curve_roots_finiteLocallyConstant X o hn hunit)
  refine ⟨S, ?_⟩
  intro b hb a haX haT
  have hv := hS b hb a haX haT
  rw [sectionPullback_roots o C.curveMap a haX n hn hinv] at hv
  exact hv

end AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues
