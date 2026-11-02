/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.RelativeSection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.RootsHigherSection
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsField
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldConservative
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Bounded
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod

/-! # The degree-two root image of a pointed smooth proper curve family

The positive section bundle defines one original Kummer class and hence an
actual constant-cyclic sheaf map. Its field pullbacks are the existing positive
point classes. Original proper exchange and trace normalization prove the map
invertible, without choosing a Picard representative or a component model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

open OverField.Curve.PointDivisor

section SeparatedFamily

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The Kummer class of the actual positive section bundle. -/
def positiveSectionRootClass : Sheaf.H.{w} (mu X n) 2 :=
  Kummer.picardBoundary X n hn hinv (classOf X (positiveSectionLineBundle p o ho))

/-- Its original higher-image section. -/
def positiveSectionHigherSection : (globalSections S).obj
    ((higherDirectImage p 2).obj (mu X n)) :=
  cohomologyToHigherSections p (mu X n) 2 (positiveSectionRootClass p o ho n hn hinv)

/-- Original coefficient annihilation kills this same section. -/
theorem positiveSectionHigherSection_killed :
    n • positiveSectionHigherSection p o ho n hn hinv = 0 := by
  rw [positiveSectionHigherSection, ← map_nsmul]
  rw [Ext.nsmul_eq_zero_of_nsmul_id_right n (mu_killedBy X n), map_zero]

/-- The actual constant-cyclic map specified by the positive section class. -/
def positiveSectionDegreeTwoMap : ConstantFinite.coefficient (ULift.{u} (ZMod n)) S ⟶
    (higherDirectImage p 2).obj (mu X n) :=
  cyclicSectionMap _ n (positiveSectionHigherSection p o ho n hn hinv)
    (positiveSectionHigherSection_killed p o ho n hn hinv)

omit [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- Bounded proper base change applies to the original root coefficient. -/
theorem rootsHigherImagePullbackMap_isIso [IsProper p]
    {T : Scheme.{u}} (t : T ⟶ S) (q : ℕ) :
    IsIso (rootsHigherImagePullbackMap p n hn hinv t q) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (pullback p t))
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} T)
  have hi : IsIso ((higherBaseChangeMap p (pullback.snd p t) t (pullback.fst p t)
      (IsPullback.of_hasPullback p t).w.symm q).app (mu X n)) := by
    simpa only [higherBaseChangeMapFromDerived_eq] using
      (Proper.properHigherBaseChange_isIso_of_killed p (pullback.snd p t) t
        (pullback.fst p t) (IsPullback.of_hasPullback p t) n (Nat.ne_of_gt hn)
        (mu X n) (mu_killedBy X n) q)
  let := hi
  unfold rootsHigherImagePullbackMap
  infer_instance

/-- The transported cyclic map sends its positive generator to the SAME
field point class. Both original cohomology worlds are retained. -/
theorem positiveSectionDegreeTwoMap_field_adjoint_one
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S)
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p t))]
    (hY : OverField.Curve.Properties (Over.mk (pullback.snd p t))) :
    (constantAdjunction (Spec (.of k))).homEquiv _ _
      (((inverseImageConstantIso t).app (ConstantFinite.value (ULift.{u} (ZMod n)))).inv ≫
        (inverseImage t).map (positiveSectionDegreeTwoMap p o ho n hn hinv) ≫
          rootsHigherImagePullbackMap p n hn hinv t 2)
      (ULift.up (ULift.up (1 : ZMod n))) =
    cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) 2
      (Kummer.picardBoundary.{u, w'} (pullback p t) n hn
        (levelInvertible (pullback.fst p t) n hinv)
        (classOf _ (positiveLineBundle (Over.mk (pullback.snd p t)) hY
          (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho]))
          (Hom.graph_snd p t _ _)))) := by
  have hraw := rootsHigherSectionMap_pullback_adjoint_one.{u, w, w'}
    p n hn hinv t 2 (positiveSectionRootClass p o ho n hn hinv)
  change _ = cohomologyToHigherSections.{u, w'} (pullback.snd p t)
    (mu (pullback p t) n) 2 _
  refine hraw.trans (congrArg
    (cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) 2) ?_)
  exact (Kummer.picardBoundary_pullback.{u, w, w'} (pullback.fst p t) n hn hinv
    (classOf X (positiveSectionLineBundle p o ho))).trans
      (congrArg (Kummer.picardBoundary.{u, w'} (pullback p t) n hn
        (levelInvertible (pullback.fst p t) n hinv))
        (positiveSectionClass_fieldFibre p o ho t hY))

private theorem cyclicValue_bijective_of_trace_one
    (n : ℕ) {M : Type (u + 1)} [AddCommGroup M]
    (e : M ≃+ ZMod n)
    (a : ULift.{u + 1} (ULift.{u} (ZMod n)) →+ M)
    (h : e (a (ULift.up (ULift.up (1 : ZMod n)))) = 1) : Function.Bijective a := by
  have he (x : ULift.{u + 1} (ULift.{u} (ZMod n))) : e (a x) = x.down.down := by
    rcases x with ⟨⟨x⟩⟩
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    have hz : (ULift.up (ULift.up (z : ZMod n)) : ULift.{u + 1} (ULift.{u} (ZMod n))) =
        z • ULift.up (ULift.up (1 : ZMod n)) := by
      apply ULift.ext
      apply ULift.ext
      simp
    rw [hz, map_zsmul, map_zsmul, h]
    simp
  constructor
  · intro x y hxy
    apply ULift.ext
    apply ULift.ext
    rw [← he x, ← he y, hxy]
  · intro z
    refine ⟨ULift.up (ULift.up (e z)), e.injective ?_⟩
    exact he _

private theorem field_cyclicMap_isIso_of_trace_one
    (k : Type u) [Field k] [IsSepClosed k] (n : ℕ) (hn : 0 < n)
    {F : AbelianSheaf.{u, u + 1} (Spec (.of k))}
    (a : ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of k)) ⟶ F)
    (e : (globalSections (Spec (.of k))).obj F ≃+ ZMod n)
    (h : e ((constantAdjunction (Spec (.of k))).homEquiv _ _ a
      (ULift.up (ULift.up (1 : ZMod n)))) = 1) : IsIso a := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hb := cyclicValue_bijective_of_trace_one n e
    (((constantAdjunction (Spec (.of k))).homEquiv _ _ a).hom) h
  have hi := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hu : IsIso ((constantAdjunction (Spec (.of k))).unit.app
      (ConstantFinite.value (ULift.{u} (ZMod n)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective (Spec (.of k)) (ULift.{u} (ZMod n)))
  let := hu
  have hm : IsIso ((globalSections (Spec (.of k))).map a) := by
    change IsIso ((constantAdjunction (Spec (.of k))).unit.app _ ≫
      (globalSections (Spec (.of k))).map a) at hi
    exact (isIso_comp_left_iff _ _).mp hi
  let := hm
  exact isIso_of_field_globalSections k a

end SeparatedFamily

-- Properness supplies separatedness for the remaining endpoints.
variable {X S : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The section cycle gives a genuine constant trivialization of the original
second root image for every smooth proper geometrically connected pointed family. -/
theorem positiveSectionDegreeTwoMap_isIso [IsProper p] [GeometricallyConnected p]
    (hbase : IsUnit (n : Γ(S, ⊤))) :
    IsIso (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S)
  intro k _ _ t _
  let hExt : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pullback p t)) :=
    HasExt.standard _
  let hExtOver : HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd p t)).left) := hExt
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd p t) :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback p t) inferInstance
  have hproper : IsProper (pullback.snd p t) := inferInstance
  have hconnected : GeometricallyConnected (pullback.snd p t) := inferInstance
  have hY : OverField.Curve.Properties (Over.mk (pullback.snd p t)) :=
    ⟨hsm, hproper, hconnected⟩
  let eH := AddEquiv.ofBijective
    (cohomologyToHigherSections.{u, u + 2} (pullback.snd p t) (mu (pullback p t) n) 2)
    (cohomologyToHigherSections_bijective_of_isSepClosed.{u, u + 2}
      k (pullback.snd p t) (mu (pullback p t) n) 2)
  have hk : IsUnit (n : k) := by
    simpa only [map_natCast] using
      (levelInvertible t n hbase).map (Scheme.ΓSpecIso (.of k)).hom.hom
  let E := eH.symm.trans (Curves.traceAddEquiv.{u, u + 2} hY n hn hk
    (levelInvertible (pullback.fst p t) n hinv))
  let a := ((inverseImageConstantIso t).app
      (ConstantFinite.value (ULift.{u} (ZMod n)))).inv ≫
    (inverseImage t).map (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv) ≫
      rootsHigherImagePullbackMap p n hn hinv t 2
  have ha : IsIso a := by
    apply field_cyclicMap_isIso_of_trace_one k n hn a E
    rw [positiveSectionDegreeTwoMap_field_adjoint_one.{u, w, u + 2} p o ho n hn hinv t hY]
    change Curves.traceAddEquiv.{u, u + 2} hY n hn hk _ (eH.symm (eH _)) = 1
    rw [eH.symm_apply_apply]
    exact Curves.traceAddEquiv_picardBoundary_positiveLineBundle.{u, u + 2} hY n hn hk _ _ _
  have hb := rootsHigherImagePullbackMap_isIso p n hn hinv t 2
  let := hb
  have ht : IsIso ((inverseImage t).map (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv)) := by
    have hleft := (isIso_comp_left_iff
      (((inverseImageConstantIso t).app (ConstantFinite.value (ULift.{u} (ZMod n)))).inv)
      _).mp ha
    exact (isIso_comp_right_iff _ _).mp hleft
  let := ht
  have hh : IsIso ((pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.map
      ((inverseImage t).map (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv))) := by
    infer_instance
  have hh' := (NatIso.isIso_map_iff
    (StalkInverseImage.stalkUnitNatIso t (𝟙 (Spec (.of k)))))
      (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv)
  exact (congrArg (fun ξ : Spec (.of k) ⟶ S =>
    IsIso ((pointSmallEtale ξ).sheafFiber.map
      (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv))) (Category.id_comp t)).mp
        (hh'.mpr hh)

include o ho hn hinv in
/-- Constructibility follows from the actual finite constant source and cycle isomorphism. -/
theorem isConstructible_rootsHigherDirectImage_two_pointedCurve
    [IsProper p] [GeometricallyConnected p] (hbase : IsUnit (n : Γ(S, ⊤))) :
    Constructible.IsConstructible ((higherDirectImage p 2).obj (mu X n)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : IsIso (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv) :=
    positiveSectionDegreeTwoMap_isIso.{u, w} p o ho n hn hinv hbase
  exact (Constructible.isConstructible_iff_of_iso
    (asIso (positiveSectionDegreeTwoMap.{u, w} p o ho n hn hinv))).mp
      (Constructible.isConstructible_constant S (ConstantFinite.value (ULift.{u} (ZMod n))))

end AlgebraicGeometry.Scheme.EtaleCohomology
