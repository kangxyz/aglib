/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenRestriction
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Picard.Torsion

/-!
# Original Picard restriction across one closed point

A line bundle trivial on the complement of one point has its original
trivialization divisor supported at that point. On a smooth proper curve over
an algebraically closed field, this computes the kernel of the actual Picard
pullback as the multiples of the actual point line bundle. No Picard scheme
representative or cohomological purity theorem is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction

/-- The actual Picard pullback restricted to the existing torsion subgroups. -/
def torsionPullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) (n : ℕ) :
    Torsion.picardTorsion Z n →+ Torsion.picardTorsion Y n where
  toFun a := ⟨PullbackTensor.Local.pullbackHom f a.val, by
    change n • PullbackTensor.Local.pullbackHom f a.val = 0
    have ha : n • a.val = 0 := a.property
    rw [← map_nsmul, ha, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (PullbackTensor.Local.pullbackHom f))
  map_add' a b := Subtype.ext ((PullbackTensor.Local.pullbackHom f).map_add a.val b.val)

/-- The whole torsion restriction retains the original Picard pullback underneath. -/
theorem torsionPullback_subtype {Y Z : Scheme.{u}} (f : Y ⟶ Z) (n : ℕ) :
    (Torsion.picardTorsion Y n).subtype.comp (torsionPullback f n) =
      (PullbackTensor.Local.pullbackHom f).comp (Torsion.picardTorsion Z n).subtype := rfl

section SupportedDivisor

variable (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
  [∀ y : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
  (hdim : topologicalKrullDim Y ≤ 1) (x : Scheme.ClosedPoint Y)
  (V : Y.Opens) [Nonempty V] (hV : (V : Set Y) = {x.val}ᶜ)

include hV

/-- The original trivialization on a one-point complement gives an actual
divisor supported at that point, on the same original line bundle. -/
theorem exists_eq_divisorToPicard_single_of_pullbackClass_eq_zero
    (c : PicardGroup Y) (hc : pullbackClass V.ι c = 0) :
    ∃ m : ℤ, c = DivisorClass.divisorToPicard Y hdim (Finsupp.single x m) := by
  classical
  revert hc
  induction c using Quotient.inductionOn with
  | h L =>
    intro hc
    obtain ⟨ep⟩ := (class_eq_iff V.toScheme (pullbackLineBundle V.ι L)
      (trivialLineBundle V.toScheme)).mp hc
    let er : (Scheme.Modules.restrictFunctor V.ι).obj L.val ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.val ≪≫ ep ≪≫
        coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit V.toScheme.ringCatSheaf)
    let e : L.val.over V ≅ SheafOfModules.unit (Y.ringCatSheaf.over V) :=
      (Scheme.Modules.overEquiv V).functor.preimageIso
        ((Scheme.Modules.overFunctorEquiv V).app L.val ≪≫ er ≪≫
          (Scheme.Modules.overUnitIso V).symm)
    let D := RationalTrivialization.divisor Y L.val V e L.property
    have hzero (y : Scheme.ClosedPoint Y) (hy : y ≠ x) : D y = 0 := by
      apply RationalTrivialization.divisorCoefficient_zero_on_chart
      change y.val ∈ (V : Set Y)
      rw [hV]
      exact fun he => hy (Subtype.ext he)
    have hsingle : D = Finsupp.single x (D x) := by
      ext y
      by_cases hy : y = x
      · subst y
        simp
      · simpa [hy, Ne.symm hy] using hzero y hy
    refine ⟨D x, ?_⟩
    have hclass : classOf Y L = classOf Y (DivisorClass.divisorLineBundle Y hdim D) :=
      (class_eq_iff Y L (DivisorClass.divisorLineBundle Y hdim D)).mpr
        ⟨DivisorInverse.toDivisorIso Y L.val L.property V e hdim⟩
    change classOf Y L = DivisorClass.divisorToPicard Y hdim (Finsupp.single x (D x))
    exact hclass.trans (congrArg (DivisorClass.divisorToPicard Y hdim) hsingle)

end SupportedDivisor

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)

/-- The original point line-bundle class at a closed point, using its native
rational section only inside the existing point-divisor construction. -/
abbrev closedPointClass (x : Scheme.ClosedPoint X.left) : PicardGroup X.left := by
  have := curveProperties_locallyOfFiniteType hX
  exact classOf X.left (PointDivisor.positiveLineBundle X hX
    (pointOfClosedPoint X.hom x.val x.property) (pointOfClosedPoint_comp X.hom x.val x.property))

variable (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
  (hV : (V : Set X.left) = {x.val}ᶜ)

include hV

omit [IsAlgClosed k] in
include hX in
/-- Removing one closed point cannot exhaust the original dimension-one
curve. No algebraic closedness is needed for this geometric fact. -/
theorem nonempty_onePoint_complement : Nonempty V := by
  classical
  by_contra hempty
  have : IsEmpty V := not_nonempty_iff.mp hempty
  have hD : Set.range V.ι = ({x.val} : Set X.left)ᶜ :=
    (Scheme.Opens.range_ι V).trans hV
  have hsingle : ({x.val} : Set X.left) = Set.univ := by
    apply compl_injective
    rw [Set.compl_univ, ← hD]
    exact Set.range_eq_empty V.ι
  have : Finite X.left := Set.finite_univ_iff.mp (hsingle ▸ Set.finite_singleton x.val)
  have : T1Space X.left := ⟨fun y => by
    have hy : y ∈ ({x.val} : Set X.left) := by rw [hsingle]; trivial
    simpa only [Set.mem_singleton_iff.mp hy] using x.property⟩
  have hdim := topologicalKrullDim_zero_of_discreteTopology X.left
  rw [curveProperties_dimension smoothFieldDimension hX] at hdim
  exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hdim

/-- The original point class restricts to zero on its complement. -/
theorem pullbackClass_closedPointClass_eq_zero :
    pullbackClass V.ι (closedPointClass hX x) = 0 := by
  have := curveProperties_locallyOfFiniteType hX
  let p := pointOfClosedPoint X.hom x.val x.property
  have hp : p ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom x.val x.property
  have hpx : p (IsLocalRing.closedPoint k) = x.val :=
    pointOfClosedPoint_apply X.hom x.val x.property _
  have hdisj : Disjoint (Set.range p) (Set.range V.ι) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, rfl⟩ hz
    have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [ht, hpx] at hz
    rw [Scheme.Opens.range_ι, hV] at hz
    exact hz rfl
  let I := PointDivisor.idealLineBundle X hX p hp
  let e : (Scheme.Modules.pullback V.ι).obj I.val ≅ (trivialLineBundle V.toScheme).val :=
    Scheme.Hom.idealModulePullbackIsoOfDisjoint p V.ι hdisj ≪≫
      (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit V.toScheme.ringCatSheaf)).symm
  have hI : pullbackClass V.ι (classOf X.left I) = 0 :=
    (class_eq_iff V.toScheme (pullbackLineBundle V.ι I) (trivialLineBundle V.toScheme)).mpr ⟨e⟩
  change pullbackClass V.ι (classOf X.left (dualLineBundle X.left I)) = 0
  rw [classOf_dual, PullbackTensor.Local.pullbackClass_neg, hI, neg_zero]

/-- The kernel of the actual one-point Picard pullback consists exactly of
the integer multiples of the original point line-bundle class. -/
theorem pullbackClass_eq_zero_iff_exists_zsmul_closedPointClass (c : PicardGroup X.left) :
    pullbackClass V.ι c = 0 ↔ ∃ m : ℤ, c = m • closedPointClass hX x := by
  have : Nonempty V := nonempty_onePoint_complement hX x V hV
  have : IsIntegral X.left :=
    curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  have : IsNoetherian X.left := curveProperties_isNoetherian hX
  have (y : Scheme.ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk y.val) :=
    isDiscreteValuationRing_stalk_of_isOpenImmersion hX (𝟙 X.left) y
  have := curveProperties_locallyOfFiniteType hX
  have hdim : topologicalKrullDim X.left ≤ 1 :=
    (curveProperties_dimension smoothFieldDimension hX).le
  let p := pointOfClosedPoint X.hom x.val x.property
  have hp : p ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom x.val x.property
  let r : Scheme.RationalPoint k X.left := ⟨X.hom, p, hp⟩
  have hr : (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint X.left) = x :=
    Subtype.ext (pointOfClosedPoint_apply X.hom x.val x.property _)
  let I := PointDivisor.idealLineBundle X hX p hp
  have hpoint : closedPointClass hX x =
      DivisorClass.divisorToPicard X.left hdim (Finsupp.single x 1) := by
    have h := PointDivisor.idealDual_class_eq_point X.left r I.property hdim
    change classOf X.left (dualLineBundle X.left I) = _ at h
    rw [hr] at h
    exact h
  constructor
  · intro hc
    obtain ⟨m, hm⟩ := exists_eq_divisorToPicard_single_of_pullbackClass_eq_zero
      X.left hdim x V hV c hc
    refine ⟨m, hm.trans ?_⟩
    have hs : Finsupp.single x m = m • Finsupp.single x (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul, ← hpoint]
  · rintro ⟨m, rfl⟩
    change PullbackTensor.Local.pullbackHom V.ι (m • closedPointClass hX x) = 0
    rw [map_zsmul]
    change m • pullbackClass V.ι (closedPointClass hX x) = 0
    rw [pullbackClass_closedPointClass_eq_zero hX x V hV, smul_zero]

include hX in
/-- The original restriction of global units across one closed point is
bijective. This asserts no equality of the full rings of regular functions. -/
theorem globalUnits_restriction_bijective :
    Function.Bijective (Units.map
      (X.left.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.toMonoidHom) := by
  classical
  have : Nonempty V := nonempty_onePoint_complement hX x V hV
  have : IsIntegral X.left :=
    curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  have : IsNoetherian X.left := curveProperties_isNoetherian hX
  have : IsProper X.hom := hX.proper
  have := curveProperties_locallyOfFiniteType hX
  have (y : Scheme.ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk y.val) :=
    isDiscreteValuationRing_stalk_of_isOpenImmersion hX (𝟙 X.left) y
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  let i : V ⟶ (⊤ : X.left.Opens) := homOfLE le_top
  have hgerm : X.left.presheaf.map i.op ≫ X.left.germToFunctionField V =
      X.left.germToFunctionField ⊤ := X.left.presheaf.germ_res i _ _
  constructor
  · intro a b hab
    apply Units.ext
    exact map_injective_of_isIntegral X.left i (congrArg Units.val hab)
  · intro a
    let f : X.left.functionFieldˣ := Units.map (X.left.germToFunctionField V).hom.toMonoidHom a
    let D := principal X.left (Additive.ofMul f)
    have hzero (y : Scheme.ClosedPoint X.left) (hy : y ≠ x) : D y = 0 := by
      have hyV : y.val ∈ (V : Set X.left) := by
        rw [hV]
        exact fun he => hy (Subtype.ext he)
      exact Scheme.ord_of_isUnit a.isUnit hyV
    have hsingle : D = Finsupp.single x (D x) := by
      ext y
      by_cases hy : y = x
      · subst y
        simp
      · simpa [hy, Ne.symm hy] using hzero y hy
    have hm : D x = 0 := by
      have h := Degree.properCurveProductFormula k X.left X.hom
        (curveProperties_dimension smoothFieldDimension hX) f
      change Degree.degDiv X.left X.hom D = 0 at h
      rw [hsingle, Degree.degDiv_single, Degree.weight_eq_one, mul_one] at h
      exact h
    have hD : principal X.left (Additive.ofMul f) = 0 := by
      change D = 0
      rw [hsingle, hm, Finsupp.single_zero]
    obtain ⟨b, hb⟩ := (principal_eq_zero_iff_globalUnit X.left
      (point_eq_generic_or_isClosed X.left (curveProperties_dimension smoothFieldDimension hX).le)
      (fun y => coheight_eq_one_of_dvr X.left y.val) f).mp hD
    refine ⟨b, ?_⟩
    apply Units.ext
    apply X.left.germToFunctionField_injective V
    have hb' : X.left.germToFunctionField ⊤ (b : Γ(X.left, ⊤)) = (f : X.left.functionField) :=
      congrArg Units.val hb
    have hg := congrArg (fun g : Γ(X.left, ⊤) ⟶ CommRingCat.of X.left.functionField =>
      g (b : Γ(X.left, ⊤))) hgerm
    exact hg.trans hb'

include hX in
/-- The same unit bijection on the literal global-section map of the original
open immersion. Its comparison with restriction on the open is the native top iso. -/
theorem globalUnits_appTop_bijective :
    Function.Bijective (Units.map V.ι.appTop.hom.toMonoidHom) := by
  let r := Units.map V.ι.appTop.hom.toMonoidHom
  let q := Units.map V.topIso.hom.hom.toMonoidHom
  let s := Units.map
    (X.left.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.toMonoidHom
  have he : V.ι.appTop ≫ V.topIso.hom =
      X.left.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    let i : V.ι ''ᵁ ⊤ ⟶ (⊤ : X.left.Opens) := homOfLE le_top
    let e : V ⟶ V.ι ''ᵁ ⊤ := eqToHom V.ι_image_top.symm
    change X.left.presheaf.map i.op ≫ X.left.presheaf.map e.op =
      X.left.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
    exact (X.left.presheaf.map_comp i.op e.op).symm.trans
      (congrArg (fun a : op (⊤ : X.left.Opens) ⟶ op V => X.left.presheaf.map a)
        (Subsingleton.elim _ _))
  have hq : Function.Bijective q :=
    Units.map_bijective (ConcreteCategory.bijective_of_isIso V.topIso.hom)
  have hs : Function.Bijective s := globalUnits_restriction_bijective hX x V hV
  have hcomp (a : Γ(X.left, ⊤)ˣ) : q (r a) = s a := by
    apply Units.ext
    exact congrArg (fun g : Γ(X.left, ⊤) ⟶ Γ(X.left, V) => g (a : Γ(X.left, ⊤))) he
  change Function.Bijective r
  constructor
  · intro a b hab
    apply hs.injective
    exact (hcomp a).symm.trans ((congrArg q hab).trans (hcomp b))
  · intro a
    obtain ⟨b, hb⟩ := hs.surjective (q a)
    exact ⟨b, hq.injective ((hcomp b).trans hb)⟩

include hX in
/-- Positive-level torsion restriction across one point is bijective, through
the actual degree-one kernel generator. No coefficient invertibility is needed. -/
theorem torsionPullback_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (torsionPullback V.ι n) := by
  have := curveProperties_locallyOfFiniteType hX
  let deg := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Degree.properCurveProductFormula X hX
  have hpoint : deg (closedPointClass hX x) = 1 :=
    curveDegree_positiveLineBundle hX (pointOfClosedPoint X.hom x.val x.property)
      (pointOfClosedPoint_comp X.hom x.val x.property)
  have hker (a : PicardGroup X.left) (hr : pullbackClass V.ι a = 0) (hd : deg a = 0) :
      a = 0 := by
    obtain ⟨m, hm⟩ :=
      (pullbackClass_eq_zero_iff_exists_zsmul_closedPointClass hX x V hV a).mp hr
    have h := congrArg deg hm
    rw [hd, map_zsmul, hpoint, smul_eq_mul, mul_one] at h
    have hm0 : m = 0 := h.symm
    simpa only [hm0, zero_smul] using hm
  have htorDeg (a : PicardGroup X.left) (ha : n • a = 0) : deg a = 0 := by
    have h := congrArg deg ha
    rw [map_nsmul, map_zero] at h
    exact (nsmul_right_injective (ne_of_gt hn)) h
  constructor
  · intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hker
    · have hv : pullbackClass V.ι a.val = pullbackClass V.ι b.val := congrArg Subtype.val hab
      change PullbackTensor.Local.pullbackHom V.ι (a.val - b.val) = 0
      rw [map_sub]
      change pullbackClass V.ι a.val - pullbackClass V.ι b.val = 0
      rw [hv, sub_self]
    · rw [map_sub, htorDeg a.val a.property, htorDeg b.val b.property, sub_self]
  · intro a
    have hx : ∃ z : X.left, IsClosed ({z} : Set X.left) ∧ z ∉ Set.range V.ι :=
      ⟨x.val, x.property, by rw [Scheme.Opens.range_ι, hV]; simp⟩
    obtain ⟨b, hb0, hba⟩ := exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion
      hX V.ι hx a.val
    have hb0' : deg b = 0 := hb0
    have hnb : n • b = 0 := by
      apply hker
      · change PullbackTensor.Local.pullbackHom V.ι (n • b) = 0
        rw [map_nsmul]
        change n • pullbackClass V.ι b = 0
        rw [hba]
        exact a.property
      · rw [map_nsmul, hb0', smul_zero]
    exact ⟨⟨b, hnb⟩, Subtype.ext hba⟩

end Curve

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction
