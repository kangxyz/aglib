/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.Cohomology.Blowup.RegularPoint
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Single
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleUnit.ShortExact

/-!
# The original derived positive exceptional section

For an ordinary regular surface-point blowup, the positive exceptional line
is the actual dual of the original point ideal. Its original section is the
transpose of that ideal inclusion. The tensor ideal sequence has the actual
restricted dual ideal as its quotient. The same exceptional P1 identifies
that quotient with O(-1), whose original cohomology vanishes in every degree.

The resulting isomorphism is the original structural derived unit followed
by the derived image of that section. Its inverse retains this exact unit
equation. No canonical module, Grauert--Riemenschneider vanishing, residue
separability, or family of other exceptional twists is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Opposite HomologicalComplex IsLocalRing
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for module sheaves on the given scheme. -/
local instance exceptionalPositiveDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original structure module with its scheme-module category fixed explicitly. -/
def exceptionalPositiveStructureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The positive line is the actual structure-linear dual of the original exceptional ideal. -/
abbrev exceptionalPositiveModule (X : Scheme.{u}) (x : X) : (pointBlowup X x).Modules :=
  dualSheaf (pointBlowup X x) (idealModule (pointExceptionalι X x))

/-- This is the dual of the original invertible point ideal, with no replacement divisor. -/
theorem exceptionalPositiveModule_eq_pointIdealDual (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    exceptionalPositiveModule X x =
      (dualLineBundle (pointBlowup X x) (pointIdealLine X x hx)).val := rfl

/-- The original ideal inclusion transposed into its actual dual. -/
def exceptionalPositiveSection (X : Scheme.{u}) (x : X) :
    exceptionalPositiveStructureModule (pointBlowup X x) ⟶ exceptionalPositiveModule X x :=
  cartierDualIdealSection (pointExceptionalι X x)

/-- At one, the section evaluates an original ideal element by its original inclusion. -/
theorem exceptionalPositiveSection_one_evaluate (X : Scheme.{u}) (x : X)
    (U : (pointBlowup X x).Opens)
    (a : (idealModule (pointExceptionalι X x)).val.obj (op U)) :
    ((exceptionalPositiveSection X x).val.app (op U)
        (1 : Γ(pointBlowup X x, U))).val.app (op (Over.mk (𝟙 U))) a =
      (idealInclusion (pointExceptionalι X x)).val.app (op U) a :=
  InternalHom.transpose_one_evaluate (pointBlowup X x)
    (idealInclusion (pointExceptionalι X x)) U a

/-- The quotient map is the original pullback/pushforward unit of the positive line. -/
def exceptionalPositiveQuotientMap (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    exceptionalPositiveModule X x ⟶
      (pushforward (pointExceptionalι X x)).obj (pointNormalLine X x hx).val :=
  (pullbackPushforwardAdjunction (pointExceptionalι X x)).unit.app
    (exceptionalPositiveModule X x)

/-- The original positive section is killed by the original exceptional quotient map. -/
theorem exceptionalPositiveSection_quotient_zero (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    exceptionalPositiveSection X x ≫ exceptionalPositiveQuotientMap X x hx = 0 := by
  let i := pointExceptionalι X x
  let : IsClosedImmersion i := pointExceptionalι_isClosedImmersion X x hx
  let J : LineBundle (pointBlowup X x) := pointIdealLine X x hx
  let L := exceptionalPositiveModule X x
  let S := idealTensorQuotientSequence i L
  let e₀ := dualEvaluationIso (pointBlowup X x) J
  let e : S.X₁ ≅ exceptionalPositiveStructureModule (pointBlowup X x) :=
    ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
  have he : e.hom ≫ exceptionalPositiveSection X x = S.f :=
    cartierDualEvaluation_transpose i J.property
  apply (cancel_epi e.hom).mp
  rw [comp_zero, ← Category.assoc, he]
  exact S.zero

/-- The exact row retains the actual positive section and the original normal-line quotient. -/
def exceptionalPositiveSequence (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) : ShortComplex (pointBlowup X x).Modules :=
  ShortComplex.mk (exceptionalPositiveSection X x)
    (exceptionalPositiveQuotientMap X x hx) (exceptionalPositiveSection_quotient_zero X x hx)

/-- The original tensor ideal row proves short exactness of the original positive row. -/
theorem exceptionalPositiveSequence_shortExact (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) : (exceptionalPositiveSequence X x hx).ShortExact := by
  let i := pointExceptionalι X x
  let : IsClosedImmersion i := pointExceptionalι_isClosedImmersion X x hx
  let J : LineBundle (pointBlowup X x) := pointIdealLine X x hx
  let L := exceptionalPositiveModule X x
  let : IsFiniteLocallyFree (pointBlowup X x) L :=
    isFiniteLocallyFree_of_isLocallyRankOne
      (dualLineBundle (pointBlowup X x) J).property
  let S := idealTensorQuotientSequence i L
  have hS : S.ShortExact :=
    ShortComplex.shortExact_of_iso (idealTensorQuotientSequenceIso i L)
      (tensor_shortExact_finiteLocallyFree L (idealSequence i) (idealSequence_shortExact i))
  let e₀ := dualEvaluationIso (pointBlowup X x) J
  let e : S.X₁ ≅ exceptionalPositiveStructureModule (pointBlowup X x) :=
    ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
  have he : e.hom ≫ exceptionalPositiveSection X x = S.f :=
    cartierDualEvaluation_transpose i J.property
  let E : S ≅ exceptionalPositiveSequence X x hx :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by
        change e.hom ≫ exceptionalPositiveSection X x = S.f ≫ 𝟙 L
        exact he.trans (Category.comp_id S.f).symm)
      (by
        change (𝟙 L) ≫ exceptionalPositiveQuotientMap X x hx =
          exceptionalPositiveQuotientMap X x hx ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact ShortComplex.shortExact_of_iso E hS

private theorem projectiveLine_negativeOne_cohomology (k : Type u) [CommRing k] (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace k (ULift.{u} (Fin 2)))
        (ProjectiveSpace.twistingSheaf k (ULift.{u} (Fin 2)) (-1))) q) := by
  classical
  by_cases hq : q = 0
  · subst q
    let : IsEmpty (MvPolynomial.coordinateLaurentEndpointWeight
        (ι := ULift.{u} (Fin 2)) (-1)) := by
      constructor
      rintro ⟨e, he | he⟩
      · let a := (MvPolynomial.coordinateNonnegativeDegreeExponentEquiv
          (ι := ULift.{u} (Fin 2)) (-1)).symm
            (MvPolynomial.coordinateEmptyWeightEquiv (-1) ⟨e, he⟩)
        have ha := a.property
        omega
      · let : IsEmpty (MvPolynomial.coordinateNegativeDegreeExponents
            (ι := ULift.{u} (Fin 2)) (-1)) :=
          MvPolynomial.coordinateNegativeDegreeExponents_isEmpty (-1) (by simp)
        exact isEmptyElim (MvPolynomial.coordinateFullWeightEquiv (-1) ⟨e, he⟩)
    exact (twistingCohomologyEndpointEquiv k (ULift.{u} (Fin 2)) (-1) 0).injective.subsingleton
  · exact twistingCohomology_subsingleton_of_neg_le_degree k (ULift.{u} (Fin 2))
      1 Equiv.ulift (-1) q (by decide) hq

/-- The original exceptional normal line has zero original cohomology in every degree.
The dimension-two local-ring input and the full residue field are retained. -/
theorem pointNormalLine_cohomology_subsingleton (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pointExceptionalFibre X x) (pointNormalLine X x hx).val) q) := by
  let k := ResidueField (X.presheaf.stalk x)
  let P := ProjectiveSpace k (ULift.{u} (Fin 2))
  let T := ProjectiveSpace.twistingSheaf k (ULift.{u} (Fin 2)) (-1)
  let j := pointNativeComparison X x hx hd
  let : IsIso j := by
    let E := (Over.forget (Spec (X.residueField x))).mapIso
      (pointExceptionalOverIsoProjectiveP1 X x hx hd)
    dsimp only [j]
    rw [pointNativeComparison_projectiveP1]
    exact IsIso.comp_isIso' E.isIso_hom
      (ProjectiveSpace.finUliftIso (ResidueField (X.presheaf.stalk x)) 2).isIso_hom
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf P T) q) :=
    projectiveLine_negativeOne_cohomology k q
  have hp : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pointExceptionalFibre X x) ((Scheme.Modules.pullback j).obj T)) q) := by
    have hs := (moduleCohomologyPullback_bijective j T q).2
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hs a
    obtain ⟨b, rfl⟩ := hs b
    exact congrArg (moduleCohomologyPullback j T q) (Subsingleton.elim a b)
  exact moduleCohomology_subsingleton_of_iso
    (pointNormalTwistingIso X x hx hd).symm q hp

private theorem affineTarget_higherImage_isZero_of_cohomology
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ)
    (hM : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q)) :
    IsZero (((pushforward f).rightDerived q).obj M) := by
  let G := ((pushforward f).rightDerived q).obj M
  let := hM
  let : Subsingleton (moduleSpecΓFunctor.obj G) :=
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M
      (injectiveResolution M) q).injective.subsingleton
  let : G.IsQuasicoherent := moduleHigherDirectImage_isQuasicoherent f M q
  let : (tilde.functor (.of R)).PreservesZeroMorphisms :=
    ⟨fun _ _ => tilde.map_zero⟩
  exact ((tilde.functor (.of R)).map_isZero (ModuleCat.isZero_of_subsingleton
    (moduleSpecΓFunctor.obj G))).of_iso (asIso G.fromTildeΓ).symm

private theorem affineTarget_derivedSingle_isZero_of_all_cohomology
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : Y.Modules) [M.IsQuasicoherent]
    (hM : ∀ q : ℕ, Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q)) :
    IsZero ((derivedPushforwardPlus f).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M)) := by
  let F := pushforward f
  have hz (q : ℕ) : IsZero ((F.rightDerived q).obj M) :=
    affineTarget_higherImage_isZero_of_cohomology f M q (hM q)
  have hordinary : IsZero (F.obj M) := (hz 0).of_iso (F.rightDerivedZeroIsoSelf.app M).symm
  have hsingle := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).map_isZero hordinary
  exact hsingle.of_iso (F.rightDerivedFunctorPlusSingleIsoOfAcyclic M (fun q => hz (q + 1)))

/-- The actual normal-line quotient has zero derived image under the original blowdown. -/
theorem exceptionalPositiveQuotient_derived_isZero (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk x)] (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsZero ((derivedPushforwardPlus (pointBlowdown X x)).obj
      ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).obj
        ((pushforward (pointExceptionalι X x)).obj (pointNormalLine X x hx).val))) := by
  let E := pointExceptionalFibre X x
  let Y := pointBlowup X x
  let k := ResidueField (X.presheaf.stalk x)
  let i : E ⟶ Y := pointExceptionalι X x
  let b : Y ⟶ X := pointBlowdown X x
  let p : E ⟶ Spec (.of k) := pointExceptionalStructureMap X x
  let j : Spec (.of k) ⟶ X := X.fromSpecResidueField x
  let N : E.Modules := (pointNormalLine X x hx).val
  let K := (DerivedCategory.Plus.singleFunctor (pointExceptionalFibre X x).Modules 0).obj N
  let : IsClosedImmersion i := pointExceptionalι_isClosedImmersion X x hx
  let : IsProper b := (pointBlowupDatum X x).isProper_of_isLocallyNoetherian
  let : IsProper p := inferInstanceAs
    (IsProper (Limits.pullback.snd (pointBlowdown X x) (X.fromSpecResidueField x)))
  let : UniversallyClosed p := (inferInstance : IsProper p).toUniversallyClosed
  let : QuasiCompact p := ⟨fun _ _ => p.isProperMap.isCompact_preimage⟩
  let : IsSeparated p := (inferInstance : IsProper p).toIsSeparated
  let : QuasiSeparated p := inferInstance
  let : IsFiniteLocallyFree (pointExceptionalFibre X x) N :=
    isFiniteLocallyFree_of_isLocallyRankOne (pointNormalLine X x hx).property
  let : N.IsQuasicoherent := lineBundle_isQuasicoherent (pointNormalLine X x hx)
  have hp : IsZero ((derivedPushforwardPlus p).obj K) :=
    affineTarget_derivedSingle_isZero_of_all_cohomology p N
      (pointNormalLine_cohomology_subsingleton X x hx hd)
  have hsquare : i ≫ b = p ≫ j := Limits.pullback.condition
  have hcomp : IsZero ((derivedPushforwardPlus (i ≫ b)).obj K) := by
    rw [hsquare]
    exact ((derivedPushforwardPlus j).map_isZero hp).of_iso
      ((derivedPushforwardPlusCompIso p j).app K)
  exact hcomp.of_iso
    ((derivedPushforwardPlus b).mapIso (affineDerivedPushforwardSingleIso i N).symm ≪≫
      ((derivedPushforwardPlusCompIso i b).app K).symm)

/-- Applying the original derived pushforward to the original positive section is invertible. -/
theorem exceptionalPositiveSection_derived_isIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk x)] (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsIso ((derivedPushforwardPlus (pointBlowdown X x)).map
      ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).map
        (exceptionalPositiveSection X x))) := by
  let hS := exceptionalPositiveSequence_shortExact X x hx
  let F := derivedPushforwardPlus (pointBlowdown X x)
  let T := F.mapTriangle.obj hS.singleTrianglePlus
  have hT : T ∈ distTriang _ :=
    F.map_distinguished hS.singleTrianglePlus hS.singleTrianglePlus_distinguished
  have hz : IsZero T.obj₃ := exceptionalPositiveQuotient_derived_isZero X x hx hd
  exact (T.isZero₃_iff_isIso₁ hT).mp hz

private theorem regularPoint_derivedStructureUnit_isIso
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (hX : RegularStalks X)
    (x : X) (hx : IsClosed ({x} : Set X)) (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsIso (moduleDerivedPushforwardUnit X (pointBlowdown X x)) := by
  let b := pointBlowdown X x
  let O : (pointBlowup X x).Modules := SheafOfModules.unit (pointBlowup X x).ringCatSheaf
  let F := pushforward b
  have hz (q : ℕ) : IsZero ((F.rightDerived (q + 1)).obj O) :=
    isZero_higherDirectImage_structure_of_regular_point X hX x hx hd (q + 1)
      (Nat.zero_lt_succ q)
  let : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus (pointBlowup X x).Modules 0).obj O)) :=
    F.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ O hz
  let E : F.mapCochainComplexPlus.obj
      ((CochainComplex.singleFunctorPlus (pointBlowup X x).Modules 0).obj O) ≅
      (CochainComplex.singleFunctorPlus X.Modules 0).obj (F.obj O) :=
    (CochainComplex.plus X.Modules).isoMk ((singleMapHomologicalComplex F (.up ℤ) 0).app O)
  have hsingle : IsIso (F.rightDerivedSingleUnit O) := by
    change IsIso (DerivedCategory.Plus.Q.map E.inv ≫
      F.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus (pointBlowup X x).Modules 0).obj O))
    infer_instance
  let := hsingle
  let : IsIso (structureModuleMap b) :=
    isIso_structureModuleMap_of_regular_point X hX x hx hd
  change IsIso ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
    (structureModuleMap b) ≫ F.rightDerivedSingleUnit O)
  infer_instance

/-- The specified original structural unit followed by the derived original dual-ideal section. -/
def exceptionalPositiveDelta (X : Scheme.{u}) (x : X) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (exceptionalPositiveStructureModule X) ⟶
      (derivedPushforwardPlus (pointBlowdown X x)).obj
        ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).obj
          (exceptionalPositiveModule X x)) :=
  moduleDerivedPushforwardUnit X (pointBlowdown X x) ≫
    (derivedPushforwardPlus (pointBlowdown X x)).map
      ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).map
        (exceptionalPositiveSection X x))

/-- The actual positive exceptional delta is invertible for an original
regular surface-point blowup. -/
theorem exceptionalPositiveDelta_isIso (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (hX : RegularStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : IsIso (exceptionalPositiveDelta X x) := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact IsIso.comp_isIso' (regularPoint_derivedStructureUnit_isIso X hX x hx hd)
    (exceptionalPositiveSection_derived_isIso X x hx hd)

/-- Delta is also the original ordinary coefficient map followed by its installed derived unit. -/
theorem exceptionalPositiveDelta_singleUnit (X : Scheme.{u}) (x : X) :
    exceptionalPositiveDelta X x =
      (DerivedCategory.Plus.singleFunctor X.Modules 0).map
        (structureModuleMap (pointBlowdown X x) ≫
          (pushforward (pointBlowdown X x)).map (exceptionalPositiveSection X x)) ≫
      (pushforward (pointBlowdown X x)).rightDerivedSingleUnit (exceptionalPositiveModule X x) := by
  let F := pushforward (pointBlowdown X x)
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let OX : X.Modules := exceptionalPositiveStructureModule X
  let OY : (pointBlowup X x).Modules := exceptionalPositiveStructureModule (pointBlowup X x)
  let L : (pointBlowup X x).Modules := exceptionalPositiveModule X x
  let u : OX ⟶ F.obj OY := structureModuleMap (pointBlowdown X x)
  let v : OY ⟶ L := exceptionalPositiveSection X x
  let w : OX ⟶ F.obj L := u ≫ F.map v
  have h := F.rightDerivedSingleUnit_coefficient_naturality u w (𝟙 OX) v
    (Category.id_comp w)
  change (S.map u ≫ F.rightDerivedSingleUnit OY) ≫
    F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).map v) =
    S.map w ≫ F.rightDerivedSingleUnit L
  have hid : S.map (𝟙 OX) = 𝟙 (S.obj OX) := S.map_id OX
  have hc : S.map (𝟙 OX) ≫ (S.map w ≫ F.rightDerivedSingleUnit L) =
      S.map w ≫ F.rightDerivedSingleUnit L :=
    (congrArg (fun a : S.obj OX ⟶ S.obj OX =>
      a ≫ (S.map w ≫ F.rightDerivedSingleUnit L)) hid).trans (Category.id_comp _)
  exact h.symm.trans hc

/-- Rho is the inverse of this same original delta, fixing its scalar normalization. -/
def exceptionalPositiveRho (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (hX : RegularStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    (derivedPushforwardPlus (pointBlowdown X x)).obj
        ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).obj
          (exceptionalPositiveModule X x)) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (exceptionalPositiveStructureModule X) := by
  let := exceptionalPositiveDelta_isIso X hX x hx hd
  exact inv (exceptionalPositiveDelta X x)

/-- The global original structural-unit equation, before any generic or scalar specialization. -/
@[reassoc]
theorem exceptionalPositiveRho_unit (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (hX : RegularStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    moduleDerivedPushforwardUnit X (pointBlowdown X x) ≫
      (derivedPushforwardPlus (pointBlowdown X x)).map
        ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).map
          (exceptionalPositiveSection X x)) ≫
      exceptionalPositiveRho X hX x hx hd = 𝟙 _ := by
  let := exceptionalPositiveDelta_isIso X hX x hx hd
  exact (Category.assoc (moduleDerivedPushforwardUnit X (pointBlowdown X x))
    ((derivedPushforwardPlus (pointBlowdown X x)).map
      ((DerivedCategory.Plus.singleFunctor (pointBlowup X x).Modules 0).map
        (exceptionalPositiveSection X x)))
    (exceptionalPositiveRho X hX x hx hd)).symm.trans
      (IsIso.hom_inv_id (exceptionalPositiveDelta X x))

/-- The other inverse identity retains the same actual derived positive line. -/
@[reassoc]
theorem exceptionalPositiveRho_delta (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (hX : RegularStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    exceptionalPositiveRho X hX x hx hd ≫ exceptionalPositiveDelta X x = 𝟙 _ := by
  let := exceptionalPositiveDelta_isIso X hX x hx hd
  exact IsIso.inv_hom_id (exceptionalPositiveDelta X x)

end AlgebraicGeometry.Scheme.Cohomology
