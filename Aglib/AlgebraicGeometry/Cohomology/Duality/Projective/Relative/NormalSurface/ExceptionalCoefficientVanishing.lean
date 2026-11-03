/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity.IdealSequence
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.ExceptionalCurveTwistVanishing
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.CartierCurve.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# Coefficient ideal-power vanishing on the original rational blowup

The original Cartier row and an actual coefficient-canonical restriction
identify all quotients. Native Serre vanishing starts one finite descent.
The residue coefficient line remains explicit and is not trivialized.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance coefficientVanishingDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

private theorem coefficientIdealPower_serreH1
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdA : ringKrullDim A = 2) (M : (source A hdA).Modules) [M.IsFinitePresentation] :
    ∃ B : ℕ, ∀ q : ℕ, B ≤ q →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (source A hdA)
        (ordinaryIdealPower A hdA q ⊗ M)) 1) := by
  let X := source A hdA
  obtain ⟨d, j, hj, _, ⟨eJ⟩⟩ := exists_tautologicalEmbedding A hdA
  let : IsClosedImmersion j := hj
  obtain ⟨B, hB⟩ := embeddedTensorTwist_serreVanishing j d Equiv.ulift M
    (affineLocallyFiniteType_of_finitePresentation M)
  refine ⟨B, fun q hq => ?_⟩
  let ep := Surfaces.Contraction.projectivePowerIso j
    (ordinaryExceptionalLine A hdA) eJ.symm q
  let eP := ep.symm ≪≫ ordinaryTensorPowerIso A hdA q
  exact moduleCohomology_subsingleton_of_iso
    ((moduleTensorRightFunctor X M).mapIso eP) 1
    (hB (q : ℤ) (by exact_mod_cast hq) 1 (by decide))


variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdA : ringKrullDim A = 2) (hNagata : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A)
    (M : (source A hdA).Modules) [M.IsFinitePresentation]

/-- The field structure on the original maximal-ideal quotient. -/
local instance coefficientVanishingResidueField : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
  Ideal.Quotient.field _

local notation "κ" => A ⧸ IsLocalRing.maximalIdeal A

variable (ιE : Type u)
    (jE : exceptionalCurve A hdA ⟶ ProjectiveSpace (A ⧸ IsLocalRing.maximalIdeal A) ιE)
    [IsClosedImmersion jE]
    (m : ℕ) (em : ιE ≃ Fin (m + 1)) (hm : 1 ≤ m)
    (hstruct : jE ≫ toSpec (A ⧸ IsLocalRing.maximalIdeal A) ιE = exceptionalStructureMap A hdA)
    (eL : (Modules.pullback jE).obj
      (twistingSheaf (A ⧸ IsLocalRing.maximalIdeal A) ιE 1) ≅ (exceptionalLine A hdA).val)
    (V : ModuleCat.{u} (A ⧸ IsLocalRing.maximalIdeal A))
    [Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) V]
    (hV : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) V = 1)
    (eM : (Modules.pullback (exceptionalCurveInclusion A hdA)).obj M ≅
      cmCurveCoefficientCanonicalModule (A ⧸ IsLocalRing.maximalIdeal A) ιE jE m V ⊗
        (exceptionalLine A hdA).val)
    [Mono ((cartierTensorSection (exceptionalCurveInclusion A hdA)).app M)]

include hNagata hRat em hm hstruct eL hV eM in
/-- Every original exceptional ideal power of the actual coefficient has H1 zero.
Both the Serre start and the positive curve quotient vanishings are proved. -/
theorem exceptionalCoefficientIdealPower_h1_subsingleton (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (source A hdA)
      (ordinaryIdealPower A hdA q ⊗ M)) 1) := by
  let X := source A hdA
  let E := exceptionalCurve A hdA
  let i := exceptionalCurveInclusion A hdA
  let W := M
  let I : X.Modules := idealModule i
  let L : E.Modules := (exceptionalLine A hdA).val
  let Ω := cmCurveCoefficientCanonicalModule κ ιE jE m V
  let : Ω.IsFinitePresentation :=
    cmCurveCoefficientCanonicalModule_finitePresentation κ ιE jE m em V
  let S := idealTensorQuotientSequence i W
  have hS : S.ShortExact := idealTensorQuotientSequence_shortExact i (datum A).cartier W
  have hstep (r : ℕ)
      (hnext : Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf X (ordinaryIdealPower A hdA (r + 1) ⊗ W)) 1)) :
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf X (ordinaryIdealPower A hdA r ⊗ W)) 1) := by
    let P := ordinaryIdealPower A hdA r
    let Q := exceptionalPower A hdA (r + 1) ⊗ Ω
    let : IsFiniteLocallyFree X P :=
      isFiniteLocallyFree_of_isLocallyRankOne (ordinaryIdealPower_locallyRankOne A hdA r)
    let T := S.map (moduleTensorLeftFunctor X P)
    have hT : T.ShortExact := tensor_shortExact_finiteLocallyFree P S hS
    let e₁ : T.X₁ ≅ ordinaryIdealPower A hdA (r + 1) ⊗ W :=
      (moduleTensorLeftFunctor X P).mapIso (β_ W I) ≪≫
        (α_ P I W).symm ≪≫
          (moduleTensorRightFunctor X W).mapIso (ordinaryPowerStepIso A hdA r)
    let : IsIso (pullbackTensorMap i P I) := Pullback.Tensor.pullbackTensorMap_isIso i P I
    let eStep : exceptionalPower A hdA r ⊗ L ≅ exceptionalPower A hdA (r + 1) :=
      (asIso (pullbackTensorMap i P I)).symm ≪≫
        (Modules.pullback i).mapIso (ordinaryPowerStepIso A hdA r)
    let eQ : (Modules.pullback i).obj P ⊗ (Modules.pullback i).obj W ≅ Q :=
      (moduleTensorLeftFunctor E (exceptionalPower A hdA r)).mapIso eM ≪≫
        (moduleTensorLeftFunctor E (exceptionalPower A hdA r)).mapIso (β_ Ω L) ≪≫
          (α_ (exceptionalPower A hdA r) L Ω).symm ≪≫
            (moduleTensorRightFunctor E Ω).mapIso eStep
    let e₃ : T.X₃ ≅ (Modules.pushforward i).obj Q :=
      closedImmersionProjectionFormulaIso i P ((Modules.pullback i).obj W) ≪≫
        (Modules.pushforward i).mapIso eQ
    let : (exceptionalPower A hdA (r + 1)).IsQuasicoherent :=
      lineBundle_isQuasicoherent ⟨exceptionalPower A hdA (r + 1),
        pullback_locallyRankOne i _ (ordinaryIdealPower_locallyRankOne A hdA (r + 1))⟩
    let : Q.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor _ _
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf E Q) 1) :=
      exceptionalCoefficientPositivePower_h1_subsingleton A hdA hNagata hRat
        ιE jE m em hm hstruct eL V
        hV (r + 1) (by omega)
    have hpush : Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf X ((Modules.pushforward i).obj Q)) 1) :=
      (moduleAffinePushforwardCohomologyLinearEquiv i
        (ordinaryCoefficients A hdA) Q 1).toEquiv.subsingleton
    exact CartierCurve.h1_subsingleton_middle T hT
      (moduleCohomology_subsingleton_of_iso e₁.symm 1 hnext)
      (moduleCohomology_subsingleton_of_iso e₃.symm 1 hpush)
  obtain ⟨B, hB⟩ := coefficientIdealPower_serreH1 A hdA M
  have hdesc (k : ℕ) : ∀ r : ℕ, B ≤ r + k →
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf X (ordinaryIdealPower A hdA r ⊗ W)) 1) := by
    induction k with
    | zero => exact fun r hr => hB r (by simpa using hr)
    | succ k ih =>
      intro r hr
      exact hstep r (ih (r + 1) (by omega))
  exact hdesc B q (by omega)


include hNagata hRat em hm hstruct eL hV eM in
/-- Sections lift through the literal original closed-immersion adjunction unit
for this actual coefficient, not through a substituted restriction map. -/
theorem exceptionalCoefficientRestriction_sections_surjective :
    Function.Surjective
      (((pullbackPushforwardAdjunction (exceptionalCurveInclusion A hdA)).unit.app
        M).val.app (op ⊤)) := by
  let X := source A hdA
  let i := exceptionalCurveInclusion A hdA
  let W := M
  let S := idealTensorQuotientSequence i W
  have hS : S.ShortExact := idealTensorQuotientSequence_shortExact i (datum A).cartier W
  have hpower := exceptionalCoefficientIdealPower_h1_subsingleton
    A hdA hNagata hRat M ιE jE m em hm hstruct eL V hV eM 1
  let eI : ordinaryIdealPower A hdA 1 ≅ idealModule i :=
    eqToIso (congrArg (fun J : X.IdealSheafData => idealModule J.subschemeι)
      (pow_one (exceptionalIdeal A hdA)))
  let e : ordinaryIdealPower A hdA 1 ⊗ W ≅ S.X₁ :=
    (moduleTensorRightFunctor X W).mapIso eI ≪≫ β_ (idealModule i) W
  exact CartierCurve.sections_surjective_of_h1_subsingleton S hS
    (moduleCohomology_subsingleton_of_iso e 1 hpower)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
