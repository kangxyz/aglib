/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.PointBlowupFrame
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence

/-!
# Conditional original exceptional inverse-line identification

Restrict the SAME original-map canonical frame to the full exceptional
scheme. The existing localized Cartier isomorphism, for the SAME selected
projective embedding and original derived residue coefficient, then
trivializes the positive canonical twist. Cancel the actual exceptional
line using its native dual evaluation, braiding, associators and unit maps.

This constructs the inverse-line identification; it is not a premise.
The sole exceptional-generation premise remains conditional.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Modules.standardHasDerivedCategory restrictionModuleDerived

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


/-- CONDITIONAL: the original Cartier coefficient for the SAME chosen
exceptional embedding is the dual of the actual positive exceptional line.
The isomorphism is constructed from the SAME original inverse-trace map. -/
def normalSurfacePointBlowupExceptionalCanonicalInverseLineIso
    (hgen : Epi (globalSectionsEval
      ((Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
        ((Modules.pullback (stalkBlowupComparison P x hx)).obj
          (normalSurfaceCanonicalModule R ιZ jZ nZ)))))
    (ιE : Type u)
    (jE : exceptionalCurve (P.presheaf.stalk x) hdS ⟶
      ProjectiveSpace (P.residueField x) ιE) [IsClosedImmersion jE]
    (m : ℕ) (eE : ιE ≃ Fin (m + 1)) (hm : 1 ≤ m)
    (hjE : jE ≫ toSpec (P.residueField x) ιE =
      RationalSingularities.MaximalIdealBlowup.exceptionalStructureMap
        (P.presheaf.stalk x) hdS) :
    cmCurveCoefficientCanonicalModule (P.residueField x) ιE jE m
        (ModuleCat.derivedResidueCoefficientLine R (P.residueField x)) ≅
      (dualLineBundle (exceptionalCurve (P.presheaf.stalk x) hdS)
        (exceptionalLine (P.presheaf.stalk x) hdS)).val := by
  let : Finite ιP := Finite.of_equiv _ eP.symm
  let : IsIntegrallyClosed (P.presheaf.stalk x) := (hP x).2
  let E := exceptionalCurve (P.presheaf.stalk x) hdS
  let i := exceptionalCurveInclusion (P.presheaf.stalk x) hdS
  let L := exceptionalLine (P.presheaf.stalk x) hdS
  let W := cmCurveCoefficientCanonicalModule (P.residueField x) ιE jE m
    (ModuleCat.derivedResidueCoefficientLine R (P.residueField x))
  let eB := normalSurfacePointBlowupCanonicalIsoOfExceptionalGeneration
    R P x hx ιP ιZ jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
    hdR hdS hNagata hRat hres d hgen
  let eRes := localizedExceptionalCanonicalRestrictionIso
    R P x hx hdS ιZ jZ hZ hdZ nZ eZ hfinZ hdR hNagata hRat
    (jP ≫ toSpec R ιP) hb hres ιE jE m eE hm hjE
  let eTriv : W ⊗ L.val ≅ SheafOfModules.unit E.ringCatSheaf :=
    eRes.symm ≪≫ (Modules.pullback i).mapIso eB ≪≫ pullbackUnitIso i
  let T := lineBundleDualTensorEquivalence E L
  exact (T.counitIso.app W).symm ≪≫
    T.functor.mapIso ((tensorSheafBraiding E L.val W) ≪≫ eTriv) ≪≫
      ((SheafOfModulesOfCommRing.tensorRightUnitIso E.sheaf).app (dualLineBundle E L).val)

end AlgebraicGeometry.Scheme.Cohomology
