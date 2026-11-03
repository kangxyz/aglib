/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.IsIso
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Generation
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.LocalizedExceptionalCanonicalVanishing
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.DerivedUnit
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Support
public import Aglib.AlgebraicGeometry.Modules.Generators.Restriction
public import Aglib.AlgebraicGeometry.Modules.Locality.PointLocalization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Quotient

/-!
# Conditional generation of the original point-blowup canonical pullback

Generation of the SAME full exceptional restriction of the original global
canonical coefficient implies epimorphy of the original inverse-trace
adjoint. The original local rationality supplies the structure-unit and trace
isomorphisms. Actual Cartier vanishing supplies section lifting; proper local
support and the original away-centre isomorphism give the global conclusion.

This is a conditional bridge, not a proof of exceptional generation. Its one
generation input must be discharged on the full nonreduced exceptional scheme.
No canonical frame, child Gorenstein assumption, finite later stalk over the
original base, or altered trace or coefficient action is introduced.
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

include hdR hres in
/-- CONDITIONAL bridge: generation of the actual full exceptional restriction
implies that the original adjoint of the original inverse proper canonical
trace is epi. All unit, trace, section-lifting and locality facts are derived. -/
theorem normalSurfacePointBlowupCanonicalPullback_epi_of_exceptional_generation
    (hgen : Epi (globalSectionsEval
      ((Modules.pullback (exceptionalCurveInclusion (P.presheaf.stalk x) hdS)).obj
        ((Modules.pullback (stalkBlowupComparison P x hx)).obj
          (normalSurfaceCanonicalModule R ιZ jZ nZ))))) :
    letI : IsProper (pointBlowdown P x) :=
      (pointBlowupDatum P x).isProper_of_isLocallyNoetherian
    letI : IsIso (moduleDerivedPushforwardUnit P (pointBlowdown P x)) :=
      RationalSingularities.isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
        P hP x hx (pointBlowupDatum P x) hNagata hdS hRat hdZ
    letI : IsIso (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
      jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ) :=
      normalSurfaceProperCanonicalTrace_isIso_of_structureUnit R ιP ιZ
        (pointBlowdown P x) jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
    Epi (ordinaryTracePullback (pointBlowdown P x)
      (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
        jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ)) := by
  let : Finite ιP := Finite.of_equiv _ eP.symm
  let : IsProper (pointBlowdown P x) :=
    (pointBlowupDatum P x).isProper_of_isLocallyNoetherian
  let : IsIso (moduleDerivedPushforwardUnit P (pointBlowdown P x)) :=
    RationalSingularities.isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
      P hP x hx (pointBlowupDatum P x) hNagata hdS hRat hdZ
  let : IsIso (normalSurfaceProperCanonicalTrace R ιP ιZ (pointBlowdown P x)
    jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ) :=
    normalSurfaceProperCanonicalTrace_isIso_of_structureUnit R ιP ιZ
      (pointBlowdown P x) jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
  let : IsProper (jP ≫ toSpec R ιP) := inferInstance
  let : Flat (P.fromSpecStalk x) := Scheme.fromSpecStalk_flat P x
  let S := P.presheaf.stalk x
  let b := pointBlowdown P x
  let a : source S hdS ⟶ pointBlowup P x := stalkBlowupComparison P x hx
  let p := map S hdS
  let i := exceptionalCurveInclusion S hdS
  let W := normalSurfaceCanonicalModule R ιZ jZ nZ
  let V := normalSurfaceCanonicalModule R ιP jP nP
  let τ := normalSurfaceProperCanonicalTrace R ιP ιZ b
    jP jZ hb hP hdP hZ hdZ nP nZ eP eZ hfinP hfinZ
  let φ : (Modules.pullback b).obj V ⟶ W := ordinaryTracePullback b τ
  let M := (Modules.pullback a).obj W
  let φS := (Modules.pullback a).map φ
  let H : IsPullback a p b (P.fromSpecStalk x) :=
    stalkBlowupComparison_isPullback P x hx
  let : W.IsFinitePresentation :=
    normalSurfaceHomology_finitePresentation R ιZ jZ nZ eZ (nZ : ℤ)
  let : V.IsFinitePresentation :=
    normalSurfaceHomology_finitePresentation R ιP jP nP eP (nP : ℤ)
  let : M.IsFinitePresentation := Modules.finitePresentation_pullback a W
  let : W.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType
    (affineLocallyFiniteType_of_finitePresentation W)
  let : V.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType
    (affineLocallyFiniteType_of_finitePresentation V)
  have hsections : Function.Surjective (φS.val.app (op ⊤)) :=
    ordinaryTracePullback_baseChange_app_top_surjective a p b (P.fromSpecStalk x) H τ
  have hunit : Function.Surjective
      (((pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤)) :=
    (localizedExceptionalCanonicalVanishing R P x hx hdS ιZ jZ hZ hdZ nZ eZ hfinZ
      hP hdR hNagata hRat (jP ≫ toSpec R ιP) hb hres).2
  let : Epi (globalSectionsEval ((Modules.pullback i).obj M)) := hgen
  let : Epi ((Modules.pullback i).map φS) :=
    epi_pullback_of_sections_and_unit_surjective i φS hsections hunit
  have hQ : affineLocallyFiniteType (source S hdS) (cokernel φS) :=
    affineLocallyFiniteType_cokernel φS (affineLocallyFiniteType_of_finitePresentation M)
  let : Field (S ⧸ IsLocalRing.maximalIdeal S) := Ideal.Quotient.field _
  let : IsLocalHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : Epi φS :=
    Surfaces.Contraction.FormalNeighborhood.properLocal_epi_of_closedFibre_pullback_epi
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)) p i
      (exceptionalStructureMap S hdS) (exceptionalStructureMap_isPullback S hdS) φS hQ
  let U : P.Opens := ⟨({x} : Set P)ᶜ, hx.isOpen_compl⟩
  let aU := (b ⁻¹ᵁ U).ι
  let bU := b ∣_ U
  let : IsClosedImmersion (P.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hdisjoint : Disjoint (U : Set P) ((P.fromSpecResidueField x).ker.support : Set P) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_left.mpr fun y hy hy' => hy hy'
  let : IsIso bU := (pointBlowupDatum P x).restrict_isIso_of_disjoint U hdisjoint
  have haway : IsIso ((Modules.pullback aU).map φ) := by
    change IsIso ((Modules.pullback aU).map (ordinaryTracePullback b τ))
    exact ordinaryTracePullback_isIso_of_isIso_restrict b τ U
  let : IsIso ((Modules.pullback aU).map φ) := haway
  change Epi φ
  exact epi_of_localization_and_away x hx a p b H φ

end AlgebraicGeometry.Scheme.Cohomology
