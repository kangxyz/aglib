/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Stalk
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Coherent homology of the original derived closed right adjoint

The original injective-resolution unit identifies homology of `Ri! (L[0])`
with the original closed-adjoint resolution. Exact open restriction transports
this comparison through the installed derived open isomorphism. The actual
quotient presentation of an affine closed immersion then proves finite
presentation of homology over a locally Noetherian ambient scheme.

No coherence, stalk comparison, concentration, or chosen model is assumed for
the derived object. The coefficient is the original finitely presented ambient
module sheaf. The quotient stalk comparison retains the lower original germ
and exact-functor Ext map. The current consumer is chosen-embedding normal
surface concentration.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived category of module sheaves used for the closed right adjoint. -/
local instance finiteSourceDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- Homology of the original installed closed right adjoint on the original
coefficient in degree zero. -/
abbrev derivedClosedImmersionRightAdjointHomology {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) (n : ℤ) : X.Modules :=
  (DerivedCategory.Plus.homologyFunctor X.Modules n).obj
    ((derivedClosedImmersionRightAdjointPlus i).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj L))

/-- The original resolution unit and the native localization-homology
factorization give the model comparison for any closed immersion. -/
def derivedClosedImmersionRightAdjointModelHomologyIso {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {L : Y.Modules}
    (J : InjectiveResolution L) (n : ℤ) :
    derivedClosedImmersionRightAdjointHomology i L n ≅
      (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex).homology n :=
  ((DerivedCategory.Plus.homologyFunctor X.Modules n).mapIso
      (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint i))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app
      ((closedImmersionRightAdjoint i).mapCochainComplexPlus.obj J.cochainComplexPlus)

/-- The model arrow is the original resolution arrow, with no independent
choice of a derived-object isomorphism. -/
theorem derivedClosedImmersionRightAdjointModelHomologyIso_hom {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {L : Y.Modules}
    (J : InjectiveResolution L) (n : ℤ) :
    (derivedClosedImmersionRightAdjointModelHomologyIso i J n).hom =
      (DerivedCategory.Plus.homologyFunctor X.Modules n).map
        (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint i)).inv ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).hom.app
        ((closedImmersionRightAdjoint i).mapCochainComplexPlus.obj J.cochainComplexPlus) := rfl

/-- Negative homology of the actual derived object vanishes by its
nonnegative injective-resolution model. -/
theorem derivedClosedImmersionRightAdjointHomology_isZero_of_neg {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) (n : ℤ) (hn : n < 0) :
    IsZero (derivedClosedImmersionRightAdjointHomology i L n) := by
  let J := injectiveResolution L
  exact (ShortComplex.isZero_homology_of_isZero_X₂ _
    ((closedImmersionRightAdjoint i).map_isZero
      (J.cochainComplex.isZero_of_isStrictlyGE 0 n hn))).of_iso
        (derivedClosedImmersionRightAdjointModelHomologyIso i J n)

section Open

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion i] [IsClosedImmersion b]
  (h : IsPullback a b i j)

/-- Homology of the actual derived closed right adjoint commutes with the
original open square, through exact restriction and the original derived
open comparison. -/
def derivedClosedImmersionRightAdjointOpenHomologyIso (L : X.Modules) (n : ℤ) :
    (restrictFunctor a).obj (derivedClosedImmersionRightAdjointHomology i L n) ≅
      derivedClosedImmersionRightAdjointHomology b ((restrictFunctor j).obj L) n :=
  (((restrictFunctor a).rightDerivedFunctorPlusHomologyIso n).app
    ((derivedClosedImmersionRightAdjointPlus i).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj L))).symm ≪≫
  (DerivedCategory.Plus.homologyFunctor W.Modules n).mapIso
    ((derivedClosedImmersionRightAdjointOpenIso a b i j h).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj L) ≪≫
    (derivedClosedImmersionRightAdjointPlus b).mapIso
      (((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).app L))

/-- The forward open homology arrow retains all three original comparisons:
exact restriction, the derived open exchange, and the exact-single map. -/
theorem derivedClosedImmersionRightAdjointOpenHomologyIso_hom (L : X.Modules) (n : ℤ) :
    (derivedClosedImmersionRightAdjointOpenHomologyIso a b i j h L n).hom =
      ((restrictFunctor a).rightDerivedFunctorPlusHomologyIso n).inv.app
        ((derivedClosedImmersionRightAdjointPlus i).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj L)) ≫
      (DerivedCategory.Plus.homologyFunctor W.Modules n).map
        ((derivedClosedImmersionRightAdjointOpenIso a b i j h).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj L) ≫
        (derivedClosedImmersionRightAdjointPlus b).map
          (((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).hom.app L)) := rfl

end Open

/-- Changing the source by an actual scheme isomorphism uses the original
open square and the original identity-restriction coefficient comparison. -/
def derivedClosedImmersionRightAdjointSourceIsoHomologyIso
    {X X' Y : Scheme.{u}} (e : X' ≅ X) (i : X ⟶ Y) [IsClosedImmersion i]
    (L : Y.Modules) (n : ℤ) :
    (restrictFunctor e.hom).obj (derivedClosedImmersionRightAdjointHomology i L n) ≅
      derivedClosedImmersionRightAdjointHomology (e.hom ≫ i) L n :=
  derivedClosedImmersionRightAdjointOpenHomologyIso e.hom (e.hom ≫ i) i (𝟙 Y)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) L n ≪≫
    (DerivedCategory.Plus.homologyFunctor X'.Modules n).mapIso
      ((derivedClosedImmersionRightAdjointPlus (e.hom ≫ i)).mapIso
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).mapIso
          (restrictFunctorId.app L)))

section Quotient

variable {R : CommRingCat.{u}} (I : Ideal R) {L : (Spec R).Modules}
  (J : InjectiveResolution L)

/-- The quotient model is a specialization of the original model comparison. -/
def derivedClosedImmersionRightAdjointQuotientHomologyIso (n : ℤ) :
    derivedClosedImmersionRightAdjointHomology
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) L n ≅
      (closedImmersionRightAdjointQuotientResolutionComplex I J).homology n :=
  derivedClosedImmersionRightAdjointModelHomologyIso _ J n

include J in
/-- The original quotient model proves coherence of the actual derived
homology before any concentration calculation. -/
theorem derivedClosedImmersionRightAdjointQuotientHomology_finitePresentation
    [IsNoetherianRing R] [L.IsFinitePresentation] (n : ℤ) :
    (derivedClosedImmersionRightAdjointHomology
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) L n).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation (Spec (.of (R ⧸ I))).ringCatSheaf).prop_of_iso
    (derivedClosedImmersionRightAdjointQuotientHomologyIso I J n).symm
    (closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation_of_coefficient
      I J n)

variable [IsNoetherianRing R] [L.IsQuasicoherent]

/-- The actual derived homology stalk is the original local Ext group.
The resolution-to-derived transport is followed by the normalized original
quotient-germ comparison, and retains the original ambient stalk action. -/
def derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv
    (x : PrimeSpectrum (R ⧸ I)) (n : ℕ) :
    (ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap I x).hom).obj
      ((moduleStalk (Spec (quotientRing I)) x).obj
        (derivedClosedImmersionRightAdjointHomology
          (Spec.map (quotientMap I)) L (n : ℤ))) ≃ₗ[ambientRing I x]
      Ext.{u}
        ((ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap I x).hom).obj
          (ModuleCat.of (sourceRing I x) (sourceRing I x)))
        ((moduleStalk (Spec R) (imagePoint I x)).obj L) n :=
  ((ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap I x).hom).mapIso
      ((moduleStalk (Spec (quotientRing I)) x).mapIso
        (derivedClosedImmersionRightAdjointQuotientHomologyIso I J (n : ℤ)))).toLinearEquiv.trans
    (closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n)

/-- On original section homology, the inverse derived-model map followed by
the derived stalk comparison is exactly the original local Ext arrow. -/
theorem derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv_germ
    (x : PrimeSpectrum (R ⧸ I)) (n : ℕ)
    (s : ((((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology (n : ℤ))) :
    derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv I J x n
      (((moduleStalk (Spec (.of (R ⧸ I))) x).map
        (derivedClosedImmersionRightAdjointQuotientHomologyIso I J (n : ℤ)).inv)
          (closedImmersionQuotientHomologyToStalk I x J n s)) =
      closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n
        (closedImmersionQuotientHomologyToStalk I x J n s) := by
  change closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n
    (((moduleStalk (Spec (.of (R ⧸ I))) x).map
      (derivedClosedImmersionRightAdjointQuotientHomologyIso I J (n : ℤ)).hom)
        (((moduleStalk (Spec (.of (R ⧸ I))) x).map
          (derivedClosedImmersionRightAdjointQuotientHomologyIso I J (n : ℤ)).inv) _)) = _
  let e := (moduleStalk (Spec (.of (R ⧸ I))) x).mapIso
    (derivedClosedImmersionRightAdjointQuotientHomologyIso I J (n : ℤ))
  exact congrArg (closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n)
    (e.toLinearEquiv.apply_symm_apply (closedImmersionQuotientHomologyToStalk I x J n s))

end Quotient

/-- Every affine-target closed immersion is an actual quotient up to its
canonical source isomorphism. Its derived homology is therefore coherent. -/
theorem derivedClosedImmersionRightAdjointHomology_finitePresentation_spec
    {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}}
    (i : X ⟶ Spec R) [IsClosedImmersion i] (L : (Spec R).Modules)
    [L.IsFinitePresentation] (n : ℤ) :
    (derivedClosedImmersionRightAdjointHomology i L n).IsFinitePresentation := by
  obtain ⟨I, e, rfl⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hq : (derivedClosedImmersionRightAdjointHomology q L n).IsFinitePresentation :=
    derivedClosedImmersionRightAdjointQuotientHomology_finitePresentation
      I (injectiveResolution L) n
  let E := derivedClosedImmersionRightAdjointSourceIsoHomologyIso e q L n
  have he := finitePresentation_restrict e.hom (derivedClosedImmersionRightAdjointHomology q L n)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso E he

/-- The genuine finite-presentation conclusion on an arbitrary affine ambient
scheme is transported through its original `isoSpec`. -/
theorem derivedClosedImmersionRightAdjointHomology_finitePresentation_affine
    {X Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) [L.IsFinitePresentation] (n : ℤ) :
    (derivedClosedImmersionRightAdjointHomology i L n).IsFinitePresentation := by
  let e := Scheme.isoSpec Y
  let b := i ≫ e.hom
  let : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hL := finitePresentation_restrict e.inv L
  have hb := derivedClosedImmersionRightAdjointHomology_finitePresentation_spec
    b ((restrictFunctor e.inv).obj L) n
  let E := (restrictFunctorId.app (derivedClosedImmersionRightAdjointHomology i L n)).symm ≪≫
    derivedClosedImmersionRightAdjointOpenHomologyIso (𝟙 X) b i e.inv
      (IsPullback.of_horiz_isIso ⟨by simp [b]⟩) L n
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso E.symm hb

/-- Coherent homology of the original derived closed right adjoint on a
locally Noetherian ambient scheme. The proof is by actual affine restrictions;
no quasicoherence or Ext comparison of the derived output is assumed. -/
theorem derivedClosedImmersionRightAdjointHomology_finitePresentation
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) [L.IsFinitePresentation] (n : ℤ) :
    (derivedClosedImmersionRightAdjointHomology i L n).IsFinitePresentation := by
  apply finitePresentation_of_openCover _ (fun U : Y.affineOpens => i ⁻¹ᵁ U.1)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) i.base.hom)
  intro U
  have hL := finitePresentation_restrict U.1.ι L
  have hU := derivedClosedImmersionRightAdjointHomology_finitePresentation_affine
    (i ∣_ U.1) ((restrictFunctor U.1.ι).obj L) n
  exact (SheafOfModules.isFinitePresentation (i ⁻¹ᵁ U.1).toScheme.ringCatSheaf).prop_of_iso
    (derivedClosedImmersionRightAdjointOpenHomologyIso
      (i ⁻¹ᵁ U.1).ι (i ∣_ U.1) i U.1.ι (isPullback_morphismRestrict i U.1).flip L n).symm hU

/-- The original derived homology has closed ordinary stalk support. -/
theorem derivedClosedImmersionRightAdjointHomology_isClosed_support
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) [L.IsFinitePresentation] (n : ℤ) :
    IsClosed (support (derivedClosedImmersionRightAdjointHomology i L n)) := by
  have := derivedClosedImmersionRightAdjointHomology_finitePresentation i L n
  exact QuasiCoherent.isClosed_support_of_affineLocallyFiniteType
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation _)

/-- An actual quotient chart of a closed immersion over a specified affine
open chart. All comparison data are geometric maps and an actual pullback. -/
structure ClosedImmersionAffineQuotientChart {X Y : Scheme.{u}}
    (i : X ⟶ Y) (R : CommRingCat.{u}) (j : Spec R ⟶ Y) where
  /-- The ideal defining the affine quotient over `Spec R`. -/
  ideal : Ideal R
  /-- The open chart map from the quotient spectrum to the original closed source. -/
  sourceMap : Spec (.of (R ⧸ ideal)) ⟶ X
  isOpenImmersion : IsOpenImmersion sourceMap
  square : IsPullback sourceMap
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal))) i j

attribute [instance] ClosedImmersionAffineQuotientChart.isOpenImmersion

/-- The native pullback and the actual affine closed-immersion quotient
presentation construct the chart; no derived-model premise is supplied. -/
theorem nonempty_closedImmersionAffineQuotientChart {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (R : CommRingCat.{u})
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Nonempty (ClosedImmersionAffineQuotientChart i R j) := by
  obtain ⟨I, e, he⟩ :=
    (IsClosedImmersion.Spec_iff (f := pullback.snd i j)).mp inferInstance
  refine ⟨⟨I, e.inv ≫ pullback.fst i j, inferInstance, ?_⟩⟩
  exact (IsPullback.of_hasPullback i j).of_iso e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (by simpa using he) (by simp) (by simp)

/-- The selected quotient chart comes from the original closed immersion
and the specified actual affine open. -/
def closedImmersionAffineQuotientChart {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (R : CommRingCat.{u})
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    ClosedImmersionAffineQuotientChart i R j :=
  Classical.choice (nonempty_closedImmersionAffineQuotientChart i R j)

namespace ClosedImmersionAffineQuotientChart

variable {X Y : Scheme.{u}} {i : X ⟶ Y} [IsClosedImmersion i]
  {R : CommRingCat.{u}} {j : Spec R ⟶ Y} [IsOpenImmersion j]
  (C : ClosedImmersionAffineQuotientChart i R j)

omit [IsClosedImmersion i] [IsOpenImmersion j] in
/-- The actual quotient chart contains every source point above its ambient
chart; the original ambient point is retained. -/
theorem exists_point (x : X) (y : Spec R) (hxy : i x = j y) :
    ∃ z : Spec (.of (R ⧸ C.ideal)), C.sourceMap z = x ∧
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))) z = y :=
  exists_preimage_of_isPullback C.square x y hxy

/-- The original stalk of derived homology is its literal quotient-chart
stalk, via the original open stalk map and derived open exchange. -/
def homologyStalkIso (L : Y.Modules) (n : ℤ)
    (z : Spec (.of (R ⧸ C.ideal))) :
    (stalkFunctor X (C.sourceMap z)).obj
        (derivedClosedImmersionRightAdjointHomology i L n) ≅
      (stalkFunctor (Spec (.of (R ⧸ C.ideal))) z).obj
        (derivedClosedImmersionRightAdjointHomology
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal)))
          ((restrictFunctor j).obj L) n) :=
  ((restrictStalkNatIso C.sourceMap z).app
    (derivedClosedImmersionRightAdjointHomology i L n)).symm ≪≫
    (stalkFunctor (Spec (.of (R ⧸ C.ideal))) z).mapIso
      (derivedClosedImmersionRightAdjointOpenHomologyIso C.sourceMap
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))) i j C.square L n)

end ClosedImmersionAffineQuotientChart

end AlgebraicGeometry.Scheme.Modules
