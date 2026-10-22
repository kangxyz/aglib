/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Invertible
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.NegativeDegree
public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Intrinsic sections with poles at an original rational point

The modules are the actual tensor powers of the dual of the original point
ideal. Their positive section is the native transpose of the kernel-ideal
inclusion. Proper curve duality proves vanishing over the original field;
Riemann–Roch gives the dimensions. No group law or representing Picard
scheme is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k]

private theorem integral (X : FScheme k) (hX : Properties X) : IsIntegral X.left := by
  let := hX.smooth
  let := hX.connected
  let : GeometricallyIntegral X.hom :=
    Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected X.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

private theorem closedDVR (X : FScheme k) (hX : Properties X) [IsIntegral X.left]
    (x : Scheme.ClosedPoint X.left) :
    IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := by
  let := hX.smooth
  have h : SmoothOfRelativeDimension 1 (𝟙 X.left ≫ X.hom) := by
    simpa only [Category.id_comp] using hX.smooth
  let := h
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 X.left) X.hom x.val x.property

/-- The actual kernel ideal of the original rational point, with its proved
Cartier rank-one property. -/
def idealLineBundle (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : LineBundle X.left := by
  let := hX.smooth
  let := hX.proper
  exact ⟨Scheme.Hom.idealModule p,
    Scheme.Hom.sectionIdeal_isLocallyRankOne Scheme.Hom.smoothRelativeDivisorIdeal X.hom p hp⟩

/-- The original positive point module O(p), namely the actual dual ideal. -/
def positiveLineBundle (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : LineBundle X.left :=
  dualLineBundle X.left (idealLineBundle X hX p hp)

/-- The native tensor-power model of O(np), including its canonical zero power. -/
def poleLineBundle (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) : LineBundle X.left :=
  tensorPowerLineBundle X.left (positiveLineBundle X hX p hp) n

/-- The original constant-one section O -> O(p) is the canonical transpose
of the original kernel-ideal inclusion. -/
def positiveSection (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (show X.left.Modules from SheafOfModules.unit X.left.ringCatSheaf) ⟶
      (show X.left.Modules from (positiveLineBundle X hX p hp).val) :=
  Scheme.Modules.InternalHom.transpose X.left (Scheme.Hom.idealInclusion p)

private theorem tensorRight_faithful (Y : Scheme.{u}) (L : LineBundle Y) :
    (tensorRight (C := Y.Modules) L.val).Faithful := by
  let : (tensorLeft (C := Y.Modules) L.val).Faithful :=
    inferInstanceAs ((lineBundleDualTensorEquivalence Y L).inverse.Faithful)
  exact Functor.Faithful.of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (C := Y.Modules) L.val)

private theorem tensorRight_preservesMonomorphisms (Y : Scheme.{u}) (L : LineBundle Y) :
    (tensorRight (C := Y.Modules) L.val).PreservesMonomorphisms := by
  let : (tensorLeft (C := Y.Modules) L.val).PreservesMonomorphisms :=
    inferInstanceAs ((lineBundleDualTensorEquivalence Y L).inverse.PreservesMonomorphisms)
  exact Functor.PreservesMonomorphisms.of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (C := Y.Modules) L.val)

instance positiveSectionMono (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Mono (positiveSection X hX p hp) := by
  let I := idealLineBundle X hX p hp
  let F := tensorRight (C := X.left.Modules) I.val
  let : F.Faithful := tensorRight_faithful X.left I
  have hEq : F.map (positiveSection X hX p hp) ≫ (dualEvaluationIso X.left I).hom =
      (tensorSheafLeftUnit X.left I.val).hom ≫ Scheme.Hom.idealInclusion p :=
    Scheme.Modules.InternalHom.transpose_dualEvaluation X.left I (Scheme.Hom.idealInclusion p)
  have ht : Mono (F.map (positiveSection X hX p hp) ≫ (dualEvaluationIso X.left I).hom) := by
    rw [hEq]
    infer_instance
  have : Mono (F.map (positiveSection X hX p hp)) :=
    mono_of_mono _ (dualEvaluationIso X.left I).hom
  exact F.mono_of_mono_map inferInstance

/-- The canonical map O(np) -> O((n+1)p) tensors the original positive
section with the identity of the actual nth power. -/
def inclusion (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    (show X.left.Modules from (poleLineBundle X hX p hp n).val) ⟶
      (show X.left.Modules from (poleLineBundle X hX p hp (n + 1)).val) :=
  (tensorSheafLeftUnit X.left (poleLineBundle X hX p hp n).val).inv ≫
    tensorSheafMap X.left (positiveSection X hX p hp)
      (𝟙 (poleLineBundle X hX p hp n).val)

instance inclusionMono (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    Mono (inclusion X hX p hp n) := by
  let L := poleLineBundle X hX p hp n
  let : (tensorRight (C := X.left.Modules) L.val).PreservesMonomorphisms :=
    tensorRight_preservesMonomorphisms X.left L
  have : Mono ((tensorRight (C := X.left.Modules) L.val).map
      (positiveSection X hX p hp)) := inferInstance
  exact inferInstanceAs (Mono ((tensorSheafLeftUnit X.left L.val).inv ≫
    (tensorRight (C := X.left.Modules) L.val).map (positiveSection X hX p hp)))

/-- The original global-section space, with scalars from X's structural map. -/
abbrev sections (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :=
  (poleLineBundle X hX p hp n).val.val.obj (op ⊤)

/-- The actual induced map on sections, linear for the original field action. -/
def sectionsInclusion (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    sections X hX p hp n →ₗ[k] sections X hX p hp (n + 1) where
  toFun := (inclusion X hX p hp n).val.app (op ⊤)
  map_add' a b := map_add _ a b
  map_smul' a b := by
    change (inclusion X hX p hp n).val.app (op ⊤) (Scheme.constants X a • b) =
      Scheme.constants X a • (inclusion X hX p hp n).val.app (op ⊤) b
    exact ((inclusion X hX p hp n).val.app (op ⊤)).hom.map_smul _ _

theorem sectionsInclusion_injective (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    Function.Injective (sectionsInclusion X hX p hp n) :=
  moduleHom_app_injective (inclusion X hX p hp n) ⊤

private theorem power_degree (X : FScheme k) (hX : Properties X)
    [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom) (n : ℕ) :
    Picard.Degree.lineBundleDegree X.left X.hom hdim hprod (poleLineBundle X hX p hp n) = n := by
  let := hX.proper
  have : IsClosedImmersion (p ≫ X.hom) := by rw [hp]; infer_instance
  have : IsClosedImmersion p := IsClosedImmersion.of_comp p X.hom
  have : IsFinite (p ≫ X.hom) := by rw [hp]; infer_instance
  have hdeg := Abel.FiniteCartierDegree.finiteCartierIdealDegree k X.left (Spec (.of k))
    X.hom p hdim hprod (idealLineBundle X hX p hp).property
    hX.proper inferInstance inferInstance
  rw [hp, Scheme.Hom.finiteSchemeDegree_id] at hdeg
  change Picard.Degree.lineBundleDegree X.left X.hom hdim hprod
    (positiveLineBundle X hX p hp) = 1 at hdeg
  induction n with
  | zero => exact Picard.Degree.lineBundleDegree_trivial X.left X.hom hdim hprod
  | succ n ih =>
    change Picard.Degree.lineBundleDegree X.left X.hom hdim hprod
      (tensorLineBundle X.left (positiveLineBundle X hX p hp) (poleLineBundle X hX p hp n)) = _
    rw [Picard.Degree.lineBundleDegree_tensor, ih, hdeg]
    omega

private theorem smooth_highDegree_vanishing
    (X : FScheme k) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left = 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom)
    (L : LineBundle X.left) (hsmooth : SmoothOfRelativeDimension 1 X.hom)
    (hp : IsProper X.hom) (hc : Function.Bijective (Scheme.constants X))
    (hL : 2 * (coherentGenus k X : ℤ) - 1 ≤
      Picard.Degree.lineBundleDegree X.left X.hom hdim.le hprod L) :
    Subsingleton (moduleCohomology k X L.val 1) := by
  let := hp
  let N := tensorLineBundle X.left (canonicalLineBundle X hsmooth) (dualLineBundle X.left L)
  have hN : Picard.Degree.lineBundleDegree X.left X.hom hdim.le hprod N < 0 := by
    dsimp only [N]
    rw [Picard.Degree.lineBundleDegree_tensor, Picard.Degree.lineBundleDegree_dual,
      smoothCanonicalDegree k X hdim.le hprod hsmooth hp hc]
    omega
  have := lineBundleH0_subsingleton_of_neg_degree X hdim.le hprod N hN
  let := moduleCategoryLinearOfHom X.left (Scheme.constants X)
  let E : Ext.{u + 1} (C := X.left.Modules) L.val (differentialSheaf X) 0 ≃ₗ[k]
      moduleCohomology k X N.val 0 := lineBundleExtZeroEquivH0 X L (differentialSheaf X)
  have : Subsingleton (Ext.{u + 1} (C := X.left.Modules) L.val (differentialSheaf X) 0) :=
    E.injective.subsingleton
  obtain ⟨n, i, hi, hbase⟩ := Projectivity.exists_projectiveEmbedding X hdim
  let := hi
  have hM : affineLocallyFiniteType X.left L.val :=
    (affineLocallyFiniteType_iff_finitePresentation L.val).mpr
      (lineBundle_isFinitePresentation X.left L)
  let D := Duality.actualCanonicalExtDuality _ n Equiv.ulift X i hbase hsmooth
    L.val hM (genericPoint X.left) 0 1 (by omega)
  have : Subsingleton (Module.Dual k (moduleCohomology k X L.val 1)) :=
    D.symm.injective.subsingleton
  let : Module.Projective k (moduleCohomology k X L.val 1) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace k (moduleCohomology k X L.val 1))
  exact (Module.subsingleton_dual_iff k).mp inferInstance

/-- Over the original arbitrary field, H1(O(np)) vanishes for every positive n,
and the original H0 has dimension n. -/
theorem cohomology (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) :
    Subsingleton (moduleCohomology k X (poleLineBundle X hX p hp n).val 1) ∧
      Module.finrank k (moduleCohomology k X (poleLineBundle X hX p hp n).val 0) = n := by
  let : IsIntegral X.left := integral X hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let := hX.proper
  have (x : Scheme.ClosedPoint X.left) :
      IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := closedDVR X hX x
  have hdim := curveProperties_dimension Scheme.smoothFieldDimension hX
  let hprod := Picard.Degree.properCurveProductFormula k X.left X.hom hdim
  let : GeometricallyIntegral X.hom := by
    let := hX.smooth
    let := hX.connected
    exact Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected
      X.hom
  have hc := Scheme.constants_bijective_of_proper_geometricallyIntegral X
  have hdeg := power_degree X hX p hp hdim.le hprod n
  have hz := smooth_highDegree_vanishing X hdim hprod (poleLineBundle X hX p hp n)
    hX.smooth hX.proper hc (by rw [hg, hdeg]; omega)
  let := hz
  refine ⟨hz, ?_⟩
  have hrr := lineBundleRiemannRoch k X hdim.le hprod (poleLineBundle X hX p hp n) hX.proper hc
  have hzdim : Module.finrank k (moduleCohomology k X (poleLineBundle X hX p hp n).val 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hdeg, hg, hzdim] at hrr
  omega

/-- The dimension statement on the actual global-section module. -/
theorem sections_finrank (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) :
    Module.finrank k (sections X hX p hp n) = n :=
  (moduleH0Equiv X (poleLineBundle X hX p hp n).val).finrank_eq.symm.trans
    (cohomology X hX p hp hg n hn).2

/-- Canonical identification of the first native tensor power with O(p). -/
def firstPowerIso (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (show X.left.Modules from (poleLineBundle X hX p hp 1).val) ≅
      (show X.left.Modules from (positiveLineBundle X hX p hp).val) :=
  tensorSheafIso X.left (Iso.refl _) (Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)) ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso X.left.sheaf).app _

/-- The original constant one in the first pole space, transported only by
its canonical native tensor-unit comparison. -/
def oneSection (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : sections X hX p hp 1 :=
  (firstPowerIso X hX p hp).inv.val.app (op ⊤)
    ((positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤)))

@[simp] theorem firstPowerIso_oneSection (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (firstPowerIso X hX p hp).hom.val.app (op ⊤) (oneSection X hX p hp) =
      (positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤)) := by
  change ((firstPowerIso X hX p hp).inv ≫ (firstPowerIso X hX p hp).hom).val.app (op ⊤) _ = _
  rw [Iso.inv_hom_id]
  rfl

/-- Under the actual internal-Hom model, constant one acts on the original
point ideal by its original inclusion into the structure module. -/
theorem oneSection_evaluate (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (m : (Scheme.Hom.idealModule p).val.obj (op ⊤)) :
    ((firstPowerIso X hX p hp).hom.val.app (op ⊤) (oneSection X hX p hp)).val.app
      (op (Over.mk (𝟙 (⊤ : X.left.Opens)))) m =
      (Scheme.Hom.idealInclusion p).val.app (op ⊤) m := by
  rw [firstPowerIso_oneSection]
  exact Scheme.Modules.InternalHom.transpose_one_evaluate X.left (Scheme.Hom.idealInclusion p) ⊤ m

theorem oneSection_ne_zero (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    oneSection X hX p hp ≠ 0 := by
  let : IsIntegral X.left := integral X hX
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, by trivial⟩⟩
  intro hz
  have h := congrArg ((firstPowerIso X hX p hp).hom.val.app (op ⊤)) hz
  rw [firstPowerIso_oneSection, map_zero] at h
  have he : (1 : Γ(X.left, ⊤)) = 0 :=
    moduleHom_app_injective (positiveSection X hX p hp) ⊤ (h.trans (map_zero _).symm)
  exact one_ne_zero he

/-- The first original pole space is spanned by that actual constant-one
section; no arbitrary choice of vector-space coordinates is involved. -/
theorem oneSection_spans (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    Submodule.span k ({oneSection X hX p hp} : Set (sections X hX p hp 1)) = ⊤ :=
  (finrank_eq_one_iff_of_nonzero (oneSection X hX p hp)
    (oneSection_ne_zero X hX p hp)).mp (sections_finrank X hX p hp hg 1 (by omega))

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
