/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.SerreTransport
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Structural
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.DifferentialTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Higher
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineBase
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Smooth
public import Aglib.AlgebraicGeometry.Modules.Differentials.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient

/-!
# Actual duality on smooth projective field curves

For the original field scheme, a closed projective embedding and smooth relative
dimension one give complementary-degree duality between actual module Ext into
the differential sheaf and the linear dual of actual sheaf cohomology. All
structural field actions and the original geometric direct-image map are retained.

The construction composes the installed closed right-adjoint purity map, closed
adjunction, the ambient differential determinant, and the original projective
Serre pairing. Unary-wedge evaluation and the native affine-base differential
comparison identify its canonical coefficient with `differentialSheaf X`.
The displayed pairing formula retains the original Yoneda product and trace.

Source basis: Aglib `64374534558c80c2fec996ee06bf7727b6c7f3e4`,
`Cohomology/Duality/Projective/Canonical.lean`,
`Canonical/SerreTransport.lean`, `Relative/ClosedEmbedding/Structural.lean`,
`DifferentialTrace.lean`, `Higher.lean`, and
`Cohomology/Projective/ClosedImmersion.lean`. This adapter specializes those
native constructions to relative dimension one over an arbitrary field in
universe `u`, with actual Ext and cohomology in universe `u + 1`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.OverField (FScheme)

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Duality

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

local instance curveDualityHasExt (Z : Scheme.{u}) : HasExt.{u + 1} Z.Modules :=
  HasExt.standard _

/-- Contravariant transport of the actual linear dual, without choosing any basis. -/
def dualTransport {K : Type u} [Field K] {V W : Type (u + 1)}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (E : V ≃ₗ[K] W) : Module.Dual K V ≃ₗ[K] Module.Dual K W where
  toFun f := f.comp E.symm.toLinearMap
  invFun f := f.comp E.toLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl

/-- Standard target-isomorphism transport on the original module Ext group. -/
def extTargetIso {K : Type u} [Field K] (X : Scheme.{u})
    (α : K →+* Γ(X, ⊤)) (M : X.Modules) {N N' : X.Modules}
    (E : N ≅ N') (q : ℕ) :
    letI := moduleCategoryLinearOfHom X α
    Ext.{u + 1} M N q ≃ₗ[K] Ext.{u + 1} M N' q := by
  letI := moduleCategoryLinearOfHom X α
  exact (Ext.homLinearEquiv (R := K) (X := M) (Y := N) (n := q)).trans
    ((RelativeCanonicalReindex.postcompHomLinearEquiv (S := K)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)
      ((shiftFunctor (DerivedCategory X.Modules) (q : ℤ)).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso E))).trans
      (Ext.homLinearEquiv (R := K) (X := M) (Y := N') (n := q)).symm)

/-- Nonemptiness and the already proved local dimension equation give the only bound used. -/
theorem ambientDimension_pos {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    [SmoothOfRelativeDimension 1 (i ≫ toSpec K ι)] (x : X) : 1 ≤ n := by
  let := toSpec_smoothOfRelativeDimension K ι n e
  exact RelativeCanonicalDimension.dimension_le_at_point i (toSpec K ι) n 1 x

/-- Purity, the installed closed adjunction, and the original ambient determinant map.
There is no coherence, presentation, resolution or duality premise. -/
def embeddedCanonicalExt {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    [SmoothOfRelativeDimension 1 (i ≫ toSpec K ι)] (M : X.Modules) (x : X) (r : ℕ) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) αP
    Ext.{u + 1} M
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ toSpec K ι)) 1) r ≃ₗ[K]
      Ext.{u + 1} ((Scheme.Modules.pushforward i).obj M)
        (twistingSheaf K ι (-(Fintype.card ι : ℤ))) (r + (n - 1)) := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace K ι
  let p := toSpec K ι
  let αP := p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
  letI := moduleCategoryLinearOfHom P αP
  letI := toSpec_smoothOfRelativeDimension K ι n e
  have hn := ambientDimension_pos ι n e i x
  let Ω := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) 1
  let C := DerivedCategory.Plus.ι.obj (closedImmersionCanonicalValue i p n)
  let E := DerivedCategory.Plus.ι.mapIso (smoothClosedImmersionCanonicalIso i p n 1)
  let A := RelativeCanonicalReindex.purityInputLinearEquiv (S := K)
    M Ω C ((n : ℤ) - 1) E (r + (n - 1)) r (by omega)
  let B := relativeClosedEmbeddingInputLinearEquiv i αP (relativeCanonicalModule p n)
    M (r + (n - 1))
  let D := extTargetIso P αP ((Scheme.Modules.pushforward i).obj M)
    (differentialResidueTwistingIso K ι n e) (r + (n - 1))
  exact A.trans (B.trans D)

/-- Native coherent ambient Serre duality and the original closed-image H map.
For a curve this covers exactly the complementary pairs (r,s)=(0,1),(1,0). -/
def embeddedSerreDuality {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    [SmoothOfRelativeDimension 1 (i ≫ toSpec K ι)] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (x : X) (r s : ℕ) (hrs : r + s = 1) :
    let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
    letI := moduleCohomologyModuleOfHom X (i.appTop.hom.comp αP) M s
    Ext.{u + 1} M
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ toSpec K ι)) 1) r ≃ₗ[K]
      Module.Dual K (Sheaf.H.{u + 1} (moduleAddSheaf X M) s) := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace K ι
  let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
  letI := moduleCategoryLinearOfHom P αP
  letI := moduleCohomologyModuleOfHom X (i.appTop.hom.comp αP) M s
  letI := moduleCohomologyModuleOfHom P αP ((Scheme.Modules.pushforward i).obj M) s
  have hn := ambientDimension_pos ι n e i x
  have hP :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hM
  letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  letI : ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A j _ => (hP A j).1)
  exact (embeddedCanonicalExt ι n e i M x r).trans
    ((projectiveSerreDuality K ι n e ((Scheme.Modules.pushforward i).obj M) hP
      s (r + (n - 1)) (by omega)).trans
      (dualTransport (projectiveEmbeddingCohomologyLinearEquiv K ι i M s)))

/-- The transported pairing is literally the original ambient Yoneda product,
module-Ext/cohomology comparison and normalized projective trace. -/
theorem embeddedSerreDuality_apply {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    [SmoothOfRelativeDimension 1 (i ≫ toSpec K ι)] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (x : X) (r s : ℕ) (hrs : r + s = 1)
    (β : Ext.{u + 1} M
      (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ toSpec K ι)) 1) r)
    (z : Sheaf.H.{u + 1} (moduleAddSheaf X M) s) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) αP
    letI := moduleCohomologyModuleOfHom X (i.appTop.hom.comp αP) M s
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) αP
      ((Scheme.Modules.pushforward i).obj M) s
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    let hP :=
      Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hM
    letI : ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent :=
      quasicoherent_of_affineCharts _ (fun A j _ => (hP A j).1)
    embeddedSerreDuality ι n e i M hM x r s hrs β z =
      projectiveTrace K ι n e
        (moduleExtCohomologyMap (ProjectiveSpace K ι)
          (twistingSheaf K ι (-(Fintype.card ι : ℤ))) n
          (((moduleExtCohomologyAddEquiv (ProjectiveSpace K ι)
              ((Scheme.Modules.pushforward i).obj M) s).symm
              ((projectiveEmbeddingCohomologyLinearEquiv K ι i M s).symm z)).comp
            (embeddedCanonicalExt ι n e i M x r β)
            (by have hn := ambientDimension_pos ι n e i x; omega))) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace K ι
  let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp αP)
  let := moduleCategoryLinearOfHom P αP
  let := moduleCohomologyModuleOfHom X (i.appTop.hom.comp αP) M s
  let := moduleCohomologyModuleOfHom P αP ((Scheme.Modules.pushforward i).obj M) s
  have hn := ambientDimension_pos ι n e i x
  have hP :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hM
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let : ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A j _ => (hP A j).1)
  change projectiveSerreDuality K ι n e ((Scheme.Modules.pushforward i).obj M) hP
      s (r + (n - 1)) (by omega) (embeddedCanonicalExt ι n e i M x r β)
      ((projectiveEmbeddingCohomologyLinearEquiv K ι i M s).symm z) = _
  exact projectiveSerreDuality_apply K ι n e ((Scheme.Modules.pushforward i).obj M) hP
    s (r + (n - 1)) (by omega) (embeddedCanonicalExt ι n e i M x r β)
    ((projectiveEmbeddingCohomologyLinearEquiv K ι i M s).symm z)

/-- The affine-base constants and the old field constants are the same actual arrows. -/
theorem affineBaseConstants_eq_fieldConstants {K : Type u} [Field K] (X : FScheme K) :
    affineBaseConstants X.hom = constantsPresheafMap X := by
  ext U a
  rfl

/-- The native relative/constant-base comparison reaches the old field differential sheaf. -/
def relativeFieldDifferentialIso {K : Type u} [Field K] (X : FScheme K) :
    relativeDifferentialSheaf X.hom ≅ differentialSheaf X := by
  simpa only [affineBaseDifferentialSheaf, affineBaseConstants_eq_fieldConstants,
    differentialSheaf, differentialPresheaf] using
      relativeDifferentialSheafAffineBaseIso X.hom

/-- Canonical unary-wedge evaluation on the original module presheaf. -/
def exteriorOnePresheafIso (X : Scheme.{u}) (M : X.Modules) :
    PresheafOfModulesOfCommRing.exteriorPower (R := X.presheaf) M.val 1 ≅ M.val :=
  PresheafOfModulesOfCommRing.isoMk
    (fun U => ModuleCat.exteriorPower.iso₁ (R := X.presheaf.obj U) (M.val.obj U)) (by
    intro U V f
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro s
    change (ModuleCat.exteriorPower.iso₁ (R := X.presheaf.obj V) (M.val.obj V)).hom.hom
        ((PresheafOfModulesOfCommRing.exteriorPower (R := X.presheaf) M.val 1).map f
          (ModuleCat.exteriorPower.mk s)) =
      M.val.map f ((ModuleCat.exteriorPower.iso₁ (R := X.presheaf.obj U) (M.val.obj U)).hom.hom
        (ModuleCat.exteriorPower.mk s))
    rw [PresheafOfModulesOfCommRing.exteriorPower_map_mk]
    change _root_.exteriorPower.oneEquiv (X.presheaf.obj V) (M.val.obj V)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj V) 1 (fun j => M.val.map f (s j))) =
      M.val.map f (_root_.exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) 1 s))
    simp only [_root_.exteriorPower.oneEquiv_ιMulti])

/-- The original sheafification and its counit turn unary wedge evaluation into an iso. -/
def exteriorOneIso (X : Scheme.{u}) (M : X.Modules) : moduleExteriorPower X M 1 ≅ M :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorOnePresheafIso X M) ≪≫ sheafifyForgetIso X M


/-- On every original wedge, unary sheaf evaluation is exactly evaluation at the one index. -/
theorem exteriorOneIso_hom_wedge (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opensᵒᵖ) (s : Fin 1 → M.val.obj U) :
    (exteriorOneIso X M).hom.val.app U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M 1).app U s) = s 0 := by
  let P := PresheafOfModulesOfCommRing.exteriorPower (R := X.presheaf) M.val 1
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he : adj.homEquiv P M (exteriorOneIso X M).hom =
      (exteriorOnePresheafIso X M).hom := by
    change adj.homEquiv P M
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (exteriorOnePresheafIso X M).hom ≫ adj.counit.app M) = _
    rw [← adj.homEquiv_counit]
    exact (adj.homEquiv P M).apply_symm_apply _
  have hh := congrArg
    (fun a : P ⟶ M.val => a.app U (ModuleCat.exteriorPower.mk (R := X.presheaf.obj U) s)) he
  change (exteriorOneIso X M).hom.val.app U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M 1).app U s) =
    (ModuleCat.exteriorPower.iso₁ (R := X.presheaf.obj U) (M.val.obj U)).hom.hom
      (ModuleCat.exteriorPower.mk s) at hh
  change _ = _root_.exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)
    (_root_.exteriorPower.ιMulti (X.presheaf.obj U) 1 s) at hh
  simpa only [_root_.exteriorPower.oneEquiv_ιMulti] using hh

/-- The canonical comparison with the old actual field differential sheaf. -/
def actualCanonicalModuleIso {K : Type u} [Field K] (X : FScheme K) :
    moduleExteriorPower X.left (relativeDifferentialSheaf X.hom) 1 ≅ differentialSheaf X :=
  exteriorOneIso X.left (relativeDifferentialSheaf X.hom) ≪≫ relativeFieldDifferentialIso X

/-- Conditional original-object transport, used below with the constructed canonical comparison. -/
def actualCanonicalExtDualityOfComparison {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (X : FScheme K)
    (i : X.left ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    (hbase : i ≫ toSpec K ι = X.hom) (hsmooth : SmoothOfRelativeDimension 1 X.hom)
    (EΩ : moduleExteriorPower X.left (relativeDifferentialSheaf X.hom) 1 ≅ differentialSheaf X)
    (M : X.left.Modules) (hM : affineLocallyFiniteType X.left M) (x : X.left)
    (r s : ℕ) (hrs : r + s = 1) :
    letI := moduleCategoryLinearOfHom X.left (AlgebraicGeometry.Scheme.constants X)
    Ext.{u + 1} M (differentialSheaf X) r ≃ₗ[K]
      Module.Dual K (moduleCohomology K X M s) := by
  let αP := (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hα : i.appTop.hom.comp αP = AlgebraicGeometry.Scheme.constants X := by
    rw [← projectiveEmbedding_structuralScalars K ι i, hbase]
    rfl
  letI := moduleCategoryLinearOfHom X.left (AlgebraicGeometry.Scheme.constants X)
  letI : SmoothOfRelativeDimension 1 (i ≫ toSpec K ι) := by
    rw [hbase]
    exact hsmooth
  let EΩ' : moduleExteriorPower X.left
      (relativeDifferentialSheaf (i ≫ toSpec K ι)) 1 ≅ differentialSheaf X := by
    simpa only [hbase] using EΩ
  have D : Ext.{u + 1} M
      (moduleExteriorPower X.left (relativeDifferentialSheaf (i ≫ toSpec K ι)) 1) r ≃ₗ[K]
      Module.Dual K (moduleCohomology K X M s) := by
    have D := embeddedSerreDuality ι n e i M hM x r s hrs
    dsimp only at D
    dsimp only [αP] at hα
    rw [hα] at D
    exact D
  exact (extTargetIso X.left (AlgebraicGeometry.Scheme.constants X) M EΩ'.symm r).trans D

/-- The original actual differential sheaf has complementary-degree duality;
all comparisons are now constructed, with no EΩ premise. -/
def actualCanonicalExtDuality {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (X : FScheme K)
    (i : X.left ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    (hbase : i ≫ toSpec K ι = X.hom) (hsmooth : SmoothOfRelativeDimension 1 X.hom)
    (M : X.left.Modules) (hM : affineLocallyFiniteType X.left M) (x : X.left)
    (r s : ℕ) (hrs : r + s = 1) :
    letI := moduleCategoryLinearOfHom X.left (AlgebraicGeometry.Scheme.constants X)
    Ext.{u + 1} M (differentialSheaf X) r ≃ₗ[K]
      Module.Dual K (moduleCohomology K X M s) :=
  actualCanonicalExtDualityOfComparison ι n e X i hbase hsmooth (actualCanonicalModuleIso X)
    M hM x r s hrs

/-- Both required actual canonical cohomology identities follow from M=O.
No endomorphism comparison or additional invertible-tensor argument is required. -/
def actualCanonicalCohomologyDuality {K : Type u} [Field K] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (X : FScheme K)
    (i : X.left ⟶ ProjectiveSpace K ι) [IsClosedImmersion i]
    (hbase : i ≫ toSpec K ι = X.hom) (hsmooth : SmoothOfRelativeDimension 1 X.hom)
    (x : X.left) (r s : ℕ) (hrs : r + s = 1) :
    moduleCohomology K X (differentialSheaf X) r ≃ₗ[K]
      Module.Dual K (AlgebraicGeometry.Scheme.structureCohomology K X s) := by
  letI := moduleCategoryLinearOfHom X.left (AlgebraicGeometry.Scheme.constants X)
  let O : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  let A : Ext.{u + 1} O (differentialSheaf X) r ≃ₗ[K]
      moduleCohomology K X (differentialSheaf X) r :=
    moduleExtCohomologyLinearEquivOfCategory X.left (AlgebraicGeometry.Scheme.constants X)
      (differentialSheaf X) r
  exact A.symm.trans
    ((actualCanonicalExtDuality ι n e X i hbase hsmooth O (affineLocallyFiniteType_unit X.left)
      x r s hrs).trans (dualTransport (structureModuleCohomologyEquiv X s)))


end AlgebraicGeometry.Scheme.OverField.Curve.Duality
