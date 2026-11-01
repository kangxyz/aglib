/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.RingTheory.RootsOfUnity.Galois
public import Aglib.GroupCohomology.H1.Continuous
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedComparisonTransport

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Kummer.RootStalk` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b06760dde6fdaaf62775c1e5fba02e5e9a3ccb53ef4d2173b22bdfb39130f986`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/- Current interface migration: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Original mathematical and construction provenance is retained below.
Previous validation is historical; new-interface validation is pending. -/

/-!
# Actual etale root stalks and the supplied weight-one coefficients

C4/C5 support, `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The actual represented mu_n sheaf on Spec K has its literal geometric stalk
identified with the existing FiniteCoefficients.Mu by A's proved germ
isomorphism, C's actual scheme representation of roots and the canonical
Gamma(Spec)-isomorphism. The characteristic-zero, positive-level assumptions
prove actual etaleness through the constructed polynomial model.

The stalk action reuses intrinsic fibre evaluation, restricted along the actual
field fundamental-group equivalence. Its scalar value is proved equal to the
original additive marking and to precomposition by the actual Galois point automorphism.
Evaluation
of the existing field fundamental-group equivalence. Thus equivariance is
anchored to the actual scheme/stalk action, not merely a transported action
asserted to be monodromy. The induced continuous coefficient map and its
composite with the existing RootCup map use the existing Mu and tensor square.
No new standard family, classification, root-torsor identity or Bockstein
normalization is assumed. The latter actual torsor/sign applications remain
separate obligations. No weight-one/arithmetic-weight-two identification is
made here; tensoring uses a specified actual invariant base-field root.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
namespace GroupCohomology.Kummer.RootStalk
universe u
variable (K : Type u) [Field K] (n : ℕ)
/-- The commutative group structure on the root scheme over `Spec K`. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of K)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of K)) n

/-- Geometric sections of the root group scheme as roots of unity in the algebraic closure. -/
def sectionRootsEquiv :
    RepresentedSections (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (Over.mk
        (geometricPoint K)) ≃+
      Field.absoluteGaloisGroup.RootsOfUnity.Mu K n :=
  AddEquiv.ulift.trans ((GroupCohomology.Kummer.Coefficients.rootsMulEquiv
      (Spec (.of K)) n (Over.mk (geometricPoint K))).toAdditive.trans
    (((Scheme.ΓSpecIso (.of (AlgebraicClosure
        K))).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n).toAdditive))

@[simp] theorem sectionRootsEquiv_apply (p : Over.mk (geometricPoint K) ⟶
    MultiplicativeGroup.rootsScheme (Spec (.of K)) n) :
    ((sectionRootsEquiv K n (ULift.up (Additive.ofMul p))).toMul.val : AlgebraicClosure K) =
      (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
        ((MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ p).val.val) := rfl

theorem sectionRootsEquiv_galois (σ : Field.absoluteGaloisGroup K)
    (p : Over.mk (geometricPoint K) ⟶
      MultiplicativeGroup.rootsScheme (Spec (.of K)) n) :
    sectionRootsEquiv K n (ULift.up (Additive.ofMul
      (pointEnd K σ ≫ p))) =
      σ • sectionRootsEquiv K n (ULift.up (Additive.ofMul p)) := by
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  change (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
    (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _
      (pointEnd K σ ≫ p)).val.val =
    (asAutomorphism K σ) ((Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
      (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ p).val.val)
  have h := (MultiplicativeGroup.rootsRepresentable (Spec (.of K)) n).homEquiv_comp
    (pointEnd K σ) p
  have hval := congrArg (fun z : rootsOfUnity n Γ(Spec (.of (AlgebraicClosure K)), ⊤) =>
    (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom (z.val : Γ(Spec (.of (AlgebraicClosure
        K)), ⊤))) h
  change _ = (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
    ((Spec.map (CommRingCat.ofHom (asAutomorphism K σ).toRingHom)).appTop.hom
      ((MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ p).val.val)) at hval
  exact hval.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (asAutomorphism K σ).toRingHom))
    ((MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ p).val.val))

variable [CharZero K] [NeZero n]
theorem levelInvertible : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
  have hn : IsUnit (n : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (.of K)).inv.hom

local instance rootsEtale : Etale (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n).X.hom :=
  RootsFiniteEtale.rootsScheme_etale _ n (NeZero.pos n) (levelInvertible K n)

/-- The geometric stalk of the `n`th-root coefficient sheaf at the algebraic-closure point. -/
abbrev stalk := ((Scheme.pointSmallEtale (geometricPoint K)).sheafFiber
  (A := AddCommGrpCat.{u + 1})).obj (GroupCohomology.Kummer.Coefficients.mu
      (Spec (.of K)) n)

/-- The additive marking of the geometric root stalk by roots of unity in the algebraic closure. -/
def stalkMarking : stalk K n ≃+ Field.absoluteGaloisGroup.RootsOfUnity.Mu K n :=
  (representedFiberIso (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K))
      n)).addCommGroupIsoToAddEquiv.trans
    (sectionRootsEquiv K n)

local instance rootsFinite : IsFinite (MultiplicativeGroup.rootsGroupScheme (Spec (.of K))
    n).X.hom :=
  RootsFiniteEtale.rootsScheme_finite _ n (NeZero.pos n)

/-- The actual root sheaf has this literal represented coefficient realization. -/
def rootRepresentation : CoefficientRepresentation
    (GroupCohomology.Kummer.Coefficients.mu (Spec (.of K)) n) where
  group := MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n
  finite := inferInstance
  etale := inferInstance
  commutative := inferInstance
  iso := Iso.refl _

/-- The selected root representative has the original actual stalk evaluation map. -/
theorem rootRepresentation_fiberPointEquiv (a : stalk K n) :
    (rootRepresentation K n).fiberPointEquiv (geometricPoint K) a =
      (representedFiberEvaluation (geometricPoint K)
        (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a).down := by
  rw [CoefficientRepresentation.fiberPointEquiv_apply]
  let F := (Scheme.pointSmallEtale (geometricPoint K)).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  have hi : F.map (rootRepresentation K n).iso.inv a = a :=
    ConcreteCategory.congr_hom (F.map_id _) a
  rw [hi]
  rfl

/-- The root stalk uses the selected intrinsic actual fibre action, restricted along
its original field fundamental-group equivalence. -/
@[instance_reducible] def intrinsicStalkGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup K) (stalk K n) := by
  letI := MarkedComparisonTransport.stalkEvaluationAction (geometricPoint K)
    (rootRepresentation K n)
  exact DistribMulAction.compHom (stalk K n)
    (fundamentalGroupContinuousEquiv K).toMonoidHom

/-- The root-stalk Galois action reuses its actual intrinsic fibre evaluation. -/
@[instance_reducible] def stalkGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup K) (stalk K n) :=
  intrinsicStalkGaloisAction K n

/-- The intrinsic action evaluates through the original actual Galois point morphism. -/
theorem stalkGaloisAction_intrinsic_evaluation
    (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    representedFiberEvaluation (geometricPoint K)
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (σ • a) =
    representedSectionsPullback (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
      (pointEnd K σ)
      (representedFiberEvaluation (geometricPoint K)
        (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a) := by
  letI := stalkGaloisAction K n
  have hp := MarkedComparisonTransport.stalkEvaluation_points (geometricPoint K)
    (rootRepresentation K n) (fundamentalGroupContinuousEquiv K σ) a
  change (rootRepresentation K n).fiberPointEquiv (geometricPoint K) (σ • a) = _ at hp
  rw [rootRepresentation_fiberPointEquiv, rootRepresentation_fiberPointEquiv] at hp
  apply ULift.ext
  exact hp


theorem stalkMarking_galois (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    stalkMarking K n (σ • a) = σ • stalkMarking K n a := by
  letI := stalkGaloisAction K n
  change sectionRootsEquiv K n (representedFiberEvaluation (geometricPoint K)
    (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (σ • a)) = _
  rw [stalkGaloisAction_intrinsic_evaluation]
  exact sectionRootsEquiv_galois K n σ
    (representedFiberEvaluation (geometricPoint K)
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a).down.toMul

/-- The selected intrinsic action has exactly the original root-marked scalar value. -/
theorem stalkGaloisAction_smul_eq_original (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    σ • a = (stalkMarking K n).symm (σ • stalkMarking K n a) := by
  letI := stalkGaloisAction K n
  exact (stalkMarking K n).injective
    ((stalkMarking_galois K n σ a).trans ((stalkMarking K n).apply_symm_apply _).symm)

theorem stalkGaloisAction_evaluation (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    representedFiberEvaluation (geometricPoint K)
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (σ • a) =
    representedSectionsPullback (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
      (pointEnd K σ)
      (representedFiberEvaluation (geometricPoint K)
        (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a) := by
  letI := stalkGaloisAction K n
  apply (sectionRootsEquiv K n).injective
  exact (stalkMarking_galois K n σ a).trans
    (sectionRootsEquiv_galois K n σ
      (representedFiberEvaluation (geometricPoint K)
        (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a).down.toMul).symm

/-- The finite etale roots-of-unity scheme over a characteristic-zero field at nonzero level. -/
def rootsCover : Scheme.FiniteEtale (Spec (.of K)) :=
  ⟨(MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n).X, by constructor <;> infer_instance⟩

theorem stalkGaloisAction_fiberAut (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    (representedFiberEvaluation (geometricPoint K)
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (σ • a)).down.toMul =
    (fundamentalGroupContinuousEquiv K σ).hom.app
      (rootsCover K n)
      (representedFiberEvaluation (geometricPoint K)
        (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a).down.toMul := by
  letI := stalkGaloisAction K n
  exact congrArg (fun x => x.down.toMul) (stalkGaloisAction_evaluation K n σ a)

/-- The retained public action is literally the selected intrinsic action. -/
theorem stalkGaloisAction_eq_intrinsic :
    stalkGaloisAction K n = intrinsicStalkGaloisAction K n := rfl

/-- The literal finite stalk is equipped with its discrete topology. -/
instance stalkTopology : TopologicalSpace (stalk K n) := ⊥
instance stalkDiscreteTopology : DiscreteTopology (stalk K n) := ⟨rfl⟩

/-- The Galois action on the root stalk transported through its root-evaluation marking. -/
local instance : DistribMulAction (Field.absoluteGaloisGroup K) (stalk K n) :=
  stalkGaloisAction K n

instance stalkContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup K) (stalk K n) where
  continuous_smul := by
    have he : (fun p : Field.absoluteGaloisGroup K × stalk K n => p.1 • p.2) =
        (fun p => (stalkMarking K n).symm (p.1 • stalkMarking K n p.2)) :=
      funext (fun p => stalkGaloisAction_smul_eq_original K n p.1 p.2)
    rw [he]
    exact continuous_of_discreteTopology.comp
      (continuous_fst.smul (continuous_of_discreteTopology.comp continuous_snd))

/-- The literal root evaluation is a continuous equivariant map into the
existing weight-one coefficient; no new finite cyclic model is introduced. -/
def markingCoefficientMap : _root_.GroupCohomology.ContinuousH1.CoefficientMap
    (Field.absoluteGaloisGroup K) (stalk K n) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) where
  toFun := stalkMarking K n
  map_zero' := (stalkMarking K n).map_zero
  map_add' := (stalkMarking K n).map_add
  continuous_toFun := continuous_of_discreteTopology
  map_smul' := stalkMarking_galois K n

/-- The literal stalk marking is bijective, independently of a primitive root. -/
theorem markingCoefficientMap_bijective : Function.Bijective (markingCoefficientMap K n) :=
  (stalkMarking K n).bijective

end GroupCohomology.Kummer.RootStalk
