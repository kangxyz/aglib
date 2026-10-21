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

The stalk action is defined using this additive marking, then proved equal
to precomposition by the actual Galois point automorphism and to evaluation
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

/-- Transport along the literal root evaluation; the next theorem identifies its
map with precomposition by the actual Galois point automorphism. -/
@[instance_reducible] def stalkGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup K) (stalk K n) := by
  let e := stalkMarking K n
  exact { e.toEquiv.mulAction (Field.absoluteGaloisGroup K) with
    smul_zero σ := by
      change e.symm (σ • e 0) = 0
      simp
    smul_add σ a b := by
      change e.symm (σ • e (a + b)) = e.symm (σ • e a) + e.symm (σ • e b)
      simp [smul_add] }

theorem stalkMarking_galois (σ : Field.absoluteGaloisGroup K) (a : stalk K n) :
    letI := stalkGaloisAction K n
    stalkMarking K n (σ • a) = σ • stalkMarking K n a := by
  letI := stalkGaloisAction K n
  exact (stalkMarking K n).apply_symm_apply _

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

local instance rootsFinite : IsFinite (MultiplicativeGroup.rootsGroupScheme (Spec (.of K))
    n).X.hom :=
  RootsFiniteEtale.rootsScheme_finite _ n (NeZero.pos n)

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

/-- The literal finite stalk is equipped with its discrete topology. -/
instance stalkTopology : TopologicalSpace (stalk K n) := ⊥
instance stalkDiscreteTopology : DiscreteTopology (stalk K n) := ⟨rfl⟩

/-- The Galois action on the root stalk transported through its root-evaluation marking. -/
local instance : DistribMulAction (Field.absoluteGaloisGroup K) (stalk K n) := stalkGaloisAction K n

instance stalkContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup K) (stalk K n) where
  continuous_smul := by
    change Continuous (fun p : Field.absoluteGaloisGroup K × stalk K n =>
      (stalkMarking K n).symm (p.1 • stalkMarking K n p.2))
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
