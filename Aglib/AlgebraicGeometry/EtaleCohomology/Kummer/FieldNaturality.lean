/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Field
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ClosureEmbedding
public import Aglib.RingTheory.RootsOfUnity.BaseField
public import Aglib.RingTheory.RootsOfUnity.FieldPullbackIndependence
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Kummer.FieldNaturality` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`07051ba1d20df9855abfa86add761950ce5b5a80092d57bd086eea2b7abe0892`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/- Current interface migration: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Original mathematical and construction provenance is retained below.
Previous validation is historical; new-interface validation is pending. -/
/-!
# Actual field pullback for etale roots and their continuous H1

C4/C5 support for `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical source basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For an explicit compatible embedding of the fixed algebraic closures, the
source geometric point is extended by literal Spec precomposition. The actual
Over pullback adjunction lifts it to the pulled-back cover. Normal Galois
restriction commutes with that embedding on field elements and hence on these
actual point maps. The roots group-scheme base-change isomorphism has its
proved literal root-coordinate formula. Transporting the actual scheme torsor
action through that isomorphism gives the pulled-back roots torsor; its unique
positive transport computes exactly the existing muMap on cocycle values.

The scheme map on H1 is the actual inverse-image Ext map followed by the
canonical represented roots coefficient isomorphism. An actual relative torsor
morphism proves its class equation. Surjectivity of the constructed 03AJ map
and the genuine 03RV representatives reduce every class to the proved point
calculation, establishing comparison_pullback without a naturality premise.
Only the same explicit 03AJ/03RV, Galois-category/fibre-functor and Ext-size
inputs as the existing field comparison are retained.

The native field Kummer cocycle maps to the cocycle of the literal image root;
tensoring both root coefficients gives the existing weight-two coefficientMap.
Choice independence identifies that map with FieldPullbackIndependence.canonical.
The weight-two endpoint here concerns root-cup images for a specified root in
the base field, not a claim that every arithmetic Lambda class has such a
presentation. In particular, no primitive root in the arithmetic function
field is assumed. The arbitrary arithmetic chi-squared/Lambda coefficient
identification and final curve/Bockstein assembly remain distinct applications.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
open _root_.GroupCohomology.ContinuousH1
namespace GroupCohomology.Kummer.FieldNaturality
open Field.absoluteGaloisGroup.RootsOfUnity
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (i : Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.Embedding (K := K) (L
      := L)) (n : ℕ)

/-- The continuous equivariant map on root coordinates induced by the supplied closure embedding
and its Galois restriction map. -/
def muPullback : PullbackMap (A := Mu K n) (B := Mu L n)
    (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i) where
  toFun := Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap i n
  map_zero' := map_zero _
  map_add' := map_add _
  continuous_toFun := continuous_of_discreteTopology
  map_smul' g x := by
    letI := i.toAlgebra
    exact Field.absoluteGaloisGroup.RootsOfUnity.FieldPullback.muMap_smul K L n g x

/-- Map nth roots of unity along the given base-field algebra homomorphism. -/
def rootMap : rootsOfUnity n K →* rootsOfUnity n L :=
  restrictRootsOfUnity (algebraMap K L) n

theorem muMap_baseRoot (ζ : rootsOfUnity n K) :
    Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap i n
        (Field.absoluteGaloisGroup.RootsOfUnity.baseRoot K n ζ) =
      Field.absoluteGaloisGroup.RootsOfUnity.baseRoot L n (rootMap (K := K) (L := L) n ζ) := by
  ext
  exact i.commutes ((ζ : Kˣ) : K)

/-- Map base-field units along the given algebra homomorphism. -/
def unitMap : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom

/-- Map algebraic-closure units along the supplied closure embedding. -/
def closureUnitMap : (AlgebraicClosure K)ˣ →* (AlgebraicClosure L)ˣ :=
  Units.map i.toRingHom.toMonoidHom

theorem closureUnitMap_base (f : Kˣ) :
    closureUnitMap i (GroupCohomology.Kummer.baseUnits K f) =
      GroupCohomology.Kummer.baseUnits L (unitMap (K := K) (L := L) f) := by
  ext
  exact i.commutes (f : K)

theorem mappedRoot_pow {f : Kˣ} (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = GroupCohomology.Kummer.baseUnits K f) :
    closureUnitMap i a ^ n = GroupCohomology.Kummer.baseUnits L (unitMap (K := K) (L := L) f) := by
  rw [← map_pow, ha, closureUnitMap_base]

theorem kummer_cocycle_naturality {f : Kˣ} (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = GroupCohomology.Kummer.baseUnits K f) :
    (muPullback i n).onCocycles (GroupCohomology.Kummer.cocycle K n a ha) =
      GroupCohomology.Kummer.cocycle L n (closureUnitMap i a) (mappedRoot_pow i n a ha) := by
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  change Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap i n
    (GroupCohomology.Kummer.value K n a ha
        (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i g)) =
      GroupCohomology.Kummer.value L n (closureUnitMap i a) (mappedRoot_pow i n a ha) g
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap_value,
      GroupCohomology.Kummer.value_units,
    Units.val_div_eq_div_val]
  change i (((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
    Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i g) (a :
        AlgebraicClosure K)) / a) =
    (show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g) (i a) / i a
  exact (map_div₀ i.toRingHom _ _).trans (congrArg
    (fun z : AlgebraicClosure L => z / i (a : AlgebraicClosure K))
    (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction_commutes i g
        (a : AlgebraicClosure K)))

theorem kummer_naturality (hn : 0 < n) (f : Kˣ) :
    (muPullback i n).onH1 (GroupCohomology.Kummer.kummer K n hn f) =
      GroupCohomology.Kummer.kummer L n hn (unitMap (K := K) (L := L) f) := by
  let a := GroupCohomology.Kummer.chosenRoot K n hn f
  have ha := GroupCohomology.Kummer.chosenRoot_pow K n hn f
  rw [GroupCohomology.Kummer.kummer_eq_class L n (closureUnitMap i a) (mappedRoot_pow i n a ha) hn]
  change classOf _ _ ((muPullback i n).onCocycles (GroupCohomology.Kummer.cocycle K n a ha)) = _
  rw [kummer_cocycle_naturality]

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group

/-- The spectrum map of the given base-field algebra homomorphism, reused from the canonical
closure-embedding interface. -/
abbrev fieldMorphism : Spec (.of L) ⟶ Spec (.of K) :=
  Scheme.FiniteEtale.FieldGalois.ClosureEmbedding.fieldMorphism

/-- Literal extension of the chosen geometric point along the closure embedding. -/
abbrev pointExtension : Over.mk (geometricPoint L ≫ fieldMorphism (K := K) (L := L)) ⟶
    Over.mk (geometricPoint K) :=
  Scheme.FiniteEtale.FieldGalois.ClosureEmbedding.pointExtension i

/-- Actual point precomposition intertwines the genuine Galois restriction. -/
theorem pointExtension_galois (σ : Field.absoluteGaloisGroup L) :
    (Over.map (fieldMorphism (K := K) (L := L))).map (pointEnd L σ) ≫ pointExtension i =
      pointExtension i ≫ pointEnd K
          (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i σ)  :=
  Scheme.FiniteEtale.FieldGalois.ClosureEmbedding.pointExtension_galois i σ

/-- A source torsor point gives an actual point on its scheme pullback. -/
def pullbackPoint (Y : Scheme.FiniteEtale (Spec (.of K))) (t : Fiber (geometricPoint K) Y) :
    Fiber (geometricPoint L) ((baseChange (fieldMorphism (K := K) (L := L))).obj Y) :=
  Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionEquiv
      (fieldMorphism (K := K) (L := L))
    (Over.mk (geometricPoint L)) Y.obj (pointExtension i ≫ t)

/-- The pullback point respects literal Galois action, before any H1 quotient. -/
theorem pullbackPoint_galois (Y : Scheme.FiniteEtale (Spec (.of K)))
    (t : Fiber (geometricPoint K) Y)
    (σ : Field.absoluteGaloisGroup L) :
    pointEnd L σ ≫ pullbackPoint i Y t =
      pullbackPoint i Y (pointEnd K
          (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i σ) ≫
          t) := by
  unfold pullbackPoint
  rw [← (Over.mapPullbackAdj (fieldMorphism (K := K) (L := L))).homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, pointExtension_galois, Category.assoc]


open CartesianMonoidalCategory
open _root_.CategoryTheory
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

/-- The group scheme of nth roots of unity over the given field spectrum. -/
abbrev rootsGroup (F : Type u) [Field F] := MultiplicativeGroup.rootsGroupScheme (Spec (.of F)) n

/-- The canonical coefficient-point equivalence on arbitrary test schemes. -/
abbrev rootSections (U : Over (Spec (.of L))) :=
  MultiplicativeBaseChange.rootsComparisonEquiv (fieldMorphism (K := K) (L := L)) n U

theorem rootSections_symm_naturality {U V : Over (Spec (.of L))} (h : U ⟶ V)
    (a : V ⟶ (rootsGroup n L).X) :
    (rootSections (K := K) n U).symm (h ≫ a) =
      h ≫ (rootSections (K := K) n V).symm a := by
  apply (rootSections (K := K) n U).injective
  rw [MulEquiv.apply_symm_apply, MultiplicativeBaseChange.rootsComparisonEquiv_naturality,
    MulEquiv.apply_symm_apply]

/-- Pullback action transported through the actual roots group-scheme isomorphism. -/
def pullbackRootAction (Y : Scheme.FiniteEtale (Spec (.of K)))
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj)) :
    TorsorAction (rootsGroup n L)
      (toUnit ((baseChange (fieldMorphism (K := K) (L := L))).obj Y).obj) where
  act {U} a x :=
      (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
    (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ).act
      ((rootSections (K := K) n U).symm a) x
  naturality h a x := by
    rw [TorsorAction.naturality, rootSections_symm_naturality]
  one_act x := by rw [map_one, TorsorAction.one_act]
  mul_act a b x := by rw [map_mul, TorsorAction.mul_act]
  «over» a x := TorsorAction.over _ _ _
  transport {U} x y h := by
    obtain ⟨a, ha, hu⟩ :=
        (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
      (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ).transport x y h
    refine ⟨rootSections (K := K) n U a, ?_, ?_⟩
    · simpa only [MulEquiv.symm_apply_apply] using ha
    · intro b hb
      exact ((rootSections (K := K) n U).symm.injective
        (by simpa only [MulEquiv.symm_apply_apply] using hu _ hb))

/-- Extend the specified geometric coefficient point along the closure embedding and compare it
with the actual roots group over the extended field. -/
def pullbackCoefficientPoint
    (a : Over.mk (geometricPoint K) ⟶ (rootsGroup n K).X) :
    Over.mk (geometricPoint L) ⟶ (rootsGroup n L).X :=
  rootSections (K := K) n (Over.mk (geometricPoint L))
    (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionEquiv
        (fieldMorphism (K := K) (L := L))
      (Over.mk (geometricPoint L)) (rootsGroup n K).X (pointExtension i ≫ a))

theorem pullbackRootAction_point (Y : Scheme.FiniteEtale (Spec (.of K)))
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj))
    (a : Over.mk (geometricPoint K) ⟶ (rootsGroup n K).X) (t : Fiber (geometricPoint K) Y) :
    (pullbackRootAction (K := K) (L := L) n Y τ).act
      (pullbackCoefficientPoint i n a) (pullbackPoint i Y t) =
        pullbackPoint i Y (τ.act a t) := by
  change (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
    (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ).act
      ((rootSections (K := K) n (Over.mk (geometricPoint L))).symm
        (rootSections (K := K) n (Over.mk (geometricPoint L)) _)) _ = _
  rw [MulEquiv.symm_apply_apply]
  change (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionEquiv
    (fieldMorphism (K := K) (L := L)) (Over.mk (geometricPoint L)) Y.obj)
    (τ.act
      ((Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionMulEquiv
        (fieldMorphism (K := K) (L := L)) (Over.mk (geometricPoint L)) (rootsGroup n K)).symm
        ((Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionMulEquiv
          (fieldMorphism (K := K) (L := L)) (Over.mk (geometricPoint L)) (rootsGroup n K))
            (pointExtension i ≫ a)))
      (((Over.mapPullbackAdj (fieldMorphism (K := K) (L := L))).homEquiv
        (Over.mk (geometricPoint L)) Y.obj).symm
        (((Over.mapPullbackAdj (fieldMorphism (K := K) (L := L))).homEquiv
          (Over.mk (geometricPoint L)) Y.obj) (pointExtension i ≫ t)))) = _
  rw [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg
      (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSectionEquiv
    (fieldMorphism (K := K) (L := L)) (Over.mk (geometricPoint L)) Y.obj)
    (τ.naturality (pointExtension i) a t).symm

variable [CharZero K] [CharZero L] [NeZero n]

omit [CharZero K] [CharZero L] [NeZero n] in
-- Retain the original characteristic-zero fields and nonzero Kummer level.
@[nolint unusedArguments]
theorem pullbackCoefficientPoint_mark [CharZero K] [CharZero L] [NeZero n]
    (a : Over.mk (geometricPoint K) ⟶ (rootsGroup n K).X) :
    (GroupCohomology.Kummer.Field.pointMark L n (pullbackCoefficientPoint i n
        a)).toAdd =
      Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap i n
          (GroupCohomology.Kummer.Field.pointMark K n a).toAdd := by
  have hc : MultiplicativeGroup.rootsHomEquiv (Spec (.of L)) n (Over.mk (geometricPoint L))
      (pullbackCoefficientPoint i n a) =
    MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n
      (Over.mk (geometricPoint L ≫ fieldMorphism (K := K) (L := L))) (pointExtension i ≫ a) := by
    exact ((MultiplicativeBaseChange.rootsSectionsEquiv (Spec (.of L)) n
      (Over.mk (geometricPoint L))).apply_symm_apply _).trans
        (congrArg (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _)
          (((Over.mapPullbackAdj (fieldMorphism (K := K) (L := L))).homEquiv
            (Over.mk (geometricPoint L)) (rootsGroup n K).X).symm_apply_apply _))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (Scheme.ΓSpecIso (.of (AlgebraicClosure L))).hom.hom
    (MultiplicativeGroup.rootsHomEquiv (Spec (.of L)) n _
      (pullbackCoefficientPoint i n a)).val.val =
    i ((Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
      (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ a).val.val)
  rw [hc]
  have h := (MultiplicativeGroup.rootsRepresentable (Spec (.of K)) n).homEquiv_comp
    (pointExtension i) a
  have hv := congrArg (fun z : rootsOfUnity n Γ(Spec (.of (AlgebraicClosure L)), ⊤) =>
    (Scheme.ΓSpecIso (.of (AlgebraicClosure L))).hom.hom z.val.val) h
  exact hv.trans (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom i.toRingHom))
      (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n _ a).val.val)


universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L)))]

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open scoped CategoryTheory.PreGaloisCategory
variable [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))]

/-- The native commutative group law on the roots group over each field spectrum. -/
local instance (F : Type u) [Field F] : CommGrpObj (rootsGroup n F).X :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of F)) n
local instance (F : Type u) [Field F] : IsFinite (rootsGroup n F).X.hom :=
  RootsFiniteEtale.rootsScheme_finite _ n (NeZero.pos n)
local instance (F : Type u) [Field F] [CharZero F] : Etale (rootsGroup n F).X.hom :=
  RootsFiniteEtale.rootsScheme_etale _ n (NeZero.pos n)
      (GroupCohomology.Kummer.RootStalk.levelInvertible F n)

omit [CharZero K] [CharZero L] [NeZero n]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L)))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] in
/-- Unique positive transport commutes with actual point extension and pullback. -/
-- Retain the original field, level, fibre-functor and two Ext-universe transport inputs.
@[nolint unusedArguments]
theorem transport_pullback [CharZero K] [CharZero L] [NeZero n]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L)))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] (Y : Scheme.FiniteEtale
        (Spec (.of K)))
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj))
    (t : Fiber (geometricPoint K) Y) (σ : Field.absoluteGaloisGroup L) :
    pullbackCoefficientPoint i n
      (transport (geometricPoint K) (rootsGroup n K) Y τ t
        (pointEnd K
            (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i σ)
            ≫ t)) =
    transport (geometricPoint L) (rootsGroup n L)
      ((baseChange (fieldMorphism (K := K) (L := L))).obj Y)
      (pullbackRootAction (K := K) (L := L) n Y τ)
      (pullbackPoint i Y t) (pointEnd L σ ≫ pullbackPoint i Y t) := by
  apply transport_unique
  rw [pullbackRootAction_point, transport_act, ← pullbackPoint_galois]

/-- Equality of the literal continuous crossed homomorphisms, before quotients. -/
theorem fieldCocycle_pullback (Y : Scheme.FiniteEtale (Spec (.of K)))
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj))
    (t : Fiber (geometricPoint K) Y) :
    GroupCohomology.Kummer.Field.fieldCocycle L n
      ((baseChange (fieldMorphism (K := K) (L := L))).obj Y)
      (pullbackRootAction (K := K) (L := L) n Y τ) (pullbackPoint i Y t) =
    (muPullback i n).onCocycles (GroupCohomology.Kummer.Field.fieldCocycle K n
        Y τ t) := by
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro σ
  change (GroupCohomology.Kummer.Field.fieldCocycle L n _ _ _).val σ =
    Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.muMap i n
      ((GroupCohomology.Kummer.Field.fieldCocycle K n Y τ t).val
          (Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.restriction i σ))
  rw [GroupCohomology.Kummer.Field.fieldCocycle_value,
      GroupCohomology.Kummer.Field.fieldCocycle_value,
    ← transport_pullback, pullbackCoefficientPoint_mark]

/-- The small-etale sheaf of nth roots of unity on the given field spectrum. -/
abbrev muSheaf (F : Type u) [Field F] :=
  GroupCohomology.Kummer.Coefficients.mu (Spec (.of F)) n

/-- The actual inverse-image isomorphism for the roots coefficient. -/
def rootsPullbackIso :
    (inverseImage (fieldMorphism (K := K) (L := L))).obj (muSheaf n K) ≅ muSheaf n L :=
  representedSheafBaseChangeIso (fieldMorphism (K := K) (L := L)) (rootsGroup n K) ≪≫
    Scheme.EtaleCohomology.MarkedCoefficients.representedSheafIso
      (MultiplicativeBaseChange.rootsBaseChangeIso (fieldMorphism (K := K) (L := L)) n)

/-- Identity on the actual pulled-back cover, with the genuine roots coefficient map. -/
def rootCoefficientHom (Y : Scheme.FiniteEtale (Spec (.of K))) [Surjective Y.obj.hom]
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj)) :
    Scheme.EtaleCohomology.Torsor.Hom
      (representedSheafMap
        (MultiplicativeBaseChange.rootsBaseChangeIso (fieldMorphism (K := K) (L := L)) n).hom)
      (torsorOfSchemeAction
        (Scheme.EtaleCohomology.baseChangedGroup
          (fieldMorphism (K := K) (L := L)) (rootsGroup n K))
        ((baseChange (fieldMorphism (K := K) (L := L))).obj Y)
        (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
          (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ))
      (torsorOfSchemeAction (rootsGroup n L)
        ((baseChange (fieldMorphism (K := K) (L := L))).obj Y)
        (pullbackRootAction (K := K) (L := L) n Y τ)) where
  map := 𝟙 _
  equivariant U a t := by
    change ULift.{u + 1} (Additive
      ((Scheme.Etale.forget (Spec (.of L))).obj U.unop ⟶
        (Scheme.EtaleCohomology.baseChangedGroup
          (fieldMorphism (K := K) (L := L)) (rootsGroup n K)).X)) at a
    change ULift.{u + 1}
      ((Scheme.Etale.forget (Spec (.of L))).obj U.unop ⟶
        ((baseChange (fieldMorphism (K := K) (L := L))).obj Y).obj) at t
    apply congrArg ULift.up
    change (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
      (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ).act a.down.toMul t.down =
      (Scheme.EtaleCohomology.SchemeTorsorBaseChange.pullbackSchemeAction
        (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ).act
        ((rootSections (K := K) n ((Scheme.Etale.forget (Spec (.of L))).obj U.unop)).symm
          (a.down.toMul ≫ (MultiplicativeBaseChange.rootsBaseChangeIso
            (fieldMorphism (K := K) (L := L)) n).hom.hom.hom)) t.down
    have hc : a.down.toMul ≫ (MultiplicativeBaseChange.rootsBaseChangeIso
        (fieldMorphism (K := K) (L := L)) n).hom.hom.hom =
        rootSections (K := K) n ((Scheme.Etale.forget (Spec (.of L))).obj U.unop) a.down.toMul :=
      MultiplicativeBaseChange.groupIsoOfSections_hom _ _ _ _ _ _
    rw [hc, MulEquiv.symm_apply_apply]


/-- Genuine contravariant Ext H1 with the canonical roots coefficient transport. -/
def schemePullback : H1Etale (Spec (.of K)) (muSheaf n K) →+
    H1Etale (Spec (.of L)) (muSheaf n L) :=
  (coefficientMap (rootsPullbackIso (K := K) (L := L) n).hom).comp
    (h1Pullback (fieldMorphism (K := K) (L := L)) (muSheaf n K))

omit [CharZero L]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] in
-- Retain the original extended-field characteristic and both chosen geometric fibre functors.
@[nolint unusedArguments]
theorem schemePullback_torsor [CharZero L]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] (Y : Scheme.FiniteEtale
        (Spec (.of K))) [Surjective Y.obj.hom]
    (τ : TorsorAction (rootsGroup n K) (toUnit Y.obj)) :
    schemePullback (K := K) (L := L) n (torsorExtClass (torsorOfSchemeAction (rootsGroup n K) Y
        τ)) =
      torsorExtClass (torsorOfSchemeAction (rootsGroup n L)
        ((baseChange (fieldMorphism (K := K) (L := L))).obj Y)
        (pullbackRootAction (K := K) (L := L) n Y τ)) := by
  simp only [schemePullback, rootsPullbackIso, Iso.trans_hom,
    coefficientMap_comp, AddMonoidHom.comp_apply]
  let q : representedSheaf
      (Scheme.EtaleCohomology.baseChangedGroup
        (fieldMorphism (K := K) (L := L)) (rootsGroup n K)) ⟶
      representedSheaf (rootsGroup n L) :=
    representedSheafMap
      (MultiplicativeBaseChange.rootsBaseChangeIso (fieldMorphism (K := K) (L := L)) n).hom
  have h₁ :=
      Scheme.EtaleCohomology.SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction.{u, w, w'}
    (fieldMorphism (K := K) (L := L)) (rootsGroup n K) Y τ
  have h₂ := torsorExtClass_naturality (rootCoefficientHom (K := K) (L := L) n Y τ)
  have h₃ := congrArg (fun z : H1Etale.{u, u + 1, w'} (Spec (.of L))
      (representedSheaf (Scheme.EtaleCohomology.baseChangedGroup
        (fieldMorphism (K := K) (L := L)) (rootsGroup n K))) =>
      coefficientMap q z) h₁
  exact h₃.trans h₂

theorem comparison_schemeTorsor (F : Type u) [Field F] [CharZero F]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of F)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint F))]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of F)))]
    (hA : Stacks03AJ.{u, w} (Spec (.of F))) (hR : Stacks03RV (Spec (.of F)))
    (Y : Scheme.FiniteEtale (Spec (.of F))) [Surjective Y.obj.hom]
    (τ : TorsorAction (rootsGroup n F) (toUnit Y.obj)) (t : Fiber (geometricPoint F) Y) :
    GroupCohomology.Kummer.Field.comparison F n hA hR (torsorExtClass
        (torsorOfSchemeAction (rootsGroup n F) Y τ)) =
      classOf (Field.absoluteGaloisGroup F) (Mu F n)
          (GroupCohomology.Kummer.Field.fieldCocycle F n Y τ t) := by
  rw [GroupCohomology.Kummer.Field.comparison_torsor_representative F n hA hR
      _ Y (Iso.refl _) t,
    torsorOfSchemeAction_representedSchemeAction]


/-- The actual scheme H1 pullback and actual root marking intertwine with
Galois restriction for every class, by comparison on genuine torsor representatives. -/
theorem comparison_pullback
    (hAK : Stacks03AJ.{u, w} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
    (hAL : Stacks03AJ.{u, w'} (Spec (.of L))) (hRL : Stacks03RV (Spec (.of L)))
    (a : H1Etale (Spec (.of K)) (muSheaf n K)) :
    GroupCohomology.Kummer.Field.comparison L n hAL hRL (schemePullback (K :=
        K) (L := L) n a) =
      (muPullback i n).onH1 (GroupCohomology.Kummer.Field.comparison K n hAK
          hRK a) := by
  obtain ⟨p, rfl⟩ := (hAK.bijective (muSheaf n K)).surjective a
  refine Quotient.inductionOn p ?_
  intro P
  let Y := P.finiteEtaleRepresentative hRK
      (GroupCohomology.Kummer.Field.finiteCoefficient K n).locally_constant
  let e := P.finiteEtaleRepresentativeIso hRK
      (GroupCohomology.Kummer.Field.finiteCoefficient K n).locally_constant
  let τ := P.representedSchemeAction (rootsGroup n K) Y e
  letI : Surjective Y.obj.hom := P.represented_surjective (rootsGroup n K) Y e
  have he : torsorExtClass (torsorOfSchemeAction (rootsGroup n K) Y τ) = torsorExtClass P :=
    torsorExtClass_iso (P.representedSchemeActionIso (rootsGroup n K) Y e)
  change GroupCohomology.Kummer.Field.comparison L n hAL hRL (schemePullback
      (K := K) (L := L) n (torsorExtClass P)) =
    (muPullback i n).onH1 (GroupCohomology.Kummer.Field.comparison K n hAK hRK
        (torsorExtClass P))
  rw [← he, schemePullback_torsor]
  obtain ⟨t⟩ :=
      Scheme.EtaleCohomology.SchemeTorsorClassification.nonempty_fiber_of_surjective
        (geometricPoint K) Y
  rw [comparison_schemeTorsor n L hAL hRL _ _ (pullbackPoint i Y t),
    comparison_schemeTorsor n K hAK hRK Y τ t, fieldCocycle_pullback]
  rfl

end GroupCohomology.Kummer.FieldNaturality
