/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous.Transgression.Basic

/-!
# Transgression naturality from primitive cochain squares

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/Transgression/Naturality.lean`.
SHA-256: `350a7aff1b3c1762da7a41c2a1ccfbff05943b6c449bf15ed6dbdd1ac221028d`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

open ContinuousH1


namespace GroupCohomology.ContinuousH1.CoefficientMap

variable {G A B : Type*} [_root_.Group G] [TopologicalSpace G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- Ordinary coefficient functoriality is relative pullback along the identity. -/
def toPullbackMap (a : CoefficientMap G A B) :
    PullbackMap (A := A) (B := B) (ContinuousMonoidHom.id G) where
  toContinuousAddMonoidHom := a.toContinuousAddMonoidHom
  map_smul' := a.map_smul

@[simp] theorem toPullbackMap_onH1 (a : CoefficientMap G A B) :
    a.toPullbackMap.onH1 = a.onH1 := rfl

end GroupCohomology.ContinuousH1.CoefficientMap

namespace GroupCohomology.ContinuousH1.Transgression

open AddCommGrpCat.MultiplicationCone
open GroupCohomology

variable {G H : Type*} [_root_.Group G] [TopologicalSpace G] [_root_.Group H] [TopologicalSpace H]
variable {B₀ B₁ B₀' B₁' A A' : Type*}
  [AddCommGroup B₀] [TopologicalSpace B₀] [IsTopologicalAddGroup B₀]
  [DistribMulAction G B₀] [ContinuousSMul G B₀]
  [AddCommGroup B₁] [TopologicalSpace B₁] [IsTopologicalAddGroup B₁]
  [DistribMulAction G B₁] [ContinuousSMul G B₁]
  [AddCommGroup B₀'] [TopologicalSpace B₀'] [IsTopologicalAddGroup B₀']
  [DistribMulAction H B₀'] [ContinuousSMul H B₀']
  [AddCommGroup B₁'] [TopologicalSpace B₁'] [IsTopologicalAddGroup B₁']
  [DistribMulAction H B₁'] [ContinuousSMul H B₁']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DistribMulAction H A'] [ContinuousSMul H A']

variable {φ : ContinuousMonoidHom H G}
  {d : ContinuousH1.CoefficientMap G B₀ B₁}
  {d' : ContinuousH1.CoefficientMap H B₀' B₁'}

/-- Relative cochain maps and their differential square. Both maps carry the
actual actions; equivariance is relative to `φ`, not an assumed H1 square. -/
structure ClosedMap (φ : ContinuousMonoidHom H G)
    (d : ContinuousH1.CoefficientMap G B₀ B₁)
    (d' : ContinuousH1.CoefficientMap H B₀' B₁') where
  /-- The degree-zero continuous coefficient map, equivariant relative to `φ`. -/
  zero : ContinuousH1.PullbackMap (A := B₀) (B := B₀') φ
  /-- The degree-one continuous coefficient map, equivariant relative to `φ`. -/
  one : ContinuousH1.PullbackMap (A := B₁) (B := B₁') φ
  comm : ∀ y : B₀, d' (zero y) = one (d y)

namespace ClosedMap

variable (u : ClosedMap φ d d')

/-- The relative degree-zero cochain map restricts to the genuine kernels. -/
def onKernel : ContinuousH1.PullbackMap (A := Kernel d) (B := Kernel d') φ where
  toFun k := ⟨u.zero k.val, by
    change d' (u.zero k.val) = 0
    have hk : d k.val = 0 := k.property
    rw [u.comm, hk]
    exact u.one.toContinuousAddMonoidHom.map_zero⟩
  map_zero' := by
    apply Subtype.ext
    exact u.zero.toContinuousAddMonoidHom.map_zero
  map_add' := by
    intro k l
    apply Subtype.ext
    exact u.zero.map_add k.val l.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact u.zero.toContinuousAddMonoidHom.continuous.comp continuous_subtype_val
  map_smul' := by
    intro h k
    apply Subtype.ext
    exact u.zero.map_smul h k.val

omit [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₀'] [ContinuousSMul H B₀']
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
@[simp] theorem onKernel_val (k : Kernel d) :
    (u.onKernel.toContinuousAddMonoidHom k).val = u.zero k.val := rfl

omit [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₀'] [ContinuousSMul H B₀']
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- An invariant degree-one value remains invariant after the relative map. -/
theorem invariant (b : B₁) (hb : ∀ g : G, g • b = b) :
    ∀ h : H, h • u.one b = u.one b := by
  intro h
  rw [← u.one.map_smul, hb (φ h)]

omit [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₀'] [ContinuousSMul H B₀']
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- The primitive differential square transports every actual cochain lift. -/
theorem lift_spec (b : B₁) (y : B₀) (hy : d y = b) :
    d' (u.zero y) = u.one b := by
  rw [u.comm, hy]

omit [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₀'] [ContinuousSMul H B₀']
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- Relative equivariance transports the actual kernel-valued displacement.
The target invariant value and lift certificate may be supplied independently;
proof irrelevance prevents chosen certificates from becoming extra data. -/
theorem displacement_naturality (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (b' : B₁') (hb' : ∀ h : H, h • b' = b')
    (hy' : d' (u.zero y) = b') (h : H) :
    u.onKernel (displacement d b hb y hy (φ h)) =
      displacement d' b' hb' (u.zero y) hy' h := by
  apply Subtype.ext
  change u.zero (φ h • y - y) = h • u.zero y - u.zero y
  rw [u.zero.map_sub, u.zero.map_smul]

variable (η : ContinuousH1.CoefficientMap G (Kernel d) A)
  (η' : ContinuousH1.CoefficientMap H (Kernel d') A')
  (a : ContinuousH1.PullbackMap (A := A) (B := A') φ)
  (hη : ∀ k : Kernel d, a (η k) = η' (u.onKernel k))

include hη

omit [ContinuousSMul G A] [ContinuousSMul H A']
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- The eta square and displacement identity identify the native cocycles,
before passing to either quotient. -/
theorem cocycleOfLift_naturality (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (b' : B₁') (hb' : ∀ h : H, h • b' = b')
    (hy' : d' (u.zero y) = b') :
    a.onCocycles (cocycleOfLift d η b hb y hy) =
      cocycleOfLift d' η' b' hb' (u.zero y) hy' := by
  apply ContinuousH1.Cocycle.ext
  intro h
  rw [ContinuousH1.PullbackMap.onCocycles_apply, cocycleOfLift_apply,
    cocycleOfLift_apply, hη, u.displacement_naturality]

omit [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- Arbitrary lift formula for simultaneous group pullback and coefficient map. -/
-- Retain the original continuous-coefficient interface for both degree-one target groups;
-- the class identity uses their specified topology and action, not these continuity instances.
@[nolint unusedArguments]
theorem classOfLift_naturality
    [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
    [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁']
    (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) :
    a.onH1 (ContinuousH1.classOf G A (cocycleOfLift d η b hb y hy)) =
      ContinuousH1.classOf H A'
        (cocycleOfLift d' η' (u.one b) (u.invariant b hb)
          (u.zero y) (u.lift_spec b y hy)) := by
  rw [ContinuousH1.PullbackMap.onH1_classOf,
    u.cocycleOfLift_naturality η η' a hη]

end ClosedMap

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup C₃]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup D₃]
  {C : Complex C₀ C₁ C₂ C₃} {D : Complex D₀ D₁ D₂ D₃}

/-- Primitive source-to-closed cochain squares. The degree-zero square records
compatibility with source boundaries; degree-one compatibility transports the
lift used in the class formula. No square on H1 is assumed. -/
structure SourceSquare (u : ClosedMap φ d d')
    (s : SourceData d C) (t : SourceData d' D) (f : ChainMap C D) : Prop where
  zero : ∀ x : C₀, u.zero (s.pull₀ x) = t.pull₀ (f.f₀ x)
  one : ∀ x : C₁, u.one (s.pull₁ x) = t.pull₁ (f.f₁ x)

namespace SourceData

variable (s : SourceData d C) (t : SourceData d' D)
  (u : ClosedMap φ d d') (f : ChainMap C D)
  (hs : SourceSquare u s t f)
  (η : ContinuousH1.CoefficientMap G (Kernel d) A)
  (η' : ContinuousH1.CoefficientMap H (Kernel d') A')
  (a : ContinuousH1.PullbackMap (A := A) (B := A') φ)
  (hη : ∀ k : Kernel d, a (η k) = η' (u.onKernel k))

include hs hη

omit [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
  [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁'] in
/-- Naturality of the cycle class. The image of the source's chosen lift is an
actual target lift; target lift independence replaces its separately chosen lift. -/
-- Retain the original continuous-coefficient interface for both degree-one target groups;
-- the class identity uses their specified topology and action, not these continuity instances.
@[nolint unusedArguments]
theorem chosenClass_naturality
    [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]
    [IsTopologicalAddGroup B₁'] [ContinuousSMul H B₁']
    (x : C.Cycles₁) :
    a.onH1 (s.chosenClass η x) = t.chosenClass η' (f.onCycles₁ x) := by
  have hy : d' (u.zero (s.lift x)) = t.pull₁ (f.onCycles₁ x).val := by
    rw [u.comm, s.lift_spec]
    exact hs.one x.val
  rw [t.chosenClass_eq η' (f.onCycles₁ x) (u.zero (s.lift x)) hy]
  change a.onH1 (ContinuousH1.classOf G A
    (cocycleOfLift d η (s.pull₁ x.val) (fun g => s.invariant₁ g x)
      (s.lift x) (s.lift_spec x))) = _
  rw [ContinuousH1.PullbackMap.onH1_classOf,
    u.cocycleOfLift_naturality η η' a hη]

/-- Actual transgression naturality on every source H1 class. -/
theorem transgression_naturality_apply (q : C.H₁) :
    a.onH1 (s.transgression η q) = t.transgression η' (f.onH₁ q) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₁.range q
  exact s.chosenClass_naturality t u f hs η η' a hη x

/-- The final source-to-continuous-H1 square follows from primitive cochain data. -/
theorem transgression_naturality :
    a.onH1.comp (s.transgression η) = (t.transgression η').comp f.onH₁ := by
  ext q
  exact s.transgression_naturality_apply t u f hs η η' a hη q

end SourceData

end GroupCohomology.ContinuousH1.Transgression

namespace GroupCohomology.ContinuousH1.Transgression.SourceData

open AddCommGrpCat.MultiplicationCone
open GroupCohomology

variable {G : Type*} [_root_.Group G] [TopologicalSpace G]
  {B₀ B₁ B₀' B₁' A A' : Type*}
  [AddCommGroup B₀] [TopologicalSpace B₀] [IsTopologicalAddGroup B₀]
  [DistribMulAction G B₀] [ContinuousSMul G B₀]
  [AddCommGroup B₁] [TopologicalSpace B₁] [IsTopologicalAddGroup B₁]
  [DistribMulAction G B₁] [ContinuousSMul G B₁]
  [AddCommGroup B₀'] [TopologicalSpace B₀'] [IsTopologicalAddGroup B₀']
  [DistribMulAction G B₀'] [ContinuousSMul G B₀']
  [AddCommGroup B₁'] [TopologicalSpace B₁'] [IsTopologicalAddGroup B₁']
  [DistribMulAction G B₁'] [ContinuousSMul G B₁']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DistribMulAction G A'] [ContinuousSMul G A']
  {d : ContinuousH1.CoefficientMap G B₀ B₁}
  {d' : ContinuousH1.CoefficientMap G B₀' B₁'}
  {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup C₃]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup D₃]
  {C : Complex C₀ C₁ C₂ C₃} {D : Complex D₀ D₁ D₂ D₃}

/-- The same-group specialization lands in the existing native coefficient
`CoefficientMap.onH1`, rather than leaving the identity-group adapter implicit. -/
theorem transgression_naturality_coefficients
    (s : SourceData d C) (t : SourceData d' D)
    (u : ClosedMap (ContinuousMonoidHom.id G) d d')
    (f : ChainMap C D) (hs : SourceSquare u s t f)
    (η : ContinuousH1.CoefficientMap G (Kernel d) A)
    (η' : ContinuousH1.CoefficientMap G (Kernel d') A')
    (a : ContinuousH1.CoefficientMap G A A')
    (hη : ∀ k : Kernel d, a (η k) = η' (u.onKernel k)) :
    a.onH1.comp (s.transgression η) = (t.transgression η').comp f.onH₁ := by
  simpa only [ContinuousH1.CoefficientMap.toPullbackMap_onH1] using
    s.transgression_naturality t u f hs η η' a.toPullbackMap hη

end GroupCohomology.ContinuousH1.Transgression.SourceData
