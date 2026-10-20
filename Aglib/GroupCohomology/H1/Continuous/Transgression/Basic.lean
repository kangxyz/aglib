/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MultiplicationCone.Quotient
public import Aglib.GroupCohomology.H1.Continuous

/-!
# Conditional source-to-continuous-H1 transgression

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/Transgression/Basic.lean`.
SHA-256: `02af1a58a64dc513a9fcdae70e7f630cd015674e7eaf081d9fb28c55a1cb0e84`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.ContinuousH1.Transgression

open AddCommGrpCat.MultiplicationCone
open _root_.GroupCohomology

variable {G B₀ B₁ A : Type*}
  [_root_.Group G] [TopologicalSpace G]
  [AddCommGroup B₀] [TopologicalSpace B₀] [IsTopologicalAddGroup B₀]
  [DistribMulAction G B₀] [ContinuousSMul G B₀]
  [AddCommGroup B₁] [TopologicalSpace B₁] [IsTopologicalAddGroup B₁]
  [DistribMulAction G B₁] [ContinuousSMul G B₁]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

variable (d : ContinuousH1.CoefficientMap G B₀ B₁)

omit [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁]

/-- The actual kernel of the closed-field degree-zero differential. -/
abbrev Kernel := d.toContinuousAddMonoidHom.toAddMonoidHom.ker

/-- Equivariance of the differential restricts the genuine action to its kernel. -/
instance kernelDistribMulAction : DistribMulAction G (Kernel d) where
  smul g x := ⟨g • x.val, by
    change d (g • x.val) = 0
    rw [d.map_smul]
    have hx : d x.val = 0 := x.property
    rw [hx, smul_zero]⟩
  one_smul x := by apply Subtype.ext; exact one_smul _ _
  mul_smul g h x := by apply Subtype.ext; exact mul_smul _ _ _
  smul_zero g := by apply Subtype.ext; exact smul_zero _
  smul_add g x y := by apply Subtype.ext; exact smul_add _ _ _

omit [TopologicalSpace G] [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
@[simp] theorem kernel_smul_val (g : G) (x : Kernel d) :
    (g • x : Kernel d).val = g • x.val := rfl

instance kernelContinuousSMul : ContinuousSMul G (Kernel d) where
  continuous_smul :=
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

variable (η : ContinuousH1.CoefficientMap G (Kernel d) A)

/-- A lifted invariant value gives a continuous kernel-valued displacement. -/
def displacement (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (g : G) : Kernel d :=
  ⟨g • y - y, by
    change d (g • y - y) = 0
    rw [d.map_sub, d.map_smul, hy, hb g, sub_self]⟩

omit [TopologicalSpace G] [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
@[simp] theorem displacement_val (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (g : G) :
    (displacement d b hb y hy g).val = g • y - y := rfl

omit [TopologicalSpace G] [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
theorem displacement_mul (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (g h : G) :
    displacement d b hb y hy (g * h) =
      displacement d b hb y hy g + g • displacement d b hb y hy h := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, displacement_val, kernel_smul_val, mul_smul, smul_sub]
  abel

/-- The actual native continuous cocycle, with positive displacement sign. -/
def cocycleOfLift (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) : ContinuousH1.Cocycle G A :=
  ⟨⟨fun g => η (displacement d b hb y hy g),
    η.continuous.comp
      (((continuous_id.smul continuous_const).sub continuous_const).subtype_mk _)⟩, by
    intro g h
    simp only [ContinuousMap.coe_mk, displacement_mul, η.map_add, η.map_smul]⟩

omit [ContinuousSMul G A] [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
@[simp] theorem cocycleOfLift_apply (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (g : G) :
    (cocycleOfLift d η b hb y hy).val g = η (displacement d b hb y hy g) := rfl

/-- The difference of any two lifts of the same source value is in `ker d`. -/
def liftDifference (b : B₁) (y y' : B₀) (hy : d y = b) (hy' : d y' = b) : Kernel d :=
  ⟨y - y', by change d (y - y') = 0; rw [d.map_sub, hy, hy', sub_self]⟩

omit [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
/-- Native coboundary convention: changing `y'` to `y` gives the principal
cocycle of the *positive* difference `η (y - y')`. -/
theorem lift_difference_principal (b : B₁) (hb : ∀ g : G, g • b = b)
    (y y' : B₀) (hy : d y = b) (hy' : d y' = b) :
    ContinuousH1.principal G A (η (liftDifference d b y y' hy hy')) =
      cocycleOfLift d η b hb y hy - cocycleOfLift d η b hb y' hy' := by
  apply ContinuousH1.Cocycle.ext
  intro g
  rw [ContinuousH1.principal_apply, ContinuousH1.Cocycle.sub_apply, cocycleOfLift_apply,
    cocycleOfLift_apply, ← η.map_smul, ← η.map_sub, ← η.map_sub]
  congr 1
  apply Subtype.ext
  change g • (y - y') - (y - y') = (g • y - y) - (g • y' - y')
  rw [smul_sub]
  abel

/-- Thus the native H1 class is independent of the cochain lift. -/
theorem classOf_lift_eq (b : B₁) (hb : ∀ g : G, g • b = b)
    (y y' : B₀) (hy : d y = b) (hy' : d y' = b) :
    ContinuousH1.classOf G A (cocycleOfLift d η b hb y hy) =
      ContinuousH1.classOf G A (cocycleOfLift d η b hb y' hy') :=
  (ContinuousH1.classOf_eq_iff G A _ _).mpr
    ⟨η (liftDifference d b y y' hy hy'), lift_difference_principal d η b hb y y' hy hy'⟩

omit [ContinuousSMul G A] [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
theorem cocycleOfLift_add (b b' : B₁) (hb : ∀ g : G, g • b = b)
    (hb' : ∀ g : G, g • b' = b') (y y' : B₀) (hy : d y = b) (hy' : d y' = b') :
    cocycleOfLift d η (b + b') (fun g => by rw [smul_add, hb g, hb' g])
      (y + y') (by rw [d.map_add, hy, hy']) =
    cocycleOfLift d η b hb y hy + cocycleOfLift d η b' hb' y' hy' := by
  apply ContinuousH1.Cocycle.ext
  intro g
  rw [ContinuousH1.Cocycle.add_apply, cocycleOfLift_apply, cocycleOfLift_apply,
    cocycleOfLift_apply, ← η.map_add]
  congr 1
  apply Subtype.ext
  change g • (y + y') - (y + y') = (g • y - y) + (g • y' - y')
  rw [smul_add]
  abel

omit [ContinuousSMul G A] [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
/-- An invariant lift has identically zero displacement. -/
theorem cocycleOfLift_eq_zero (b : B₁) (hb : ∀ g : G, g • b = b)
    (y : B₀) (hy : d y = b) (hinv : ∀ g : G, g • y = y) :
    cocycleOfLift d η b hb y hy = 0 := by
  apply ContinuousH1.Cocycle.ext
  intro g
  rw [cocycleOfLift_apply, ContinuousH1.Cocycle.zero_apply]
  have hz : displacement d b hb y hy g = 0 := by
    apply Subtype.ext
    change g • y - y = 0
    rw [hinv g, sub_self]
  rw [hz, η.map_zero]

variable {C₀ C₁ C₂ C₃ : Type*}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup C₃]

/-- Primitive low-degree source pullback and descent premises. This contains
cochain maps and liftability, never an intended H1 comparison as input. -/
structure SourceData (C : Complex C₀ C₁ C₂ C₃) where
  /-- The specified degree-zero map into the target cochain group. -/
  pull₀ : C₀ →+ B₀
  /-- The specified degree-one map into the target cochain group. -/
  pull₁ : C₁ →+ B₁
  comm₀ : ∀ x, d (pull₀ x) = pull₁ (C.d₀ x)
  invariant₀ : ∀ (g : G) (x : C₀), g • pull₀ x = pull₀ x
  invariant₁ : ∀ (g : G) (x : C.Cycles₁), g • pull₁ x.val = pull₁ x.val
  liftable : ∀ x : C.Cycles₁, ∃ y : B₀, d y = pull₁ x.val

namespace SourceData

variable {d} {C : Complex C₀ C₁ C₂ C₃} (s : SourceData d C)

/-- A lift chosen from the `SourceData.liftable` premise for the given source cycle. -/
def lift (x : C.Cycles₁) : B₀ := Classical.choose (s.liftable x)

omit [TopologicalSpace G] [IsTopologicalAddGroup B₀] [ContinuousSMul G B₀]
  [IsTopologicalAddGroup B₁] [ContinuousSMul G B₁] in
theorem lift_spec (x : C.Cycles₁) : d (s.lift x) = s.pull₁ x.val :=
  Classical.choose_spec (s.liftable x)

/-- Chosen lifts are used only before passing to native continuous H1. -/
def chosenClass (η : ContinuousH1.CoefficientMap G (Kernel d) A) (x : C.Cycles₁) :
    ContinuousH1.H1 G A :=
  ContinuousH1.classOf G A (cocycleOfLift d η (s.pull₁ x.val) (fun g => s.invariant₁ g x)
    (s.lift x) (s.lift_spec x))

/-- Any actual lift computes the chosen class, so no additive section is needed. -/
theorem chosenClass_eq (η : ContinuousH1.CoefficientMap G (Kernel d) A) (x : C.Cycles₁)
    (y : B₀) (hy : d y = s.pull₁ x.val) :
    s.chosenClass η x = ContinuousH1.classOf G A
      (cocycleOfLift d η (s.pull₁ x.val) (fun g => s.invariant₁ g x) y hy) :=
  classOf_lift_eq d η _ _ _ _ _ hy

theorem chosenClass_zero (η : ContinuousH1.CoefficientMap G (Kernel d) A) :
    s.chosenClass η 0 = 0 := by
  rw [s.chosenClass_eq η 0 0 (by simp)]
  rw [cocycleOfLift_eq_zero d η _ _ _ _ (fun g => smul_zero g), map_zero]

theorem chosenClass_add (η : ContinuousH1.CoefficientMap G (Kernel d) A) (x x' : C.Cycles₁) :
    s.chosenClass η (x + x') = s.chosenClass η x + s.chosenClass η x' := by
  have hsum : d (s.lift x + s.lift x') = s.pull₁ (x + x').val := by
    rw [d.map_add, s.lift_spec, s.lift_spec]
    exact (s.pull₁.map_add x.val x'.val).symm
  rw [s.chosenClass_eq η (x + x') (s.lift x + s.lift x') hsum]
  have hc : cocycleOfLift d η (s.pull₁ (x + x').val)
      (fun g => s.invariant₁ g (x + x')) (s.lift x + s.lift x') hsum =
      cocycleOfLift d η (s.pull₁ x.val) (fun g => s.invariant₁ g x)
        (s.lift x) (s.lift_spec x) +
      cocycleOfLift d η (s.pull₁ x'.val) (fun g => s.invariant₁ g x')
        (s.lift x') (s.lift_spec x') := by
    apply ContinuousH1.Cocycle.ext
    intro g
    rw [ContinuousH1.Cocycle.add_apply, cocycleOfLift_apply, cocycleOfLift_apply,
      cocycleOfLift_apply, ← η.map_add]
    congr 1
    apply Subtype.ext
    change g • (s.lift x + s.lift x') - (s.lift x + s.lift x') =
      (g • s.lift x - s.lift x) + (g • s.lift x' - s.lift x')
    rw [smul_add]
    abel
  rw [hc, map_add]
  rfl

/-- An additive map on the actual source degree-one cycle group. -/
def onCycles (η : ContinuousH1.CoefficientMap G (Kernel d) A) :
    C.Cycles₁ →+ ContinuousH1.H1 G A where
  toFun := s.chosenClass η
  map_zero' := s.chosenClass_zero η
  map_add' := s.chosenClass_add η

/-- Source boundaries have the invariant lift `pull₀ x`, and hence die. -/
theorem onCycles_boundary (η : ContinuousH1.CoefficientMap G (Kernel d) A) (x : C₀) :
    s.onCycles η (C.boundary₁ x) = 0 := by
  change s.chosenClass η (C.boundary₁ x) = 0
  rw [s.chosenClass_eq η (C.boundary₁ x) (s.pull₀ x) (s.comm₀ x)]
  exact (congrArg (ContinuousH1.classOf G A)
    (cocycleOfLift_eq_zero d η _ _ (s.pull₀ x)
      (s.comm₀ x) (fun g => s.invariant₀ g x))).trans (map_zero _)

/-- The genuine conditional source-to-native-continuous-H1 operator. -/
def transgression (η : ContinuousH1.CoefficientMap G (Kernel d) A) : C.H₁ →+ ContinuousH1.H1 G A :=
  QuotientAddGroup.lift _ (s.onCycles η) (by
    rintro _ ⟨x, rfl⟩
    exact s.onCycles_boundary η x)

@[simp] theorem transgression_class (η : ContinuousH1.CoefficientMap G (Kernel d) A)
    (x : C.Cycles₁) :
    s.transgression η (x : C.H₁) = s.chosenClass η x := rfl

/-- Formula on any source cycle and any closed-field cochain lift. -/
theorem transgression_formula (η : ContinuousH1.CoefficientMap G (Kernel d) A)
    (x : C.Cycles₁) (y : B₀) (hy : d y = s.pull₁ x.val) :
    s.transgression η (QuotientAddGroup.mk' C.boundary₁.range x) =
      ContinuousH1.classOf G A (cocycleOfLift d η (s.pull₁ x.val)
        (fun g => s.invariant₁ g x) y hy) := s.chosenClass_eq η x y hy

end SourceData

variable {D₂ D₃ : Type*} [AddCommGroup D₂] [AddCommGroup D₃]

omit [TopologicalSpace B₀] [IsTopologicalAddGroup B₀]
  [TopologicalSpace B₁] [IsTopologicalAddGroup B₁] in
/-- Vanishing of the actual closed-source H1 implies precisely the needed
cochain liftability; it is not a comparison hypothesis. -/
theorem liftable_of_H1_zero (C : Complex C₀ C₁ C₂ C₃) (D : Complex B₀ B₁ D₂ D₃)
    (f : ChainMap C D) (hzero : ∀ q : D.H₁, q = 0) :
    ∀ x : C.Cycles₁, ∃ y : B₀, D.d₀ y = f.f₁ x.val := by
  intro x
  have hz := hzero (QuotientAddGroup.mk' D.boundary₁.range (f.onCycles₁ x))
  obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
  exact ⟨y, congrArg Subtype.val hy⟩

/-- Constructor from an actual source-to-closed-source chain map. Its cochain
squares are used, and invariance and closed H1 vanishing remain explicit. -/
def sourceDataOfChainMap (C : Complex C₀ C₁ C₂ C₃) (D : Complex B₀ B₁ D₂ D₃)
    (f : ChainMap C D) (hd : ∀ y : B₀, d y = D.d₀ y)
    (hinv₀ : ∀ (g : G) (x : C₀), g • f.f₀ x = f.f₀ x)
    (hinv₁ : ∀ (g : G) (x : C.Cycles₁), g • f.f₁ x.val = f.f₁ x.val)
    (hzero : ∀ q : D.H₁, q = 0) : SourceData d C where
  pull₀ := f.f₀
  pull₁ := f.f₁
  comm₀ x := (hd _).trans (f.comm₀ x).symm
  invariant₀ := hinv₀
  invariant₁ := hinv₁
  liftable x := by
    obtain ⟨y, hy⟩ := liftable_of_H1_zero C D f hzero x
    exact ⟨y, (hd y).trans hy⟩

/-- Directly consume the existing literal mod-n quotient complex. No cone
equivalence or arbitrary finite comparison map is required. -/
def onModH1 (C : Complex C₀ C₁ C₂ C₃) (n : ℕ)
    (s : SourceData d (C.modComplex n)) : (C.modComplex n).H₁ →+ ContinuousH1.H1 G A :=
  s.transgression η

/-- The same operator consumes coefficient-cone H1 via the already constructed
positive first-component projection, whether or not it is an equivalence. -/
def onConeH1 (C : Complex C₀ C₁ C₂ C₃) (n : ℕ)
    (s : SourceData d (C.modComplex n)) : C.H₁mod n →+ ContinuousH1.H1 G A :=
  (onModH1 d η C n s).comp (C.projectMod n)

@[simp] theorem onConeH1_class (C : Complex C₀ C₁ C₂ C₃) (n : ℕ)
    (s : SourceData d (C.modComplex n)) (x : C.Cocycles n) :
    onConeH1 d η C n s (C.classMod n x) =
      s.chosenClass η (C.projectCycles n x) := rfl

end GroupCohomology.ContinuousH1.Transgression
