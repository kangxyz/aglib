/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.TorsorPoints
public import Mathlib.FieldTheory.Galois.Profinite
public import Aglib.GroupCohomology.H1.Continuous
public import Mathlib.Topology.Algebra.MulAction

/-!
Auxiliary local H1/torsor construction for
`K2-018#prop:k2018-arithmetic-characters` at source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Only the stated local conditions are covered; global class correspondence and
gluing remain separate obligations.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.ActualTorsorCocycle`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ea606c3b5232c382a4a194190261e4278eb6e4435260ea275bf756b6332265a1`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped TensorProduct

namespace Algebra.FiniteEtale.TorsorCocycle

section PointTopology
variable (K Ω A : Type*) [Field K] [Field Ω] [Algebra K Ω]
  [CommRing A] [Algebra K A] [Module.Finite K A]

@[instance_reducible] def pointAction : MulAction (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω) where
  smul sigma f := sigma.toAlgHom.comp f
  one_smul f := by ext a; rfl
  mul_smul sigma tau f := by ext a; rfl

local instance : MulAction (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω) := pointAction K Ω A
local instance : TopologicalSpace (A →ₐ[K] Ω) := ⊥
local instance : DiscreteTopology (A →ₐ[K] Ω) := ⟨rfl⟩

theorem point_stabilizer_open (f : A →ₐ[K] Ω) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[K] Ω) f : Set (Ω ≃ₐ[K] Ω)) := by
  haveI : Module.Finite K f.range :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  have hfield : IsField f.range :=
    isField_of_isIntegral_of_isField' (R := K) (S := f.range) (Field.toIsField K)
  let E := f.range.toIntermediateField' hfield
  haveI : FiniteDimensional K E := (inferInstance : Module.Finite K f.range)
  convert E.fixingSubgroup_isOpen using 1
  ext sigma
  change sigma • f = f ↔ sigma ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change sigma.toAlgHom.comp f = f ↔ ∀ x ∈ E, sigma x = x
  constructor
  · intro hsigma x hx
    obtain ⟨a, ha⟩ : ∃ a, f a = x := hx
    rw [← ha]
    exact DFunLike.congr_fun hsigma a
  · intro hsigma
    ext a
    exact hsigma (f a) ⟨a, rfl⟩


theorem point_orbit_continuous (f : A →ₐ[K] Ω) :
    Continuous (fun sigma : Ω ≃ₐ[K] Ω => sigma.toAlgHom.comp f) := by
  letI : ContinuousSMul (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (point_stabilizer_open K Ω A)
  exact continuous_id.smul continuous_const

end PointTopology

section CoactionPoints

open Algebra.FiniteEtale.GenericMaps Algebra.FiniteEtale.TorsorExtension
universe u v
variable (K Ω A C : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]
  {epsilon : C →ₐ[K] K} {delta : C →ₐ[K] C ⊗[K] C}
  (alpha : AlgebraCoaction K A C epsilon delta)

/-- Positive translation is evaluated using the ORIGINAL generic coaction. -/
def translate (h : C →ₐ[K] Ω) (f : A →ₐ[K] Ω) : A →ₐ[K] Ω :=
  (Algebra.TensorProduct.lift f h (fun _ _ => .all _ _)).comp alpha.coact

/-- The actual transporter gives uniqueness of its coefficient coordinate. -/
theorem translate_injective
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω) :
    Function.Injective (fun h : C →ₐ[K] Ω => translate K Ω A C alpha h f) := by
  intro h₁ h₂ heq
  let psi₁ := Algebra.TensorProduct.lift f h₁ (fun _ _ => .all _ _)
  let psi₂ := Algebra.TensorProduct.lift f h₂ (fun _ _ => .all _ _)
  have ht : psi₁.comp (transporter K A C alpha.coact) =
      psi₂.comp (transporter K A C alpha.coact) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    have hb := DFunLike.congr_fun heq b
    change psi₁ (alpha.coact b) = psi₂ (alpha.coact b) at hb
    simp only [AlgHom.comp_apply, transporter, Algebra.TensorProduct.lift_tmul,
      map_mul, Algebra.TensorProduct.includeLeft_apply, psi₁, psi₂, map_one, mul_one]
    exact congrArg (fun y : Ω => f a * y) hb
  have hpsi : psi₁ = psi₂ := by
    apply AlgHom.ext
    intro z
    obtain ⟨t, rfl⟩ := hT.surjective z
    exact DFunLike.congr_fun ht t
  ext c
  have hv := DFunLike.congr_fun hpsi ((1 : A) ⊗ₜ[K] c)
  simpa only [psi₁, psi₂, Algebra.TensorProduct.lift_tmul, map_one, one_mul] using hv

/-- The coordinate equivalence comes from the actual transporter, not a
replacement torsor or a supplied rational trivialization. -/
def coefficientPointEquiv
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω) :
    (C →ₐ[K] Ω) ≃ (A →ₐ[K] Ω) :=
  Equiv.ofBijective (fun h => translate K Ω A C alpha h f)
    ⟨translate_injective K Ω A C alpha hT f,
      fun g => exists_coefficient_point K Ω A C alpha.coact hT f g⟩

variable (Lambda : Type v) [AddCommGroup Lambda]
  (mark : Lambda ≃ (C →ₐ[K] Ω))
  (hzero : mark 0 = (Algebra.ofId K Ω).comp epsilon)
  (hadd : ∀ x y, mark (x + y) =
    (Algebra.TensorProduct.lift (mark x) (mark y) (fun _ _ => .all _ _)).comp delta)

include hzero in
/-- Zero in the actual coefficient coordinates is the genuine counit point. -/
theorem translate_zero (f : A →ₐ[K] Ω) : translate K Ω A C alpha (mark 0) f = f := by
  have heval : Algebra.TensorProduct.lift f ((Algebra.ofId K Ω).comp epsilon)
      (fun _ _ => .all _ _) = f.comp (coactionCounit K A C epsilon) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [coactionCounit, Algebra.smul_def, mul_comm]
  rw [translate, hzero, heval, AlgHom.comp_assoc, alpha.counit]
  ext a
  rfl

include hadd in
/-- Addition of coordinates is evaluated through the actual Delta and the
original generic coassociativity law. -/
theorem translate_add (x y : Lambda) (f : A →ₐ[K] Ω) :
    translate K Ω A C alpha (mark (x + y)) f =
      translate K Ω A C alpha (mark y) (translate K Ω A C alpha (mark x) f) := by
  let psi : (A ⊗[K] (C ⊗[K] C)) →ₐ[K] Ω :=
    Algebra.TensorProduct.lift f
      (Algebra.TensorProduct.lift (mark x) (mark y) (fun _ _ => .all _ _))
      (fun _ _ => .all _ _)
  have hleft : Algebra.TensorProduct.lift f (mark (x + y)) (fun _ _ => .all _ _) =
      psi.comp (Algebra.TensorProduct.map (AlgHom.id K A) delta) := by
    rw [hadd]
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [psi]
  have hright : Algebra.TensorProduct.lift
      (translate K Ω A C alpha (mark x) f) (mark y) (fun _ _ => .all _ _) =
      (psi.comp (Algebra.TensorProduct.assoc K K K A C C).toAlgHom).comp
        (Algebra.TensorProduct.map alpha.coact (AlgHom.id K C)) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    change (Algebra.TensorProduct.lift f (mark x) (fun _ _ => .all _ _) (alpha.coact a)) *
        mark y c = psi ((Algebra.TensorProduct.assoc K K K A C C) ((alpha.coact a) ⊗ₜ[K] c))
    generalize alpha.coact a = z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [psi, mul_assoc]
    | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, add_mul, hz, hw]
  ext a
  have hcoassoc := congrArg psi (DFunLike.congr_fun alpha.coassoc a)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hcoassoc
  exact (DFunLike.congr_fun hleft (alpha.coact a)).trans
    (hcoassoc.trans (DFunLike.congr_fun hright (alpha.coact a)).symm)

variable [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  (hmark : ∀ (sigma : Ω ≃ₐ[K] Ω) x,
    sigma.toAlgHom.comp (mark x) = mark (sigma • x))

include hmark in
/-- The semilinear action is literal postcomposition on both actual point sets. -/
theorem translate_equivariant (sigma : Ω ≃ₐ[K] Ω) (x : Lambda) (f : A →ₐ[K] Ω) :
    sigma.toAlgHom.comp (translate K Ω A C alpha (mark x) f) =
      translate K Ω A C alpha (mark (sigma • x)) (sigma.toAlgHom.comp f) := by
  have ht : sigma.toAlgHom.comp
      (Algebra.TensorProduct.lift f (mark x) (fun _ _ => .all _ _)) =
      Algebra.TensorProduct.lift (sigma.toAlgHom.comp f) (mark (sigma • x))
        (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    have hc := DFunLike.congr_fun (hmark sigma x) c
    change sigma (f a * mark x c) = sigma (f a) * mark (sigma • x) c
    rw [map_mul]
    exact congrArg (fun y : Ω => sigma (f a) * y) hc
  simpa only [translate, AlgHom.comp_assoc] using congrArg (fun z => z.comp alpha.coact) ht


/-- The actual coefficient mark followed by the actual transporter coordinates. -/
def pointCoordinates
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω) :
    Lambda ≃ (A →ₐ[K] Ω) :=
  mark.trans (coefficientPointEquiv K Ω A C alpha hT f)

omit [AddCommGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda] in
@[simp] theorem pointCoordinates_apply
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω) (x : Lambda) :
    pointCoordinates K Ω A C alpha Lambda mark hT f x =
      translate K Ω A C alpha (mark x) f := rfl

variable [Module.Finite K A] [TopologicalSpace Lambda]
  [IsTopologicalAddGroup Lambda] [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]

local instance : TopologicalSpace (A →ₐ[K] Ω) := ⊥
local instance : DiscreteTopology (A →ₐ[K] Ω) := ⟨rfl⟩

include hadd hmark in
/-- The continuous cocycle is positive transport from the chosen ORIGINAL
A-point f to sigma(f), in the supplied actual coefficient coordinates. -/
def basedCocycle
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω) :
    _root_.GroupCohomology.ContinuousH1.Cocycle (Ω ≃ₐ[K] Ω) Lambda := by
  let e := pointCoordinates K Ω A C alpha Lambda mark hT f
  let value := fun sigma : Ω ≃ₐ[K] Ω => e.symm (sigma.toAlgHom.comp f)
  have hvalue (sigma : Ω ≃ₐ[K] Ω) :
      translate K Ω A C alpha (mark (value sigma)) f = sigma.toAlgHom.comp f :=
    e.apply_symm_apply _
  have hcontinuous : Continuous value :=
    (continuous_of_discreteTopology (f := e.symm)).comp (point_orbit_continuous K Ω A f)
  refine ⟨⟨value, hcontinuous⟩, ?_⟩
  intro sigma tau
  apply e.injective
  change e (value (sigma * tau)) = e (value sigma + sigma • value tau)
  calc
    e (value (sigma * tau)) = (sigma * tau).toAlgHom.comp f := e.apply_symm_apply _
    _ = sigma.toAlgHom.comp (tau.toAlgHom.comp f) := by ext a; rfl
    _ = sigma.toAlgHom.comp
        (translate K Ω A C alpha (mark (value tau)) f) :=
      congrArg (fun z => sigma.toAlgHom.comp z) (hvalue tau).symm
    _ = translate K Ω A C alpha (mark (sigma • value tau)) (sigma.toAlgHom.comp f) :=
      translate_equivariant K Ω A C alpha Lambda mark hmark sigma (value tau) f
    _ = translate K Ω A C alpha (mark (sigma • value tau))
        (translate K Ω A C alpha (mark (value sigma)) f) :=
      congrArg (translate K Ω A C alpha (mark (sigma • value tau))) (hvalue sigma).symm
    _ = translate K Ω A C alpha (mark (value sigma + sigma • value tau)) f :=
      (translate_add K Ω A C alpha Lambda mark hadd (value sigma) (sigma • value tau) f).symm
    _ = e (value sigma + sigma • value tau) := rfl

omit [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda] in
include hadd hmark in
/-- The cocycle's sign and object are fixed by this literal original-A equation. -/
theorem basedCocycle_action
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω)
    (sigma : Ω ≃ₐ[K] Ω) :
    translate K Ω A C alpha
        (mark ((basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f).val sigma)) f =
      sigma.toAlgHom.comp f :=
  (pointCoordinates K Ω A C alpha Lambda mark hT f).apply_symm_apply _

include hadd hmark in
/-- Changing the internal ORIGINAL-A point adds the standard positive principal
cocycle. The coefficient is its actual transporter coordinate. -/
theorem basedCocycle_change
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f g : A →ₐ[K] Ω) :
    basedCocycle K Ω A C alpha Lambda mark hadd hmark hT g =
      basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f +
        _root_.GroupCohomology.ContinuousH1.principal (Ω ≃ₐ[K] Ω) Lambda
          ((pointCoordinates K Ω A C alpha Lambda mark hT f).symm g) := by
  let a := (pointCoordinates K Ω A C alpha Lambda mark hT f).symm g
  have hga : translate K Ω A C alpha (mark a) f = g :=
    (pointCoordinates K Ω A C alpha Lambda mark hT f).apply_symm_apply g
  have hinj : Function.Injective (fun z : Lambda => translate K Ω A C alpha (mark z) f) :=
    (translate_injective K Ω A C alpha hT f).comp mark.injective
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro sigma
  let cf := basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f
  let cg := basedCocycle K Ω A C alpha Lambda mark hadd hmark hT g
  have hcoord : a + cg.val sigma = cf.val sigma + sigma • a := by
    apply hinj
    calc
      translate K Ω A C alpha (mark (a + cg.val sigma)) f =
          translate K Ω A C alpha (mark (cg.val sigma)) g :=
        (translate_add K Ω A C alpha Lambda mark hadd a (cg.val sigma) f).trans
          (congrArg (translate K Ω A C alpha (mark (cg.val sigma))) hga)
      _ = sigma.toAlgHom.comp g :=
        basedCocycle_action K Ω A C alpha Lambda mark hadd hmark hT g sigma
      _ = sigma.toAlgHom.comp (translate K Ω A C alpha (mark a) f) :=
        congrArg (fun z => sigma.toAlgHom.comp z) hga.symm
      _ = translate K Ω A C alpha (mark (sigma • a)) (sigma.toAlgHom.comp f) :=
        translate_equivariant K Ω A C alpha Lambda mark hmark sigma a f
      _ = translate K Ω A C alpha (mark (sigma • a))
          (translate K Ω A C alpha (mark (cf.val sigma)) f) :=
        congrArg (translate K Ω A C alpha (mark (sigma • a)))
          (basedCocycle_action K Ω A C alpha Lambda mark hadd hmark hT f sigma).symm
      _ = translate K Ω A C alpha (mark (cf.val sigma + sigma • a)) f :=
        (translate_add K Ω A C alpha Lambda mark hadd (cf.val sigma) (sigma • a) f).symm
  simp only [_root_.GroupCohomology.ContinuousH1.Cocycle.add_apply,
    _root_.GroupCohomology.ContinuousH1.principal_apply]
  have hz : cg.val sigma = cf.val sigma + sigma • a - a :=
    (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hcoord)
  exact hz.trans (by abel)

include hadd hmark in
/-- The constructed class is independent of the chosen actual geometric point. -/
theorem basedCocycle_class_independent
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f g : A →ₐ[K] Ω) :
    _root_.GroupCohomology.ContinuousH1.classOf (Ω ≃ₐ[K] Ω) Lambda
        (basedCocycle K Ω A C alpha Lambda mark hadd hmark hT g) =
      _root_.GroupCohomology.ContinuousH1.classOf (Ω ≃ₐ[K] Ω) Lambda
        (basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f) := by
  rw [basedCocycle_change, map_add, _root_.GroupCohomology.ContinuousH1.classOf_principal, add_zero]

/-- Actual subgroup inclusion, with inherited Krull topology. -/
def subgroupInclusion (I : Subgroup (Ω ≃ₐ[K] Ω)) :
    ContinuousMonoidHom I (Ω ≃ₐ[K] Ω) where
  toMonoidHom := I.subtype
  continuous_toFun := continuous_subtype_val

include hadd hmark in
/-- Vanishing in the EXISTING continuous H1 quotient on I gives a fixed
geometric point of the ORIGINAL algebra A. It is constructed as translation
of f by the negative coboundary coordinate, never as an abstract affine point. -/
theorem fixed_point_of_restriction_zero
    (hT : Function.Bijective (transporter K A C alpha.coact)) (f : A →ₐ[K] Ω)
    (I : Subgroup (Ω ≃ₐ[K] Ω))
    (hvan :
      letI := _root_.GroupCohomology.ContinuousH1.restrictedAction Lambda (subgroupInclusion K Ω I)
      letI := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous Lambda
        (subgroupInclusion K Ω I)
      _root_.GroupCohomology.ContinuousH1.restriction Lambda (subgroupInclusion K Ω I)
        (_root_.GroupCohomology.ContinuousH1.classOf (Ω ≃ₐ[K] Ω) Lambda
          (basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f)) = 0) :
    ∃ g : A →ₐ[K] Ω, ∀ sigma : I, sigma.val.toAlgHom.comp g = g := by
  let c := basedCocycle K Ω A C alpha Lambda mark hadd hmark hT f
  let phi := subgroupInclusion K Ω I
  letI := _root_.GroupCohomology.ContinuousH1.restrictedAction Lambda phi
  letI := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous Lambda phi
  have hz : _root_.GroupCohomology.ContinuousH1.classOf I Lambda
      (_root_.GroupCohomology.ContinuousH1.restrictionCocycles Lambda phi c) = 0 := hvan
  obtain ⟨a, ha⟩ := (_root_.GroupCohomology.ContinuousH1.classOf_eq_zero_iff I Lambda _).mp hz
  refine ⟨translate K Ω A C alpha (mark (-a)) f, fun sigma => ?_⟩
  have hca := congrArg
    (fun z : _root_.GroupCohomology.ContinuousH1.Cocycle I Lambda => z.val sigma) ha
  change sigma.val • a - a = c.val sigma.val at hca
  calc
    sigma.val.toAlgHom.comp (translate K Ω A C alpha (mark (-a)) f) =
        translate K Ω A C alpha (mark (sigma.val • (-a))) (sigma.val.toAlgHom.comp f) :=
      translate_equivariant K Ω A C alpha Lambda mark hmark sigma.val (-a) f
    _ = translate K Ω A C alpha (mark (sigma.val • (-a)))
        (translate K Ω A C alpha (mark (c.val sigma.val)) f) :=
      congrArg (translate K Ω A C alpha (mark (sigma.val • (-a))))
        (basedCocycle_action K Ω A C alpha Lambda mark hadd hmark hT f sigma.val).symm
    _ = translate K Ω A C alpha (mark (c.val sigma.val + sigma.val • (-a))) f :=
      (translate_add K Ω A C alpha Lambda mark hadd (c.val sigma.val) (sigma.val • (-a)) f).symm
    _ = translate K Ω A C alpha (mark (-a)) f := by
      rw [← hca, smul_neg]
      congr 2
      abel

end CoactionPoints

end Algebra.FiniteEtale.TorsorCocycle
