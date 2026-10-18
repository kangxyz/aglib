/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.GroupCohomology.H1.SplitExtension
public import Aglib.TopologicalGroup.SplitExtension

/-!
# Continuous H1 in actual split-extension coordinates

A6, K2-018 `eq:k2018-pointed-character` and
`prop:k2018-arithmetic-characters`; mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Inputs are actual continuous group homomorphisms p : E → G and s : G → E,
with p ∘ s = id, and a continuous additive G-module A. The E-action is
literally inflation along p; the actual kernel action is conjugation by s.
SplitExtension supplies the proved coordinate group/homeomorphism formulas.
The forward cocycle is c(n * s(g)); the inverse uses e ↦ (e*s(p(e))⁻¹,p(e)).

Both additive H1 maps descend through the existing common quotient. Only
PointedCohomology's public continuousH1Mk/continuousH1Lift are used; its private
coordinate type is not accessed and no second H1 quotient is introduced.
The G-to-PUnit adapter proves the actual section square. The resulting pointed
kernel equivalence has geometric representative c(n), not an arbitrary additive
automorphism. No scheme, finite-coefficient or external theorem premise is used.
The actual etale/pi1 comparison and essay specialization remain separate layers.
-/

@[expose] public section

noncomputable section
namespace GroupCohomology.SplitCoordinates
open GroupCohomology TopologicalGroup
variable {E G A : Type*} [Group E] [Group G]
  [TopologicalSpace E] [TopologicalSpace G] [IsTopologicalGroup E]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable (p : ContinuousMonoidHom E G) (s : ContinuousMonoidHom G E)
  (hps : ∀ g, p (s g) = g)
/-- Actual continuous cocycles with coefficient action inflated along p. -/
abbrev InflatedCocycle :=
  letI := ContinuousH1.restrictedAction A p
  ContinuousH1.Cocycle E A

/-- Existing coordinate cocycles with the constructed conjugation action. -/
abbrev CoordinateCocycle :=
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  PointedCohomology.ContinuousCocycle G p.toMonoidHom.ker A

/-- Evaluate a genuine cocycle on the proved inverse coordinate map. -/
def toCoordinateCocycle : InflatedCocycle (A := A) p →+ CoordinateCocycle (A := A) p s := by
  letI := ContinuousH1.restrictedAction A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact {
    toFun c := {
      toFun x := c.val (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom
        s.toMonoidHom x)
      continuous_toFun := c.continuous.comp
        (TopologicalGroup.SplitExtension.continuous_fromCoordinates p.toMonoidHom s.toMonoidHom
          s.continuous)
      cocycle := by
        intro u v g h
        rw [TopologicalGroup.SplitExtension.fromCoordinates_mul_action, c.map_mul]
        change c.val _ + p (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom
          s.toMonoidHom (u, g)) • c.val _ = c.val _ + g • c.val _
        have hp : p (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom s.toMonoidHom
          (u, g)) = g :=
          TopologicalGroup.SplitExtension.projection_fromCoordinates _ _ hps (u, g)
        rw [hp] }
    map_zero' := by ext x; rfl
    map_add' c d := by ext x; rfl }

/-- Evaluate a coordinate cocycle on the proved coordinate homeomorphism. -/
def fromCoordinateCocycle : CoordinateCocycle (A := A) p s →+ InflatedCocycle (A := A) p := by
  letI := ContinuousH1.restrictedAction A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact {
    toFun c := ⟨⟨fun e => c.toFun (TopologicalGroup.SplitExtension.toCoordinates p.toMonoidHom
      s.toMonoidHom hps e),
      c.continuous_toFun.comp (TopologicalGroup.SplitExtension.continuous_toCoordinates _ _ hps
        p.continuous s.continuous)⟩,
      by
        intro e f
        change c.toFun (TopologicalGroup.SplitExtension.toCoordinates _ _ _ (e*f)) = _
        rw [TopologicalGroup.SplitExtension.toCoordinates_mul]
        exact c.cocycle _ _ _ _⟩
    map_zero' := by ext x; rfl
    map_add' c d := by ext x; rfl }

/-- Additive coordinate equivalence before passing to cohomology. -/
def cocycleAddEquiv : InflatedCocycle (A := A) p ≃+ CoordinateCocycle (A := A) p s := by
  letI := ContinuousH1.restrictedAction A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact {
    __ := toCoordinateCocycle (A := A) p s hps
    invFun := fromCoordinateCocycle (A := A) p s hps
    left_inv c := by
      apply ContinuousH1.Cocycle.ext
      intro e
      change c.val (TopologicalGroup.SplitExtension.fromCoordinates _ _
        (TopologicalGroup.SplitExtension.toCoordinates _ _ _ e)) = c.val e
      rw [TopologicalGroup.SplitExtension.fromCoordinates_toCoordinates]
    right_inv c := by
      apply PointedCohomology.ContinuousCocycle.ext
      intro x
      change c.toFun (TopologicalGroup.SplitExtension.toCoordinates _ _ _
        (TopologicalGroup.SplitExtension.fromCoordinates _ _ x)) = c.toFun x
      rw [TopologicalGroup.SplitExtension.toCoordinates_fromCoordinates] }

/-- The existing common continuous H1, with the actual inflated action. -/
abbrev InflatedH1 :=
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction_continuous A p
  ContinuousH1.H1 E A

/-- The frozen pointed-coordinate presentation of the same common H1 quotient. -/
abbrev CoordinateH1 :=
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  PointedCohomology.ContinuousH1 (G := G) (N := p.toMonoidHom.ker) (A := A)

/-- Forward map through the existing quotient universal property. -/
def toCoordinateH1 : InflatedH1 (A := A) p →+ CoordinateH1 (A := A) p s := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction_continuous A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact QuotientAddGroup.lift (ContinuousH1.coboundaries E A)
    (PointedCohomology.continuousH1Mk.comp (toCoordinateCocycle (A := A) p s hps)) (by
      rintro c ⟨a, rfl⟩
      apply (PointedCohomology.continuousH1Mk_eq_zero_iff _).2
      refine ⟨a, fun u g => ?_⟩
      change p (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom s.toMonoidHom
        (u, g)) • a - a = g • a - a
      exact congrArg (fun k : G => k • a - a)
        (TopologicalGroup.SplitExtension.projection_fromCoordinates _ _ hps (u, g)))

/-- Inverse map using only the public coordinate quotient lift. -/
def fromCoordinateH1 : CoordinateH1 (A := A) p s →+ InflatedH1 (A := A) p := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction_continuous A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact PointedCohomology.continuousH1Lift
    ((ContinuousH1.classOf E A).comp (fromCoordinateCocycle (A := A) p s hps)) (by
      rintro c ⟨a, rfl⟩
      change ContinuousH1.classOf E A _ = 0
      have heq : fromCoordinateCocycle (A := A) p s hps
          (PointedCohomology.coboundaryHom (G := G) (N := p.toMonoidHom.ker) a) =
          ContinuousH1.principal E A a := by
        apply ContinuousH1.Cocycle.ext
        intro e
        rfl
      rw [heq, ContinuousH1.classOf_principal])

/-- Actual continuous split-extension H1 in the existing coordinate model. -/
def h1AddEquiv : InflatedH1 (A := A) p ≃+ CoordinateH1 (A := A) p s := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction_continuous A p
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact {
    __ := toCoordinateH1 (A := A) p s hps
    invFun := fromCoordinateH1 (A := A) p s hps
    left_inv x := by
      obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective E A x
      change ContinuousH1.classOf E A (fromCoordinateCocycle p s hps (toCoordinateCocycle p s hps
        c)) = _
      rw [show fromCoordinateCocycle p s hps (toCoordinateCocycle p s hps c) = c from
        (cocycleAddEquiv (A := A) p s hps).left_inv c]
    right_inv x := by
      obtain ⟨c, rfl⟩ := PointedCohomology.continuousH1Mk_surjective x
      change PointedCohomology.continuousH1Mk (toCoordinateCocycle p s hps (fromCoordinateCocycle
        p s hps c)) = _
      rw [show toCoordinateCocycle p s hps (fromCoordinateCocycle p s hps c) = c from
        (cocycleAddEquiv (A := A) p s hps).right_inv c] }

section SectionAdapter
variable (G A)
/-- The trivial geometric-coordinate adapter for a G-cocycle. -/
def sectionToCocycle : ContinuousH1.Cocycle G A →+
    PointedCohomology.ContinuousCocycle G PUnit.{1} A where
  toFun c := {
    toFun x := c.val x.2
    continuous_toFun := c.continuous.comp continuous_snd
    cocycle _ _ g h := c.map_mul g h }
  map_zero' := by ext x; rfl
  map_add' c d := by ext x; rfl

/-- Recover a G-cocycle by evaluating its unique PUnit coordinate. -/
def sectionFromCocycle : PointedCohomology.ContinuousCocycle G PUnit.{1} A →+
    ContinuousH1.Cocycle G A where
  toFun c := ⟨⟨fun g => c.toFun (PUnit.unit, g),
    c.continuous_toFun.comp (continuous_const.prodMk continuous_id)⟩,
    fun g h => c.cocycle PUnit.unit PUnit.unit g h⟩
  map_zero' := by ext x; rfl
  map_add' c d := by ext x; rfl

/-- Descend the G-to-PUnit coordinate adapter. -/
def sectionToH1 : ContinuousH1.H1 G A →+
    PointedCohomology.ContinuousH1 (G := G) (N := PUnit.{1}) (A := A) :=
  QuotientAddGroup.lift (ContinuousH1.coboundaries G A)
    (PointedCohomology.continuousH1Mk.comp (sectionToCocycle G A)) (by
      rintro c ⟨a, rfl⟩
      apply (PointedCohomology.continuousH1Mk_eq_zero_iff _).2
      exact ⟨a, fun _ _ => rfl⟩)

/-- Descend the inverse PUnit coordinate adapter. -/
def sectionFromH1 : PointedCohomology.ContinuousH1 (G := G) (N := PUnit.{1}) (A := A) →+
    ContinuousH1.H1 G A :=
  PointedCohomology.continuousH1Lift
    ((ContinuousH1.classOf G A).comp (sectionFromCocycle G A)) (by
      rintro c ⟨a, rfl⟩
      exact ContinuousH1.classOf_principal G A a)

/-- The base G cohomology in the frozen PUnit-coordinate model. -/
def sectionH1AddEquiv : ContinuousH1.H1 G A ≃+
    PointedCohomology.ContinuousH1 (G := G) (N := PUnit.{1}) (A := A) where
  __ := sectionToH1 G A
  invFun := sectionFromH1 G A
  left_inv x := by
    obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective G A x
    rfl
  right_inv x := by
    obtain ⟨c, rfl⟩ := PointedCohomology.continuousH1Mk_surjective x
    change PointedCohomology.continuousH1Mk (sectionToCocycle G A (sectionFromCocycle G A c)) = _
    congr 1
end SectionAdapter

/-- Identity on coefficients, equivariant along s because p ∘ s = id. -/
def sectionPullbackMap :
    letI := ContinuousH1.restrictedAction A p
    ContinuousH1.PullbackMap (A := A) (B := A) s := by
  letI := ContinuousH1.restrictedAction A p
  exact {
    toContinuousAddMonoidHom := ContinuousAddMonoidHom.id A
    map_smul' := by
      intro g a
      change p (s g) • a = g • a
      rw [hps] }

/-- Actual continuous cohomology restriction along the chosen section. -/
def sectionRestriction : InflatedH1 (A := A) p →+ ContinuousH1.H1 G A := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction_continuous A p
  exact (sectionPullbackMap (A := A) p s hps).onH1

/-- The coordinate equivalence commutes with actual section restriction. -/
theorem section_square (x : InflatedH1 (A := A) p) :
    let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    PointedCohomology.continuousH1SectionRestriction (h1AddEquiv (A := A) p s hps x) =
      sectionH1AddEquiv G A (sectionRestriction (A := A) p s hps x) := by
  let := ContinuousH1.restrictedAction A p
  let := ContinuousH1.restrictedAction_continuous A p
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective E A x
  change PointedCohomology.continuousH1Mk
    (PointedCohomology.sectionCocycleHom (toCoordinateCocycle p s hps c)) =
    PointedCohomology.continuousH1Mk
      (sectionToCocycle G A ((sectionPullbackMap (A := A) p s hps).onCocycles c))
  congr 1
  apply PointedCohomology.ContinuousCocycle.ext
  rintro ⟨u, g⟩
  change c.val (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom s.toMonoidHom
    (1, g)) = c.val (s g)
  rw [TopologicalGroup.SplitExtension.fromCoordinates_section]
  rfl

/-- The actual kernel of restriction along the chosen continuous section. -/
def PointedKernel : AddSubgroup (InflatedH1 (A := A) p) :=
  (sectionRestriction (A := A) p s hps).ker

/-- The kernel of the actual section map equals the frozen pointed H1. -/
def pointedH1AddEquiv :
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    PointedKernel (A := A) p s hps ≃+
      PointedCohomology.PointedH1 (G := G) (N := p.toMonoidHom.ker) (A := A) := by
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact {
    toFun x := ⟨h1AddEquiv (A := A) p s hps x.val, by
      change PointedCohomology.continuousH1SectionRestriction _ = 0
      rw [section_square]
      have hx : sectionRestriction (A := A) p s hps x.val = 0 := x.property
      rw [hx, map_zero]⟩
    invFun x := ⟨(h1AddEquiv (A := A) p s hps).symm x.val, by
      change sectionRestriction (A := A) p s hps _ = 0
      apply (sectionH1AddEquiv G A).injective
      rw [map_zero, ← section_square, (h1AddEquiv (A := A) p s hps).apply_symm_apply]
      exact x.property⟩
    left_inv x := by apply Subtype.ext; exact (h1AddEquiv (A := A) p s hps).symm_apply_apply _
    right_inv x := by apply Subtype.ext; exact (h1AddEquiv (A := A) p s hps).apply_symm_apply _
    map_add' x y := by apply Subtype.ext; exact map_add _ _ _ }

/-- The new equivalence uses the public constructor of the existing common quotient. -/
@[simp] theorem h1AddEquiv_classOf (c : InflatedCocycle (A := A) p) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    h1AddEquiv (A := A) p s hps (ContinuousH1.classOf E A c) =
      PointedCohomology.continuousH1Mk (toCoordinateCocycle p s hps c) := rfl

/-- Geometric restriction is literally evaluation on the actual kernel subgroup. -/
theorem geometric_classOf (c : InflatedCocycle (A := A) p) (n : p.toMonoidHom.ker) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    (PointedCohomology.geometricH1Hom
      (h1AddEquiv (A := A) p s hps (ContinuousH1.classOf E A c))).toFun n = c.val n := by
  change c.val (TopologicalGroup.SplitExtension.fromCoordinates p.toMonoidHom s.toMonoidHom
    (n, 1)) = c.val n
  rw [TopologicalGroup.SplitExtension.fromCoordinates_kernel]

/-- The actual section kernel, identified with the existing equivariant characters. -/
def pointedCharacterEquiv :
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    PointedKernel (A := A) p s hps ≃+
      PointedCohomology.EquivariantCharacter G p.toMonoidHom.ker A := by
  letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  exact (pointedH1AddEquiv (A := A) p s hps).trans PointedCohomology.pointedH1AddEquiv

end GroupCohomology.SplitCoordinates

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 966b8ebcc4f7c979a857e2d052cc4eab8495f312558383b70abf37fb1b42b0a8.
Definitions, hypotheses and universes are retained modulo native names. -/
