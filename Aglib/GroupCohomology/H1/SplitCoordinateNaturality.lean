/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.GroupCohomology.H1.SplitCoordinates
public import Aglib.GroupCohomology.H1.SplitCoefficients

/-!
# Coefficient naturality of actual split coordinates

Auxiliary continuous coefficient algebra for K2-018
`eq:k2018-coefficient-compatibility` and `eq:k2018-pointed-character`, at
mathematical snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982` and frozen
engineering basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For actual continuous homomorphisms p : E → G and s : G → E with p ∘ s = id,
coefficient maps are inflated literally along p. The constructed cocycle and H1
coordinate equivalences commute with the frozen coefficient maps, as do actual
section restriction, its kernel, and the geometric-character equivalence.
All quotient proofs use the public constructors of the existing common H1.
No scheme, finiteness, comparison, or external classification premise is used.
-/

@[expose] public section

noncomputable section
namespace GroupCohomology.SplitCoordinateNaturality

open GroupCohomology TopologicalGroup
open SplitCoordinates

variable {E G A B : Type*} [Group E] [Group G]
  [TopologicalSpace E] [TopologicalSpace G] [IsTopologicalGroup E]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]

variable (p : ContinuousMonoidHom E G) (s : ContinuousMonoidHom G E)
  (hps : ∀ g, p (s g) = g) (ψ : ContinuousH1.CoefficientMap G A B)

/-- The original coefficient map, equivariant for both actions inflated along p. -/
def inflatedCoefficientMap :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction B p
    ContinuousH1.CoefficientMap E A B := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction B p
  exact {
    toContinuousAddMonoidHom := ψ.toContinuousAddMonoidHom
    map_smul' e a := ψ.map_smul (p e) a }

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Inflation does not change the underlying coefficient function. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[simp, nolint simpNF unusedArguments] theorem inflatedCoefficientMap_apply (a : A) :
    inflatedCoefficientMap p ψ a = ψ a := rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Coordinate transport commutes with literal postcomposition of cocycles. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem cocycleAddEquiv_naturality (c : InflatedCocycle (A := A) p) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction B p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := ContinuousH1.restrictedAction_continuous B p
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    cocycleAddEquiv (A := B) p s hps ((inflatedCoefficientMap p ψ).onCocycles c) =
      CoefficientFunctoriality.cocycleMap ψ.toContinuousAddMonoidHom.toAddMonoidHom
        ψ.continuous ψ.map_smul (cocycleAddEquiv (A := A) p s hps c) := by
  rfl

/-- The actual H1 coordinate equivalence is natural under coefficient maps. -/
theorem h1AddEquiv_naturality (x : InflatedH1 (A := A) p) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction B p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := ContinuousH1.restrictedAction_continuous B p
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    h1AddEquiv (A := B) p s hps ((inflatedCoefficientMap p ψ).onH1 x) =
      CoefficientFunctoriality.h1Map ψ.toContinuousAddMonoidHom.toAddMonoidHom
        ψ.continuous ψ.map_smul (h1AddEquiv (A := A) p s hps x) := by
  let := ContinuousH1.restrictedAction A p
  let := ContinuousH1.restrictedAction B p
  let := ContinuousH1.restrictedAction_continuous A p
  let := ContinuousH1.restrictedAction_continuous B p
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective E A x
  rfl

/-- The PUnit-coordinate adapter for base cohomology respects coefficients. -/
theorem sectionH1AddEquiv_naturality (x : ContinuousH1.H1 G A) :
    sectionH1AddEquiv G B (ψ.onH1 x) =
      CoefficientFunctoriality.h1Map (N := PUnit.{1})
        ψ.toContinuousAddMonoidHom.toAddMonoidHom ψ.continuous ψ.map_smul
        (sectionH1AddEquiv G A x) := by
  obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective G A x
  rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Actual restriction along s commutes with the original coefficient map. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem sectionRestriction_naturality (x : InflatedH1 (A := A) p) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction B p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := ContinuousH1.restrictedAction_continuous B p
    sectionRestriction (A := B) p s hps ((inflatedCoefficientMap p ψ).onH1 x) =
      ψ.onH1 (sectionRestriction (A := A) p s hps x) := by
  let := ContinuousH1.restrictedAction A p
  let := ContinuousH1.restrictedAction B p
  let := ContinuousH1.restrictedAction_continuous A p
  let := ContinuousH1.restrictedAction_continuous B p
  obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective E A x
  rfl

/-- The coefficient map on the kernel of actual section restriction. -/
def pointedKernelMap : PointedKernel (A := A) p s hps →+
    PointedKernel (A := B) p s hps := by
  letI := ContinuousH1.restrictedAction A p
  letI := ContinuousH1.restrictedAction B p
  letI := ContinuousH1.restrictedAction_continuous A p
  letI := ContinuousH1.restrictedAction_continuous B p
  exact {
    toFun x := ⟨(inflatedCoefficientMap p ψ).onH1 x.val, by
      change sectionRestriction (A := B) p s hps _ = 0
      rw [sectionRestriction_naturality]
      have hx : sectionRestriction (A := A) p s hps x.val = 0 := x.property
      rw [hx, map_zero]⟩
    map_zero' := Subtype.ext (map_zero _)
    map_add' x y := Subtype.ext (map_add _ _ _) }

/-- The pointed coefficient map is the restriction of the actual H1 map. -/
@[simp] theorem pointedKernelMap_coe (x : PointedKernel (A := A) p s hps) :
    letI := ContinuousH1.restrictedAction A p
    letI := ContinuousH1.restrictedAction B p
    letI := ContinuousH1.restrictedAction_continuous A p
    letI := ContinuousH1.restrictedAction_continuous B p
    (pointedKernelMap p s hps ψ x).val = (inflatedCoefficientMap p ψ).onH1 x.val := rfl

/-- The equivalence with frozen pointed H1 intertwines its actual coefficient map. -/
theorem pointedH1AddEquiv_naturality (x : PointedKernel (A := A) p s hps) :
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    pointedH1AddEquiv (A := B) p s hps (pointedKernelMap p s hps ψ x) =
      CoefficientFunctoriality.pointedH1Map
        ψ.toContinuousAddMonoidHom.toAddMonoidHom ψ.continuous ψ.map_smul
        (pointedH1AddEquiv (A := A) p s hps x) := by
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  apply Subtype.ext
  exact h1AddEquiv_naturality p s hps ψ x.val

/-- Geometric characters are carried by literal postcomposition with ψ. -/
theorem pointedCharacterEquiv_naturality (x : PointedKernel (A := A) p s hps) :
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    pointedCharacterEquiv (A := B) p s hps (pointedKernelMap p s hps ψ x) =
      CoefficientFunctoriality.characterMap
        ψ.toContinuousAddMonoidHom.toAddMonoidHom ψ.continuous ψ.map_smul
        (pointedCharacterEquiv (A := A) p s hps x) := by
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  change PointedCohomology.pointedH1AddEquiv
    (pointedH1AddEquiv (A := B) p s hps (pointedKernelMap p s hps ψ x)) = _
  rw [pointedH1AddEquiv_naturality]
  exact CoefficientFunctoriality.pointedH1Map_geometric _ _ _ _

/-- The geometric-character square evaluates to the original coefficient function. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem pointedCharacterEquiv_naturality_apply
    (x : PointedKernel (A := A) p s hps) (n : p.toMonoidHom.ker) :
    letI := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
    (pointedCharacterEquiv (A := B) p s hps (pointedKernelMap p s hps ψ x)).toFun n =
      ψ ((pointedCharacterEquiv (A := A) p s hps x).toFun n) := by
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  rw [pointedCharacterEquiv_naturality]
  rfl

/-- Injective coefficients induce an injective pointed map through actual characters. -/
theorem pointedKernelMap_injective (hψ : Function.Injective ψ) :
    Function.Injective (pointedKernelMap p s hps ψ) := by
  let := TopologicalGroup.SplitExtension.kernelAction p.toMonoidHom s.toMonoidHom
  intro x y h
  apply (pointedH1AddEquiv (A := A) p s hps).injective
  apply CoefficientFunctoriality.pointedH1Map_injective
    ψ.toContinuousAddMonoidHom.toAddMonoidHom ψ.continuous ψ.map_smul hψ
  rw [← pointedH1AddEquiv_naturality, ← pointedH1AddEquiv_naturality, h]

end GroupCohomology.SplitCoordinateNaturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6cc1134a10c4c13c1cbb7c5ed00e4e96c2bfff4d2bad06cbbf50757f7720b2c6.
Definitions, hypotheses and universes are retained modulo native names. -/
