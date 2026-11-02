/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Constructible.GenericAvoidance
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Fiber

/-! # Generic surjectivity and finite-base open shrinking

Chevalley's existing image theorem is applied to the actual complement of
the finite union of the original proper branch images. This constructs the
base open on which that same family jointly covers the original target. A separate finite
closed-image construction
pushes an open containing the entire generic fibre down to the original base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Set

namespace AlgebraicGeometry.Scheme

universe u

/-- Joint coverage of the original generic fibre by a finite proper family
spreads to an actual base open. The closed union and its bad image are
constructed from these same maps; no individual branch is assumed surjective. -/
theorem exists_generic_open_jointly_surjective_proper_family
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    [LocallyOfFinitePresentation p] {I : Type u} [Finite I]
    {C : I → Scheme.{u}} (ν : ∀ i, C i ⟶ X) [∀ i, IsProper (ν i)]
    (hgeneric : ∀ x : X, p x = genericPoint (Spec (.of R)) →
      ∃ i, ∃ c : C i, ν i c = x) :
    ∃ U : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ U ∧
        ∀ x : X, p x ∈ U → ∃ i, ∃ c : C i, ν i c = x := by
  classical
  let S := Spec (.of R)
  let η : S := genericPoint S
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let bad : Set X := (⋃ i, Set.range (ν i))ᶜ
  have hbadopen : IsOpen bad :=
    (isClosed_iUnion_of_finite (fun i => (ν i).isClosedMap.isClosed_range)).isOpen_compl
  have hbad : IsConstructible bad :=
    (NoetherianSpace.isCompact bad).isConstructible hbadopen
  have himage : IsConstructible (p '' bad) := p.isConstructible_image hbad
  have hη : η ∉ p '' bad := by
    rintro ⟨x, hx, hpx⟩
    obtain ⟨i, c, hc⟩ := hgeneric x hpx
    exact hx (Set.mem_iUnion.mpr ⟨i, ⟨c, hc⟩⟩)
  obtain ⟨U, hU, hηU, hdisj⟩ :=
    (genericPoint_spec S).exists_open_disjoint_of_isConstructible himage hη
  refine ⟨⟨U, hU⟩, hηU, ?_⟩
  intro x hx
  have hxrange : x ∈ ⋃ i, Set.range (ν i) := by
    by_contra hbadx
    exact Set.disjoint_left.mp hdisj hx ⟨x, hbadx, rfl⟩
  obtain ⟨i, c, hc⟩ := Set.mem_iUnion.mp hxrange
  exact ⟨i, c, hc⟩

/-- Surjectivity over the actual generic residue-field fibre supplies an
actual generic neighbourhood on which the original finite cover is surjective.
This is the singleton instance of joint proper-image spreading. -/
theorem exists_generic_open_surjective_finite_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {C X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    [LocallyOfFinitePresentation p] (ν : C ⟶ X) [IsFinite ν]
    [Surjective (pullback.snd ν (p.fiberι (genericPoint (Spec (.of R)))))] :
    ∃ U : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ U ∧
        Surjective (pullback.snd ν (p ⁻¹ᵁ U).ι) := by
  let S := Spec (.of R)
  let η : S := genericPoint S
  have hgeneric (x : X) (hpx : p x = η) :
      ∃ i : PUnit.{u + 1}, ∃ c : C, ν c = x := by
    let z : Spec (S.residueField η) := Nonempty.some inferInstance
    have hpoint : p.base x = (S.fromSpecResidueField η).base z := by
      simpa only [Scheme.fromSpecResidueField_apply] using hpx
    obtain ⟨xη, hfst, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := p)
        (g := S.fromSpecResidueField η) x z hpoint
    obtain ⟨w, hw⟩ := (pullback.snd ν (p.fiberι η)).surjective xη
    refine ⟨PUnit.unit, pullback.fst ν (p.fiberι η) w, ?_⟩
    calc
      ν (pullback.fst ν (p.fiberι η) w) =
          p.fiberι η (pullback.snd ν (p.fiberι η) w) :=
        congrArg (fun f : pullback ν (p.fiberι η) ⟶ X => f w)
          (pullback.condition (f := ν) (g := p.fiberι η))
      _ = x := by rw [hw]; exact hfst
  obtain ⟨U, hηU, hU⟩ := exists_generic_open_jointly_surjective_proper_family R p
    (fun _ : PUnit.{u + 1} => ν) hgeneric
  refine ⟨U, hηU, ⟨fun x => ?_⟩⟩
  obtain ⟨_, c, hc⟩ := hU ((p ⁻¹ᵁ U).ι x) x.property
  obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := ν) (g := (p ⁻¹ᵁ U).ι) c x hc
  exact ⟨w, hw⟩

/-- For the original finite base map, an open containing the whole generic
fibre contains the inverse image of an actual generic base neighbourhood.
Surjectivity of the finite base map is not needed for this stronger statement. -/
theorem exists_generic_open_preimage_subset_of_isFinite
    (R : Type u) [CommRing R] [IsDomain R]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of R)) [IsFinite b] (V : B.Opens)
    (hV : ∀ z : B, b z = genericPoint (Spec (.of R)) → z ∈ V) :
    ∃ U : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ U ∧ b ⁻¹ᵁ U ≤ V := by
  let U : (Spec (.of R)).Opens :=
    ⟨(b '' (V : Set B)ᶜ)ᶜ,
      (b.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨z, hz, hzb⟩
    exact hz (hV z hzb)
  · intro z hz
    by_contra hzV
    exact hz ⟨z, hzV, rfl⟩

/-- For a finite dominant map of integral schemes, a source generic
neighbourhood contains the entire inverse image of an actual generic base
neighbourhood. The whole generic fibre condition is constructed from the
original function-field fibre isomorphism. -/
theorem exists_generic_open_preimage_subset_of_isFinite_of_genericPoint_mem
    (R : Type u) [CommRing R] [IsDomain R]
    {B : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Spec (.of R)) [IsFinite b] [IsDominant b]
    (V : B.Opens) (hV : genericPoint B ∈ V) :
    ∃ U : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ U ∧ b ⁻¹ᵁ U ≤ V := by
  apply exists_generic_open_preimage_subset_of_isFinite R b V
  intro z hz
  let S := Spec (.of R)
  let g := S.fromSpecStalk (genericPoint S)
  let w : Spec S.functionField := Nonempty.some inferInstance
  have hpoint : b.base z = g.base w := by
    simpa only [g, fromSpecStalk_genericPoint_apply] using hz
  obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := b) (g := g) z w hpoint
  let : IsIso (genericFibreMap b) := genericFibreMap_isIso b
  obtain ⟨t, ht⟩ := (genericFibreMap b).surjective v
  have hzgen : z = genericPoint B := by
    calc
      z = pullback.fst b g v := hv.symm
      _ = pullback.fst b g (genericFibreMap b t) := by rw [ht]
      _ = (B.fromSpecStalk (genericPoint B)) t := by
        exact congrArg (fun f : Spec B.functionField ⟶ B => f t)
          (pullback.lift_fst _ _ _)
      _ = genericPoint B := fromSpecStalk_genericPoint_apply B t
  simpa only [hzgen] using hV

end AlgebraicGeometry.Scheme
