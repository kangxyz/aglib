/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

/-
The finite Hilbert 90 argument is adapted from Mathlib's Hilbert90.lean:
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib LICENSE.
Authors of that argument: Riccardo Brasca, Amelia Livingston.
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Hilbert 90 through finite normal descent

Finite Hilbert 90 is proved for the actual automorphism group of a finite-dimensional field
extension, without assuming the extension Galois. For a Galois extension, infinite descent uses
a finite normal intermediate field whose fixing subgroup kills the cocycle. The neighborhood
version constructs such a field from the identity fiber in the actual Krull topology.

Extraction source: `R5Lab.Aglib.GroupCohomology.H1.ContinuousHilbert90`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`94ee62158132fce0325bf750e09c8dc57d90520574820cee72138006258a5e36`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

/-!
Continuous Hilbert 90 via an explicit finite normal descent.
The finite sum argument proves the finite case directly by linear independence
of field automorphisms. A locally trivial cocycle then descends to a finite
normal intermediate field, giving the result for a Galois extension.
-/

noncomputable section
set_option autoImplicit false

namespace GroupCohomology.ContinuousH1.Hilbert90

open scoped Topology

section Finite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

private def finiteAux (f : Gal(L/K) → Lˣ) : L → L :=
  Finsupp.linearCombination L (fun φ : Gal(L/K) => (φ : L → L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

private theorem finiteAux_ne_zero (f : Gal(L/K) → Lˣ) : finiteAux f ≠ 0 := by
  have hli : LinearIndependent L (fun (φ : Gal(L/K)) => (φ : L → L)) :=
    LinearIndependent.comp (ι' := Gal(L/K))
      (linearIndependent_monoidHom L L) (fun φ => φ)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 hli
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  exact fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

/-- Finite Hilbert 90, with the exact orientation `g(β)/β = f(g)`. -/
theorem finite_hilbert90 (f : Gal(L/K) → Lˣ)
    (hf : ∀ g h, f (g * h) = g • f h * f g) :
    ∃ β : Lˣ, ∀ g : Gal(L/K), g • β / β = f g := by
  obtain ⟨z, hz⟩ : ∃ z, finiteAux f z ≠ 0 :=
    not_forall.1 (fun H => finiteAux_ne_zero f <| funext <| fun x => H x)
  have hsum : finiteAux f z = ∑ h, f h * h z := by
    simp [finiteAux, Finsupp.linearCombination, Finsupp.sum_fintype]
  refine ⟨(Units.mk0 (finiteAux f z) hz)⁻¹, ?_⟩
  intro g
  simp only [AlgEquiv.smul_units_def, map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul,
    Units.ext_iff, hsum, Units.val_mul, Units.coe_map, Units.val_mk0,
    MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L),
    ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end Finite

section Descent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- A locally trivial units cocycle descends to any finite normal field whose
fixing subgroup kills it; its values lie in that field by the cocycle identity. -/
theorem hilbert90_of_vanishing_fixingSubgroup (E : IntermediateField K L)
    [FiniteDimensional K E] [Normal K E] (f : Gal(L/K) → Lˣ)
    (hf : ∀ g h, f (g * h) = g • f h * f g)
    (hvanish : ∀ h ∈ E.fixingSubgroup, f h = 1) :
    ∃ β : Lˣ, ∀ g : Gal(L/K), g • β / β = f g := by
  let r : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective L
  have hsame : ∀ g h : Gal(L/K), r g = r h → f g = f h := by
    intro g h heq
    have hk : h⁻¹ * g ∈ E.fixingSubgroup := by
      rw [← E.restrictNormalHom_ker]
      change r (h⁻¹ * g) = 1
      simp only [map_mul, map_inv, heq, inv_mul_cancel]
    have hc := hf h (h⁻¹ * g)
    simpa only [mul_inv_cancel_left, hvanish _ hk, smul_one, one_mul] using hc
  have hmem : ∀ g : Gal(L/K), (f g : L) ∈ E := by
    intro g
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro h hh
    have hrh : r h = 1 := by
      change h ∈ (AlgEquiv.restrictNormalHom E).ker
      rwa [E.restrictNormalHom_ker]
    have hfg : f (h * g) = f g := hsame _ _ (by simp [hrh])
    have hfix : h • f g = f g := by
      rw [hf, hvanish h hh, mul_one] at hfg
      exact hfg
    exact congrArg (fun x : Lˣ => (x : L)) hfix
  let lift : Gal(E/K) → Gal(L/K) := fun g => (hr g).choose
  have hlift : ∀ g : Gal(E/K), r (lift g) = g := fun g => (hr g).choose_spec
  let inc : Eˣ →* Lˣ := Units.map (algebraMap E L).toMonoidHom
  have hinc_inj : Function.Injective inc := Units.map_injective (algebraMap E L).injective
  let fE : Gal(E/K) → Eˣ := fun g =>
    Units.mk0 ⟨(f (lift g) : L), hmem (lift g)⟩ (by
      intro hzero
      exact (f (lift g)).ne_zero (congrArg Subtype.val hzero))
  have hinc : ∀ g : Gal(E/K), inc (fE g) = f (lift g) := by
    intro g
    apply Units.ext
    rfl
  have hinc_smul : ∀ (g : Gal(L/K)) (x : Eˣ), inc (r g • x) = g • inc x := by
    intro g x
    apply Units.ext
    exact AlgEquiv.restrictNormalHom_apply E g (x : E)
  have hfE : ∀ g h : Gal(E/K), fE (g * h) = g • fE h * fE g := by
    intro g h
    apply hinc_inj
    calc
      inc (fE (g * h)) = f (lift (g * h)) := hinc _
      _ = f (lift g * lift h) := hsame _ _ (by simp only [hlift, map_mul])
      _ = lift g • f (lift h) * f (lift g) := hf _ _
      _ = inc (g • fE h) * inc (fE g) := by
        have hs := hinc_smul (lift g) (fE h)
        rw [hlift, hinc] at hs
        rw [hs, hinc]
      _ = inc (g • fE h * fE g) := (map_mul inc _ _).symm
  obtain ⟨β, hβ⟩ := finite_hilbert90 fE hfE
  refine ⟨inc β, ?_⟩
  intro g
  calc
    g • inc β / inc β = inc (r g • β / β) := by rw [map_div, hinc_smul]
    _ = inc (fE (r g)) := congrArg inc (hβ (r g))
    _ = f (lift (r g)) := hinc _
    _ = f g := hsame _ _ (hlift _)

/-- Hilbert 90 for a units cocycle whose identity fiber is a Krull neighborhood.
Continuity into discrete units supplies this hypothesis, and the proof constructs
the finite normal descent rather than taking it as an input. -/
theorem hilbert90_of_one_fiber_mem_nhds (f : Gal(L/K) → Lˣ)
    (hf : ∀ g h, f (g * h) = g • f h * f g)
    (hlocal : {g | f g = 1} ∈ nhds (1 : Gal(L/K))) :
    ∃ β : Lˣ, ∀ g : Gal(L/K), g • β / β = f g := by
  obtain ⟨E, hfin, hnormal, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L _).mp hlocal
  have : FiniteDimensional K E := hfin
  have : Normal K E := hnormal
  exact hilbert90_of_vanishing_fixingSubgroup E f hf (fun g hg => hE hg)

end Descent

end GroupCohomology.ContinuousH1.Hilbert90
