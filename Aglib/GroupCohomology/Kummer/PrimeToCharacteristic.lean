/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous.Hilbert90
public import Aglib.GroupCohomology.Kummer.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Kummer kernels and perfect-field surjectivity

For any field K and positive n nonzero in K, the actual continuous Kummer class vanishes
exactly on nth powers. Descent of a fixed closure element requires its separability.
Separately, over a perfect field every continuous roots-of-unity cocycle has an actual
unit/root representative for every n; surjectivity of the Kummer class map uses positive n. No
perfectness assumption is added to the kernel theorem.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.PrimeToCharacteristic`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a27d4071a4694154092163f92b404b77732af1e2e6dcde9c59d3f92040594ea6`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

/-!
# The actual Kummer map in positive characteristic

For any field, at a positive level nonzero in the field, the existing continuous
`Kummer.kummer` vanishes exactly on nth powers. The chosen root is modified by
a genuine root of unity to make it Galois-fixed. Its separability then lets it
descend through the actual separable-closure intermediate field. The algebraic
closure of an imperfect field is used only as a normal extension; it is never
assumed Galois over the base field.

Over a perfect field the existing Hilbert 90 proof of Kummer surjectivity works
at every positive level. Perfectness supplies the genuine Galois extension to
the algebraic closure. This second result applies in particular to finite
constant fields and does not require invertibility of the level.

These theorems retain the existing coefficient modules, absolute Galois action,
continuous cocycles and Kummer map. They do not construct an integral Tate
symbol or prove a root-symbol kernel theorem.
-/

noncomputable section
namespace GroupCohomology.Kummer
open _root_.GroupCohomology.ContinuousH1
open Field.absoluteGaloisGroup.RootsOfUnity
variable (K : Type*) [Field K]
local notation "Kbar" => AlgebraicClosure K
local notation "G" => Field.absoluteGaloisGroup K

/-- A Galois-fixed separable element of the actual algebraic closure descends.
The algebraic closure itself is only required to be normal, not separable. -/
theorem exists_base_of_fixed_separable (x : Kbar) (hx : IsSeparable K x)
    (hfixed : ∀ g : G, (show Kbar ≃ₐ[K] Kbar from g) x = x) : ∃ a : K, algebraMap K Kbar a = x := by
  let E : IntermediateField K Kbar := separableClosure K Kbar
  let xE : E := ⟨x, hx⟩
  have hE : ∀ g : Gal(E/K), g xE = xE := by
    intro g
    apply (algebraMap E Kbar).injective
    rw [← AlgEquiv.liftNormal_commutes]
    exact hfixed (g.liftNormal Kbar)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed xE).mpr hE
  exact ⟨a, congrArg (algebraMap E Kbar) ha⟩

/-- The existing actual Kummer map has the expected kernel at invertible levels,
including over imperfect fields. -/
theorem kummer_eq_zero_iff (n : ℕ) (hn : 0 < n) [NeZero (n : K)] (f : Kˣ) :
    Kummer.kummer K n hn f = 0 ↔ ∃ a : Kˣ, a ^ n = f := by
  constructor
  · intro hf
    let β := chosenRoot K n hn f
    have hβ : β ^ n = baseUnits K f := chosenRoot_pow K n hn f
    rw [kummer_eq_class K n β hβ hn] at hf
    obtain ⟨z, hz⟩ := (classOf_eq_zero_iff G (Mu K n) (cocycle K n β hβ)).mp hf
    let α : Kbarˣ := β / (z.toMul : Kbarˣ)
    have hα : α ^ n = baseUnits K f := by
      dsimp [α]
      rw [div_pow, hβ, (mem_rootsOfUnity _ _).mp z.toMul.property, div_one]
    have hαfixed : ∀ g : G, (show Kbar ≃ₐ[K] Kbar from g) (α : Kbar) = (α : Kbar) := by
      intro g
      have h := congrArg (fun c : Cocycle G (Mu K n) =>
        ((c.val g).toMul : Kbarˣ)) hz
      change unitAction K g (z.toMul : Kbarˣ) / (z.toMul : Kbarˣ) =
        unitAction K g β / β at h
      have hu : unitAction K g α = α := by
        dsimp [α]
        rw [map_div]
        calc
          unitAction K g β / unitAction K g (z.toMul : Kbarˣ) =
              ((unitAction K g β / β) /
                (unitAction K g (z.toMul : Kbarˣ) / (z.toMul : Kbarˣ))) *
                (β / (z.toMul : Kbarˣ)) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm,
                  mul_assoc]
          _ = β / (z.toMul : Kbarˣ) := by rw [h]; simp
      exact congrArg (fun a : Kbarˣ => (a : Kbar)) hu
    have hαsep : IsSeparable K (α : Kbar) := by
      apply (Polynomial.separable_X_pow_sub_C (n := n) (f : K) (NeZero.ne _) f.ne_zero).of_dvd
      apply minpoly.dvd K (α : Kbar)
      simpa [baseUnits, sub_eq_zero] using congrArg (fun a : Kbarˣ => (a : Kbar)) hα
    obtain ⟨a, ha⟩ := exists_base_of_fixed_separable K (α : Kbar) hαsep hαfixed
    have ha0 : a ≠ 0 := by
      intro hzero
      rw [hzero, map_zero] at ha
      exact α.ne_zero ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    apply (algebraMap K Kbar).injective
    change algebraMap K Kbar (a ^ n) = algebraMap K Kbar (f : K)
    rw [map_pow, ha]
    exact congrArg (fun a : Kbarˣ => (a : Kbar)) hα
  · rintro ⟨a, rfl⟩
    exact Kummer.kummer_nthPower K n hn a

end GroupCohomology.Kummer

namespace GroupCohomology.Kummer

open Field.absoluteGaloisGroup.RootsOfUnity _root_.GroupCohomology.ContinuousH1
open scoped Topology

variable (K : Type*) [Field K] [PerfectField K] (n : ℕ)
local notation "Kbar" => AlgebraicClosure K
local notation "G" => Field.absoluteGaloisGroup K

/-- Every actual continuous roots-of-unity cocycle is the Kummer cocycle of an
actual unit, with equality of representatives rather than only of classes. -/
theorem exists_unit_cocycle_of_perfect (c : Cocycle G (Mu K n)) :
    ∃ (u : Kˣ) (β : Kbarˣ) (hβ : β ^ n = baseUnits K u), cocycle K n β hβ = c := by
  let f : Gal(Kbar/K) → Kbarˣ := fun g => ((c.val g).toMul : Kbarˣ)
  have hf : ∀ g h : Gal(Kbar/K), f (g * h) = g • f h * f g := by
    intro g h
    have hc := congrArg (fun x : Mu K n => (x.toMul : Kbarˣ)) (c.map_mul g h)
    change f (g * h) = f g * (g • f h) at hc
    exact hc.trans (mul_comm _ _)
  have hz : {g : G | c.val g = 0} ∈ nhds (1 : G) :=
    (isOpen_discrete {0}).preimage c.continuous |>.mem_nhds c.map_one
  have hlocal : {g : Gal(Kbar/K) | f g = 1} ∈ nhds (1 : Gal(Kbar/K)) := by
    refine Filter.mem_of_superset hz ?_
    intro g hg
    change ((c.val g).toMul : Kbarˣ) = 1
    rw [hg]
    rfl
  obtain ⟨β, hβ⟩ := GroupCohomology.ContinuousH1.Hilbert90.hilbert90_of_one_fiber_mem_nhds f hf
    hlocal
  have hp : ∀ g : Gal(Kbar/K), g • (β ^ n) = β ^ n := by
    intro g
    have hfn : (f g) ^ n = 1 :=
      (mem_rootsOfUnity _ _).mp (c.val g).toMul.property
    calc
      g • (β ^ n) = (g • β) ^ n := by simp only [AlgEquiv.smul_units_def, map_pow]
      _ = ((g • β / β) * β) ^ n := by rw [div_mul_cancel]
      _ = (f g) ^ n * β ^ n := by rw [hβ, mul_pow]
      _ = β ^ n := by rw [hfn, one_mul]
  have hpfield : ∀ g : Gal(Kbar/K), g ((β ^ n : Kbarˣ) : Kbar) =
      ((β ^ n : Kbarˣ) : Kbar) := by
    intro g
    exact congrArg (fun x : Kbarˣ => (x : Kbar)) (hp g)
  obtain ⟨x, hx⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β ^ n : Kbarˣ) : Kbar)).mpr hpfield
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact (β ^ n).ne_zero hx.symm
  let u : Kˣ := Units.mk0 x hx0
  have hroot : β ^ n = baseUnits K u := by
    apply Units.ext
    exact hx.symm
  refine ⟨u, β, hroot, ?_⟩
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  change unitAction K g β / β = f g
  exact hβ g

/-- Surjectivity of the exact constructed continuous Kummer map. -/
theorem kummer_surjective_of_perfect (hn : 0 < n) : Function.Surjective (kummer K n hn) := by
  intro q
  obtain ⟨c, hc⟩ := classOf_surjective G (Mu K n) q
  obtain ⟨u, β, hβ, hrep⟩ := exists_unit_cocycle_of_perfect K n c
  refine ⟨u, ?_⟩
  rw [kummer_eq_class K n β hβ hn, hrep]
  exact hc

end GroupCohomology.Kummer
