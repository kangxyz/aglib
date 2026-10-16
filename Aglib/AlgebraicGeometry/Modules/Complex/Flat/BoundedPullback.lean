/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure
public import Aglib.Algebra.Homology.CochainComplex.Cycles
public import Aglib.Algebra.Homology.MappingCone.Acyclicity


/-!
# Arbitrary pullback of bounded-above flat complexes

Actual stalkwise-flat cycles are obtained by descending from the upper bound.
Consequently arbitrary geometric pullback preserves acyclic bounded-above
flat complexes and quasi-isomorphisms between such complexes.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatPullback.lean`.
SHA-256: `c33516f3f4e3e10cf8b8d63ef66d116c44544348f1643314099e0d41a8f782c6`.
Selected source lines: 1–107.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual cycles of a bounded-above acyclic complex of stalkwise-flat sheaves are flat. -/
theorem stalkwiseFlat_cycles_of_boundedAbove_acyclic {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ) (hK : ∀ n, stalkwiseFlat X (K.X n))
    (ha : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) (n : ℤ) :
    stalkwiseFlat X (K.cycles n) :=
  CochainComplex.cycles_mem (stalkwiseFlat X) K hK ha b hb n

/-- The bounded-above flat acyclic objects really remain acyclic under arbitrary pullback. -/
theorem acyclic_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex Y.Modules ℤ) (hK : ∀ n, stalkwiseFlat Y (K.X n))
    (ha : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) :
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K).Acyclic := by
  apply CochainComplex.acyclic_map_of_cycle_sequences
  intro n
  exact shortExact_pullback_of_stalkwiseFlat_quotient f
    (CochainComplex.cycleSequence_shortExact K n (ha (n + 1)))
    (stalkwiseFlat_cycles_of_boundedAbove_acyclic K hK ha b hb (n + 1))

/-- Arbitrary geometric pullback preserves quasi-isomorphisms between bounded-above
complexes of genuinely stalkwise-flat module sheaves. -/
theorem quasiIso_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ}
    (hK : ∀ n, stalkwiseFlat Y (K.X n)) (hL : ∀ n, stalkwiseFlat Y (L.X n))
    (b c : ℤ) (hb : ∀ n, b < n → IsZero (K.X n))
    (hc : ∀ n, c < n → IsZero (L.X n)) (s : K ⟶ L) [QuasiIso s] :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map s) := by
  have ht (n : ℤ) : stalkwiseFlat Y ((CochainComplex.mappingCone s).X n) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod s n (n + 1) rfl
    exact (stalkwiseFlat Y).prop_of_iso e.symm (stalkwiseFlat_biprod Y (hK (n + 1)) (hL n))
  have hu (n : ℤ) (hn : max (b - 1) c < n) :
      IsZero ((CochainComplex.mappingCone s).X n) :=
    (CochainComplex.mappingCone.isZero_X_iff s n).mpr ⟨hb (n + 1) (by omega), hc n (by omega)⟩
  have ha := acyclic_pullback_of_boundedAbove_stalkwiseFlat f _ ht
    (CochainComplex.mappingCone_acyclic_of_quasiIso s) (max (b - 1) c) hu
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  intro n
  exact (ha n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso s (Scheme.Modules.pullback f))

end AlgebraicGeometry.Scheme.Modules
