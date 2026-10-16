/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.LocalHomotopy
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalLifting
public import Mathlib.Tactic.Abel

/-!
# One local homotopy correction

An actual partial cochain nullhomotopy can be corrected in one more degree
after shrinking an open neighborhood, when that source term is finite locally
free and the target is exact in that degree. The original cochain and homotopy
equations are retained.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalHomotopyStep.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `c8b9d1747230f9415b9c1ad06766bdc61e6282892879088c2ac394fe7d68836f`.
Selected declaration ranges: 49–53, 57–105.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}

private theorem cochain_v_heq (α : Cochain K L (-1)) (p q r : ℤ)
    (h : p + (-1) = q) (h' : p + (-1) = r) : HEq (α.v p q h) (α.v p r h') := by
  subst q
  subst r
  rfl

theorem exists_local_homotopy_step (f : K ⟶ L) (α : Cochain K L (-1)) (n : ℤ)
    (hα : HomotopyAbove f α n) (hL : L.ExactAt n)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X n)] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ β : Cochain ((restrict U.ι).obj K) ((restrict U.ι).obj L) (-1),
        HomotopyAbove ((restrict U.ι).map f) β (n - 1) := by
  let d : K.X n ⟶ L.X n := f.f n -
    α.v n (n - 1) (by omega) ≫ L.d (n - 1) n -
      K.d n (n + 1) ≫ α.v (n + 1) n (by omega)
  have hd : d ≫ L.d n (n + 1) = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, Preadditive.sub_comp]
    simp only [Category.assoc, L.d_comp_d, comp_zero, sub_zero]
    rw [f.comm, hα (n + 1) (by omega), Preadditive.comp_add]
    simp only [← Category.assoc, K.d_comp_d, zero_comp, add_zero]
    apply sub_eq_zero.mpr
    congr 2
    · omega
    · exact congrArg L.X (by omega)
    · exact cochain_v_heq α _ _ _ _ _
    · omega
  have hs : (L.sc' (n - 1) n (n + 1)).Exact :=
    (L.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 hL
  obtain ⟨U, hxU, b, hb⟩ := exists_local_factor_of_exact hs d hd x
  let R := Scheme.Modules.restrictFunctor U.ι
  change R.obj (K.X n) ⟶ R.obj (L.X (n - 1)) at b
  change b ≫ R.map (L.d (n - 1) n) = R.map d at hb
  let β : Cochain ((restrict U.ι).obj K) ((restrict U.ι).obj L) (-1) :=
    α.map R + Cochain.single b (-1)
  refine ⟨U, hxU, β, ?_⟩
  intro p hp
  have hpn : n ≤ p := by omega
  obtain rfl | hnp := hpn.eq_or_lt
  · dsimp only [β]
    rw [Cochain.add_v, Cochain.add_v, Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by
      omega)]
    simp only [Cochain.map_v, add_zero, Preadditive.add_comp]
    change R.map (f.f n) = R.map (α.v n (n - 1) _ ≫ L.d (n - 1) n) +
      b ≫ R.map (L.d (n - 1) n) + R.map (K.d n (n + 1) ≫ α.v (n + 1) n _)
    rw [hb]
    dsimp [d]
    rw [R.map_sub, R.map_sub]
    abel
  · dsimp only [β]
    rw [Cochain.add_v, Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp only [Cochain.map_v, add_zero]
    exact congrArg R.map (hα p hnp)

end AlgebraicGeometry.Scheme.Modules.Complex
