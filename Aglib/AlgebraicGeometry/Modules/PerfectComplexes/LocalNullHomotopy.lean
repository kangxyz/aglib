/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalHomotopyStep
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction

/-!
# Local nullhomotopies from strict perfect complexes

Finite descending corrections produce an actual chain nullhomotopy on a
pointed open immersion. The explicit lower term bound, termwise finite local
freeness and target acyclicity are retained by the approximation theorem.
The strict-perfect corollary has no bound or perfectness premise on the target.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalNullHomotopy.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `cc23fba72767c558490cb186c433ddfc9cffd0858baca40544082563b33b8067`.
Selected declaration ranges: 78–112, 117–127.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomComplex
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

theorem exists_local_nullHomotopy_from_approx (N : ℕ)
    {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (a : ℤ) (f : K ⟶ L) (α : Cochain K L (-1))
    (hα : HomotopyAbove f α (a + N - 1))
    (hb : ∀ p : ℤ, p < a → IsZero (K.X p))
    (hv : ∀ p : ℤ, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X p))
    (hL : L.Acyclic) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      Nonempty (Homotopy ((@restrict Y X j hj).map f) 0) := by
  induction N generalizing X K L with
  | zero =>
      have ha : HomotopyAbove f α (a - 1) := by simpa using hα
      let h := nullHomotopyOfAbove f α a ha hb
      refine ⟨X, 𝟙 X, inferInstance, x, by simp, ?_⟩
      exact ⟨((Scheme.Modules.restrictFunctor (𝟙 X)).mapHomotopy h).trans
        (Homotopy.ofEq (by simp))⟩
  | succ N ih =>
      have ha : HomotopyAbove f α (a + N) := by
        convert hα using 1
        omega
      let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X (a + N)) := hv _
      obtain ⟨O, hxO, β, hβ⟩ := exists_local_homotopy_step f α (a + N) ha (hL _) x
      have hb' (p : ℤ) (hp : p < a) : IsZero (((restrict O.ι).obj K).X p) :=
        (Scheme.Modules.restrictFunctor O.ι).map_isZero (hb p hp)
      have hv' (p : ℤ) : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree O.toScheme (((restrict
        O.ι).obj K).X p) :=
        @AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_restrict O.toScheme X O.ι inferInstance
          (K.X p) (hv p)
      obtain ⟨Y, j, hj, y, hy, ⟨h⟩⟩ := ih ((restrict O.ι).map f) β hβ hb' hv'
        (acyclic_restrict O.ι hL) ⟨x, hxO⟩
      let := hj
      refine ⟨Y, j ≫ O.ι, inferInstance, y, ?_, ?_⟩
      · change O.ι (j y) = x
        rw [hy]
        rfl
      · exact ⟨nullHomotopyOfNatIso (restrictCompIso j O.ι) h⟩

theorem exists_local_nullHomotopy {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : strictPerfect X K) (f : K ⟶ L) (hL : L.Acyclic) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      Nonempty (Homotopy ((@restrict Y X j hj).map f) 0) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  let N : ℕ := (b - a + 1).toNat
  have hα : HomotopyAbove f 0 (a + N - 1) := by
    intro p hp
    exact (hb p (Or.inr (by dsimp [N] at hp; omega))).eq_of_src _ _
  exact exists_local_nullHomotopy_from_approx N a f 0 hα
    (fun p hp ↦ hb p (Or.inl hp)) hv hL x

end AlgebraicGeometry.Scheme.Modules.Complex
