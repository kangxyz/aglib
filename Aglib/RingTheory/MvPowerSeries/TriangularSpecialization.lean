/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.Triangular
public import Aglib.RingTheory.MvPowerSeries.KillComplSubstitution

/-!
# Restricting triangular coordinates to the pivot axis

The restriction of a triangularly transformed series to its pivot axis is
exactly its weighted specialization when the pivot has weight one. This
identity concerns all formal series, not just polynomials.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} [CommRing R]

/-- The embedding whose coordinate subspace is the axis of `p`. -/
def axisEmbedding (p : σ) : Unit ↪ σ :=
  ⟨fun _ ↦ p, fun a b _ ↦ Subsingleton.elim a b⟩

variable [Finite σ] [DecidableEq σ]

/-- Triangular coordinate change followed by restriction to its pivot axis
is the actual weighted formal substitution. -/
theorem killCompl_axis_triangularAlgEquiv (p : σ) (w : σ → ℕ)
    (hw : ∀ i, i ≠ p → 0 < w i) (hp : w p = 1)
    (f : MvPowerSeries σ R) :
    killCompl (axisEmbedding p) (triangularAlgEquiv p w hw f) =
      subst (fun i ↦ (X () : MvPowerSeries Unit R) ^ w i) f := by
  change killCompl (axisEmbedding p)
    (substAlgHom (hasSubst_triangularCoordinates p w hw) f) = _
  rw [coe_substAlgHom, killCompl_subst (axisEmbedding p)
    (hasSubst_triangularCoordinates p w hw)]
  have hcoord : (fun i ↦ killCompl (axisEmbedding p)
      (triangularCoordinates (R := R) p w i)) =
      (fun i ↦ (X () : MvPowerSeries Unit R) ^ w i) := by
    have hpX : killCompl (axisEmbedding p) (X p : MvPowerSeries σ R) = X () :=
      killCompl_X (e := axisEmbedding p) ()
    funext i
    by_cases hi : i = p
    · subst i
      simp only [triangularCoordinates, ite_true, hpX, hp, pow_one]
    · have hiX : killCompl (axisEmbedding p) (X i : MvPowerSeries σ R) = 0 := by
        apply killCompl_X_eq_zero
        rintro ⟨u, hu⟩
        exact hi hu.symm
      simp only [triangularCoordinates, hi, ite_false, map_add, map_pow, hiX,
        hpX, zero_add]
  rw [hcoord]

end MvPowerSeries
