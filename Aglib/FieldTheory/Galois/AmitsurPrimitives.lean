/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.AmitsurCofaces
public import Aglib.FieldTheory.Brauer.FunctionFieldCocycles
public import Mathlib.Algebra.Group.Pi.Units

/-! # Actual Amitsur unit primitives over algebraic function fields

The units are those of the original conerve rings and every map is the original
coface. Native multiplicative Galois cocycle primitives are transported back by
the actual algebra equivalence, preserving the unit and hence nonzero condition.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Simplicial

namespace Algebra.Amitsur

universe u

variable (E L : Type u) [Field E] [Field L] [Algebra E L]
  [FiniteDimensional E L] [IsGalois E L]

/-- The literal map on units induced by an original Amitsur coface. -/
def unitCoface (n : ℕ) (j : Fin (n + 2)) : (term E L n)ˣ →* (term E L (n + 1))ˣ :=
  Units.map ((conerve E L).δ j).hom.toMonoidHom

/-- The original unit coface 0 in degree 1, in actual Galois coordinates. -/
@[simp]
theorem unit_twoEvaluation_δ_0 (b : (term E L 1)ˣ) (σ τ : Gal(L/E)) :
    Units.map ((twoEvaluation E L σ τ).hom : term E L 2 →* L)
      (unitCoface E L 1 0 b) =
        σ • Units.map (oneEvaluation E L τ).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 1 ⟶ CommAlgCat.of E L => f.hom (b : term E L 1))
    (δ_0_twoEvaluation E L σ τ)

/-- The original unit coface 1 in degree 1, in actual Galois coordinates. -/
@[simp]
theorem unit_twoEvaluation_δ_1 (b : (term E L 1)ˣ) (σ τ : Gal(L/E)) :
    Units.map ((twoEvaluation E L σ τ).hom : term E L 2 →* L)
      (unitCoface E L 1 1 b) =
        Units.map (oneEvaluation E L (σ * τ)).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 1 ⟶ CommAlgCat.of E L => f.hom (b : term E L 1))
    (δ_1_twoEvaluation E L σ τ)

/-- The original unit coface 2 in degree 1, in actual Galois coordinates. -/
@[simp]
theorem unit_twoEvaluation_δ_2 (b : (term E L 1)ˣ) (σ τ : Gal(L/E)) :
    Units.map ((twoEvaluation E L σ τ).hom : term E L 2 →* L)
      (unitCoface E L 1 2 b) =
        Units.map (oneEvaluation E L σ).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 1 ⟶ CommAlgCat.of E L => f.hom (b : term E L 1))
    (δ_2_twoEvaluation E L σ τ)

/-- The original unit coface 0 in degree 2, in actual Galois coordinates. -/
@[simp]
theorem unit_threeEvaluation_δ_0 (b : (term E L 2)ˣ) (σ τ υ : Gal(L/E)) :
    Units.map ((threeEvaluation E L σ τ υ).hom : term E L 3 →* L)
      (unitCoface E L 2 0 b) =
        σ • Units.map (twoEvaluation E L τ υ).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 2 ⟶ CommAlgCat.of E L => f.hom (b : term E L 2))
    (δ_0_threeEvaluation E L σ τ υ)

/-- The original unit coface 1 in degree 2, in actual Galois coordinates. -/
@[simp]
theorem unit_threeEvaluation_δ_1 (b : (term E L 2)ˣ) (σ τ υ : Gal(L/E)) :
    Units.map ((threeEvaluation E L σ τ υ).hom : term E L 3 →* L)
      (unitCoface E L 2 1 b) =
        Units.map (twoEvaluation E L (σ * τ) υ).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 2 ⟶ CommAlgCat.of E L => f.hom (b : term E L 2))
    (δ_1_threeEvaluation E L σ τ υ)

/-- The original unit coface 2 in degree 2, in actual Galois coordinates. -/
@[simp]
theorem unit_threeEvaluation_δ_2 (b : (term E L 2)ˣ) (σ τ υ : Gal(L/E)) :
    Units.map ((threeEvaluation E L σ τ υ).hom : term E L 3 →* L)
      (unitCoface E L 2 2 b) =
        Units.map (twoEvaluation E L σ (τ * υ)).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 2 ⟶ CommAlgCat.of E L => f.hom (b : term E L 2))
    (δ_2_threeEvaluation E L σ τ υ)

/-- The original unit coface 3 in degree 2, in actual Galois coordinates. -/
@[simp]
theorem unit_threeEvaluation_δ_3 (b : (term E L 2)ˣ) (σ τ υ : Gal(L/E)) :
    Units.map ((threeEvaluation E L σ τ υ).hom : term E L 3 →* L)
      (unitCoface E L 2 3 b) =
        Units.map (twoEvaluation E L σ τ).hom.toMonoidHom b := by
  apply Units.ext
  exact congrArg (fun f : term E L 2 ⟶ CommAlgCat.of E L => f.hom (b : term E L 2))
    (δ_3_threeEvaluation E L σ τ υ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every actual degree-two Amitsur unit cocycle has an actual degree-one
primitive over an algebraic extension of an algebraically closed rational-function field. -/
theorem exists_unit_primitive_of_algebraic_ratFunc
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra (RatFunc K) E]
    [Algebra.IsAlgebraic (RatFunc K) E]
    (c : (term E L 2)ˣ)
    (hc : unitCoface E L 2 0 c / unitCoface E L 2 1 c *
      unitCoface E L 2 2 c / unitCoface E L 2 3 c = 1) :
    ∃ b : (term E L 1)ˣ,
      unitCoface E L 1 0 b / unitCoface E L 1 1 b * unitCoface E L 1 2 b = c := by
  let a : Gal(L/E) × Gal(L/E) → Lˣ :=
    fun p => Units.map (twoEvaluation E L p.1 p.2).hom.toMonoidHom c
  have ha : groupCohomology.IsMulCocycle₂ a := by
    intro σ τ υ
    have h := congrArg (Units.map (threeEvaluation E L σ τ υ).hom.toMonoidHom) hc
    simp only [map_div, map_mul, map_one, AlgHom.toRingHom_eq_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom] at h
    rw [unit_threeEvaluation_δ_0 E L c σ τ υ, unit_threeEvaluation_δ_1 E L c σ τ υ,
      unit_threeEvaluation_δ_2 E L c σ τ υ, unit_threeEvaluation_δ_3 E L c σ τ υ] at h
    simp only [div_mul_eq_mul_div, div_div, div_eq_one] at h
    exact h.symm
  obtain ⟨b, hb⟩ := ha.isMulCoboundary₂_of_algebraic_ratFunc K E L
  let q : (term E L 1)ˣ ≃* (Gal(L/E) → Lˣ) :=
    (Units.mapEquiv (oneGaloisEquiv E L).toMulEquiv).trans MulEquiv.piUnits
  refine ⟨q.symm b, ?_⟩
  apply Units.ext
  apply (twoGaloisEquiv E L).injective
  funext τ σ
  have hq (ρ : Gal(L/E)) :
      Units.map (oneEvaluation E L ρ).hom.toMonoidHom (q.symm b) = b ρ := by
    apply Units.ext
    exact congrArg Units.val (congrFun (q.apply_symm_apply b) ρ)
  have h := hb σ τ
  rw [← hq τ, ← hq (σ * τ), ← hq σ] at h
  have h' : Units.map (twoEvaluation E L σ τ).hom.toMonoidHom
      (unitCoface E L 1 0 (q.symm b) / unitCoface E L 1 1 (q.symm b) *
        unitCoface E L 1 2 (q.symm b)) =
      Units.map (twoEvaluation E L σ τ).hom.toMonoidHom c := by
    simp only [map_div, map_mul, AlgHom.toRingHom_eq_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom]
    rw [unit_twoEvaluation_δ_0 E L (q.symm b) σ τ,
      unit_twoEvaluation_δ_1 E L (q.symm b) σ τ,
      unit_twoEvaluation_δ_2 E L (q.symm b) σ τ]
    exact h
  exact congrArg Units.val h'

end Algebra.Amitsur
