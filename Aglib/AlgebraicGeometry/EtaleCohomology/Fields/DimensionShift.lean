/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.CoinductionCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.EtaleUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCokernelGeneral
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PullbackEffacement
public import Aglib.CategoryTheory.Abelian.Ext.ClasswiseDimensionShift

/-! # Classwise dimension shifting for original finite field coefficients

Finite Galois effacement kills an original class after pullback. Exact
coinduction identifies that pullback with the map of the literal coefficient
unit. This unit is monic, and its literal cokernel is finite locally constant
with the same annihilator. The original Ext exact sequence therefore shifts
the class down one degree. Only degree-two vanishing over the original field
is needed; no higher vanishing or cohomology on finite extensions is assumed.

The geometric exactness and finite-local-constancy of finite coinduction are
explicit hypotheses in this leaf, separate from the cohomological hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

attribute [local instance] hasSheafifyLarge

variable (K : Type u) [Field K]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
  [∀ L : FiniteGaloisIntermediateField K (SeparableClosure K),
    PreservesFiniteColimits (directImage (Spec.algebraMap K L))]

/-- Classwise finite coinduction reduces every original degree at least two
to degree two for finite locally constant coefficients with a fixed annihilator.
The only cohomological input is the displayed same-field degree-two vanishing. -/
theorem cohomology_eq_zero_of_h2_of_exact_finiteCoinduction
    (hfinite : ∀ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (F : AbelianSheaf.{u, u + 1} (Spec (.of K))), IsFiniteLocallyConstant F →
      IsFiniteLocallyConstant
        ((directImage (Spec.algebraMap K L)).obj ((inverseImage (Spec.algebraMap K L)).obj F)))
    (p : ℕ)
    (h2 : ∀ (F : AbelianSheaf.{u, u + 1} (Spec (.of K))),
      IsFiniteLocallyConstant F → KilledBy p F → Subsingleton (Sheaf.H.{w} F 2))
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))
    (hF : IsFiniteLocallyConstant F) (hp : KilledBy p F)
    (n : ℕ) (α : Sheaf.H.{w} F (n + 2)) : α = 0 := by
  refine Ext.eq_zero_of_classwise_effaceable _
    (fun G => IsFiniteLocallyConstant G ∧ KilledBy p G) ?_ ?_ ⟨hF, hp⟩ n α
  · intro G hG
    exact h2 G hG.1 hG.2
  · intro F hFp n α
    rcases hFp with ⟨hF, hp⟩
    let : ∀ L : FiniteGaloisIntermediateField K (SeparableClosure K),
        HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Spec (.of L))) :=
      fun L => hasExtStandard (Spec (.of L))
    obtain ⟨L, hL⟩ := exists_finiteGalois_cohomologyPullback_eq_zero.{u, w, u + 2}
      K F (n + 2) α
    let f := Spec.algebraMap K L
    let : Etale f := (finiteFieldCover K L).property.2
    let : Surjective f := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    let C := (directImage f).obj ((inverseImage f).obj F)
    let i : F ⟶ C := (inverseImageAdjunction f).unit.app F
    have hi : Sheaf.H.map i (n + 2 + 1) α = 0 :=
      unit_cohomologyMap_eq_zero_of_pullback_eq_zero.{u, w, u + 2} f F (n + 2 + 1) α hL
    have hQ : IsFiniteLocallyConstant (cokernel i) :=
      isFiniteLocallyConstant_cokernel K F C hF (hfinite L F hF) i
    have hpQ : KilledBy p (cokernel i) :=
      killedBy_cokernel i p (killedBy_directImage_inverseImage f F hp)
    exact ⟨C, i, inferInstance, ⟨hQ, hpQ⟩, hi⟩

/-- The original all-degree conclusion, retaining the arbitrary source Ext
universe and the original finite locally constant coefficient. -/
theorem subsingleton_cohomology_of_h2_of_exact_finiteCoinduction
    (hfinite : ∀ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (F : AbelianSheaf.{u, u + 1} (Spec (.of K))), IsFiniteLocallyConstant F →
      IsFiniteLocallyConstant
        ((directImage (Spec.algebraMap K L)).obj ((inverseImage (Spec.algebraMap K L)).obj F)))
    (p : ℕ)
    (h2 : ∀ (F : AbelianSheaf.{u, u + 1} (Spec (.of K))),
      IsFiniteLocallyConstant F → KilledBy p F → Subsingleton (Sheaf.H.{w} F 2))
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))
    (hF : IsFiniteLocallyConstant F) (hp : KilledBy p F)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} F q) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hq
  rw [Nat.add_comm] at hn
  subst q
  exact ⟨fun α β =>
    (cohomology_eq_zero_of_h2_of_exact_finiteCoinduction K hfinite p h2 F hF hp n α).trans
      (cohomology_eq_zero_of_h2_of_exact_finiteCoinduction K hfinite p h2 F hF hp n β).symm⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
