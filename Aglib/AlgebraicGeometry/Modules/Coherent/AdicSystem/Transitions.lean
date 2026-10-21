/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # Canonical all-order reduction of coherent adic systems -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} {K : X.IdealSheafData} [IsLocallyNoetherian X]
variable (F : AdicSystem X K)

/-- Adjacent canonical reduction implies canonical reduction between any two
levels, with the original inverse-diagram map. -/
theorem exists_reductionIso_of_le {n m : ℕ} (h : n ≤ m) :
    ∃ e : (idealSheafQuotientFunctor X (K ^ n)).obj (F.obj.obj (op m)) ≅ F.obj.obj (op n),
      (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op m)) ≫ e.hom =
        F.obj.map (homOfLE h).op := by
  induction m, h using Nat.le_induction with
  | base =>
    let e := closedImmersionDescentIso (K ^ n).subschemeι (F.obj.obj (op n))
      (by simpa only [IdealSheafData.ker_subschemeι] using F.property.annihilated n)
    refine ⟨e, ?_⟩
    change e.inv ≫ e.hom = _
    rw [e.inv_hom_id]
    exact (F.obj.map_id (op n)).symm
  | succ m h ih =>
    obtain ⟨e, he⟩ := ih
    let d := idealSheafQuotientReductionIso X (K ^ m) (idealSheaf_pow_le X K h)
      (F.obj.obj (op (m + 1)))
    let s := F.reductionIso m
    refine ⟨d.symm ≪≫ (idealSheafQuotientFunctor X (K ^ n)).mapIso s ≪≫ e, ?_⟩
    have hd : (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op (m + 1))) ≫ d.inv =
        (idealSheafQuotientUnit X (K ^ m)).app (F.obj.obj (op (m + 1))) ≫
          (idealSheafQuotientUnit X (K ^ n)).app
            ((idealSheafQuotientFunctor X (K ^ m)).obj (F.obj.obj (op (m + 1)))) := by
      apply (cancel_mono d.hom).mp
      simp only [Category.assoc, d.inv_hom_id, Category.comp_id]
      change _ = _ ≫ _ ≫ (idealSheafQuotientReductionIso X (K ^ m)
        (idealSheaf_pow_le X K h) (F.obj.obj (op (m + 1)))).hom
      have hred :
          (idealSheafQuotientUnit X (K ^ n)).app
              ((idealSheafQuotientFunctor X (K ^ m)).obj (F.obj.obj (op (m + 1)))) ≫
            (idealSheafQuotientReductionIso X (K ^ m) (idealSheaf_pow_le X K h)
              (F.obj.obj (op (m + 1)))).hom =
          idealSheafQuotientMap X (K ^ m) (idealSheaf_pow_le X K h)
            (F.obj.obj (op (m + 1))) :=
        idealSheafQuotientUnit_reductionIso_hom X (K ^ m) (idealSheaf_pow_le X K h)
          (F.obj.obj (op (m + 1)))
      rw [hred, idealSheafQuotientUnit_map]
    change (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op (m + 1))) ≫
      d.inv ≫ (idealSheafQuotientFunctor X (K ^ n)).map s.hom ≫ e.hom = _
    have hs : (idealSheafQuotientUnit X (K ^ n)).app
        ((idealSheafQuotientFunctor X (K ^ m)).obj (F.obj.obj (op (m + 1)))) ≫
        (idealSheafQuotientFunctor X (K ^ n)).map s.hom =
        s.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op m)) := by
      simpa only [Functor.id_map] using
        ((idealSheafQuotientUnit X (K ^ n)).naturality s.hom).symm
    rw [← Category.assoc, hd]
    have hs' := congrArg (fun t =>
      (idealSheafQuotientUnit X (K ^ m)).app (F.obj.obj (op (m + 1))) ≫ t ≫ e.hom) hs
    simp only [Category.assoc] at hs'
    rw [Category.assoc, hs', he, ← Category.assoc, F.unit_reductionIso_hom m]
    change F.obj.map (homOfLE (Nat.le_succ m)).op ≫ F.obj.map (homOfLE h).op = _
    rw [← F.obj.map_comp]
    congr 1

/-- The unique all-order reduction comparison. -/
def reductionIsoOfLE {n m : ℕ} (h : n ≤ m) :
    (idealSheafQuotientFunctor X (K ^ n)).obj (F.obj.obj (op m)) ≅ F.obj.obj (op n) :=
  (F.exists_reductionIso_of_le h).choose

@[reassoc (attr := simp)]
theorem unit_reductionIsoOfLE_hom {n m : ℕ} (h : n ≤ m) :
    (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op m)) ≫
      (F.reductionIsoOfLE h).hom = F.obj.map (homOfLE h).op :=
  (F.exists_reductionIso_of_le h).choose_spec

/-- All original transition maps, not just adjacent transitions, are epimorphisms. -/
instance map_epi {n m : ℕ} (h : n ≤ m) : Epi (F.obj.map (homOfLE h).op) := by
  rw [← F.unit_reductionIsoOfLE_hom h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
