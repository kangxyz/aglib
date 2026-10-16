/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.ResidueConcentration
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# A single finite-free model detected by the residue field

A bounded complex of finite projective modules over a local ring whose actual
residue-field homology is concentrated in degree zero is homotopy equivalent to
a single finite free module in degree zero. The construction iterates the actual
lower and upper truncation cancellations.

The canonical homology base-change map of any complex homotopy equivalent to a
single module is invertible after every ring map, in every degree. Its proof
uses naturality of the original adjunction-unit map and the actual homology
maps of the homotopy equivalence.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CochainComplex

/-- A homotopy equivalence to a single module makes the original canonical
homology base-change map invertible in every degree, without flatness. -/
theorem extendScalarsHomologyMap_isIso_of_homotopyEquiv_single
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (φ : R →+* S)
    (K : CochainComplex (ModuleCat.{max v w} R) ℤ) (P : ModuleCat.{max v w} R)
    (e : HomotopyEquiv K ((singleFunctor (ModuleCat.{max v w} R) 0).obj P)) (n : ℤ) :
    IsIso (extendScalarsHomologyMap φ K n) := by
  let J := (singleFunctor (ModuleCat.{max v w} R) 0).obj P
  let F := ModuleCat.extendScalars φ
  have : IsIso (homologyMap e.hom n) := (e.toHomologyIso n).isIso_hom
  have : IsIso (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map e.hom) n) :=
    ((F.mapHomotopyEquiv e).toHomologyIso n).isIso_hom
  have : IsIso (extendScalarsHomologyMap φ J n) :=
    extendScalarsHomologyMap_isIso_of_d_eq_zero φ J n rfl
  have hc :
      F.mapShortComplex.map
          ((shortComplexFunctor (ModuleCat.{max v w} R) (.up ℤ) n).map e.hom) =
        (shortComplexFunctor (ModuleCat.{max v w} S) (.up ℤ) n).map
          ((F.mapHomologicalComplex (.up ℤ)).map e.hom) := by ext <;> rfl
  have hnat : F.map (homologyMap e.hom n) ≫ extendScalarsHomologyMap φ J n =
      extendScalarsHomologyMap φ K n ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map e.hom) n := by
    have h := ModuleCat.homologyBaseChangeMap_naturality φ
      ((shortComplexFunctor (ModuleCat.{max v w} R) (.up ℤ) n).map e.hom)
    change F.map (homologyMap e.hom n) ≫ extendScalarsHomologyMap φ J n =
      extendScalarsHomologyMap φ K n ≫ ShortComplex.homologyMap
        (F.mapShortComplex.map
          ((shortComplexFunctor (ModuleCat.{max v w} R) (.up ℤ) n).map e.hom)) at h
    rw [hc] at h
    exact h
  have heq : extendScalarsHomologyMap φ K n =
      F.map (homologyMap e.hom n) ≫ extendScalarsHomologyMap φ J n ≫
        inv (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map e.hom) n) := by
    apply (cancel_mono (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map e.hom) n)).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hnat.symm
  rw [heq]
  infer_instance

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A bounded finite-projective complex over a local ring with residue-field
homology concentrated at zero has an actual single finite-free model. -/
theorem exists_homotopyEquiv_single_of_residue_homology_nat_bounds
    (m n : ℕ) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [K.IsStrictlyGE (-(m : ℤ))] [K.IsStrictlyLE (n : ℤ)]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (hfibre : ∀ i : ℤ, i ≠ 0 → IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology i)) :
    ∃ P : ModuleCat.{max u v} R, Module.Finite R P ∧ Module.Free R P ∧
      Nonempty (HomotopyEquiv K ((singleFunctor (ModuleCat.{max u v} R) 0).obj P)) := by
  have (i : ℤ) : Module.Free R (K.X i) := Module.free_of_flat_of_isLocalRing
  obtain ⟨L, hge, hle, hfinite, hfree, ⟨e⟩⟩ :=
    exists_homotopyEquiv_isStrictlyGE_zero_of_residue_homology_neg m (n : ℤ) K
      (fun i hi => hfibre i (ne_of_lt hi))
  have : L.IsStrictlyGE 0 := hge
  have : L.IsStrictlyLE (n : ℤ) := hle
  have (i : ℤ) : Module.Finite R (L.X i) := hfinite i
  have (i : ℤ) : Module.Free R (L.X i) := hfree i
  let F := ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))
  have hL : ∀ i : ℤ, 0 < i → IsZero
      (((F.mapHomologicalComplex (.up ℤ)).obj L).homology i) := by
    intro i hi
    exact IsZero.of_iso (hfibre i (ne_of_gt hi)) ((F.mapHomotopyEquiv e).toHomologyIso i).symm
  obtain ⟨L', hge', hle', hfinite', hfree', ⟨e'⟩⟩ :=
    exists_homotopyEquiv_isStrictlyLE_zero_of_residue_homology_pos n L hL
  have : L'.IsStrictlyGE 0 := hge'
  have : L'.IsStrictlyLE 0 := hle'
  have (i : ℤ) : Module.Finite R (L'.X i) := hfinite' i
  have (i : ℤ) : Module.Free R (L'.X i) := hfree' i
  obtain ⟨P, ⟨s⟩⟩ := L'.exists_iso_single 0
  let t : L'.X 0 ≅ P :=
    (HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) 0).mapIso s ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 P
  exact ⟨P, Module.Finite.equiv t.toLinearEquiv, Module.Free.of_equiv t.toLinearEquiv,
    ⟨e.trans (e'.trans (HomotopyEquiv.ofIso s))⟩⟩

/-- Integer lower and upper term bounds give the same native single finite-free
model; the bounds need not straddle zero. -/
theorem exists_homotopyEquiv_single_of_residue_homology
    (a b : ℤ) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (hfibre : ∀ i : ℤ, i ≠ 0 → IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology i)) :
    ∃ P : ModuleCat.{max u v} R, Module.Finite R P ∧ Module.Free R P ∧
      Nonempty (HomotopyEquiv K ((singleFunctor (ModuleCat.{max u v} R) 0).obj P)) := by
  have ha : -((a.natAbs : ℕ) : ℤ) ≤ a := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le a
  have hb : b ≤ ((b.natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact le_abs_self b
  have := K.isStrictlyGE_of_ge (-((a.natAbs : ℕ) : ℤ)) a ha
  have := K.isStrictlyLE_of_le b ((b.natAbs : ℕ) : ℤ) hb
  exact exists_homotopyEquiv_single_of_residue_homology_nat_bounds a.natAbs b.natAbs K hfibre

/-- Native residue concentration of a bounded finite-projective complex over
a local ring makes the original canonical base-change map invertible in every
degree, after an arbitrary ring map. -/
theorem extendScalarsHomologyMap_isIso_of_residue_concentration
    {S : Type w} [CommRing S] (φ : R →+* S) (a b : ℤ)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (hfibre : ∀ i : ℤ, i ≠ 0 → IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology i)) (i : ℤ) :
    IsIso (extendScalarsHomologyMap.{u, max u v, w, 0} φ K i) := by
  obtain ⟨P, _, _, ⟨e⟩⟩ :=
    exists_homotopyEquiv_single_of_residue_homology.{u, max v w} a b K hfibre
  exact extendScalarsHomologyMap_isIso_of_homotopyEquiv_single.{u, max u v, w} φ K P e i

section LocalConsequences

variable (a b : ℤ) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
  [hge : K.IsStrictlyGE a] [hle : K.IsStrictlyLE b]
  [hfinite : ∀ i, Module.Finite R (K.X i)] [hprojective : ∀ i, Module.Projective R (K.X i)]
  (hfibre : ∀ i : ℤ, i ≠ 0 → IsZero
    ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (.up ℤ)).obj K).homology i))

include a b hfibre hge hle hfinite hprojective

/-- The degree-zero native homology is finite under residue concentration. -/
theorem finite_homology_zero_of_residue_concentration : Module.Finite R (K.homology 0) := by
  obtain ⟨P, hfinite, _, ⟨e⟩⟩ :=
    exists_homotopyEquiv_single_of_residue_homology a b K hfibre
  have : Module.Finite R P := hfinite
  exact Module.Finite.equiv
    (e.toHomologyIso 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P).symm.toLinearEquiv

/-- The degree-zero native homology is free over the original local ring. -/
theorem free_homology_zero_of_residue_concentration : Module.Free R (K.homology 0) := by
  obtain ⟨P, _, hfree, ⟨e⟩⟩ :=
    exists_homotopyEquiv_single_of_residue_homology a b K hfibre
  have : Module.Free R P := hfree
  exact Module.Free.of_equiv
    (e.toHomologyIso 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P).symm.toLinearEquiv

/-- Every other native homology object vanishes over the original local ring. -/
theorem isZero_homology_of_residue_concentration (i : ℤ) (hi : i ≠ 0) :
    IsZero (K.homology i) := by
  obtain ⟨P, _, _, ⟨e⟩⟩ :=
    exists_homotopyEquiv_single_of_residue_homology a b K hfibre
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 P i hi) (e.toHomologyIso i)

/-- The finite-free rank is the dimension of the actual residue-field
zero-th homology, using the original canonical base-change isomorphism. -/
theorem finrank_homology_zero_eq_residue_of_concentration :
    Module.finrank R (K.homology 0) =
      Module.finrank (IsLocalRing.ResidueField R)
        ((((ModuleCat.extendScalars (algebraMap R
          (IsLocalRing.ResidueField R))).mapHomologicalComplex (.up ℤ)).obj K).homology 0) := by
  have : Module.Free R (K.homology 0) :=
    free_homology_zero_of_residue_concentration a b K hfibre
  let φ := algebraMap R (IsLocalRing.ResidueField R)
  have : IsIso (extendScalarsHomologyMap φ K 0) :=
    extendScalarsHomologyMap_isIso_of_residue_concentration.{u, v, u} φ a b K hfibre 0
  let e := (asIso (extendScalarsHomologyMap φ K 0)).toLinearEquiv
  calc
    Module.finrank R (K.homology 0) =
        Module.finrank (IsLocalRing.ResidueField R)
          ((ModuleCat.extendScalars φ).obj (K.homology 0)) := by
      symm
      change Module.finrank (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] (K.homology 0)) = _
      exact Module.finrank_baseChange
    _ = _ := e.finrank_eq

end LocalConsequences

end CochainComplex
