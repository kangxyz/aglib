/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.Cochain
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ComplexRepresentatives

/-!
# A small family of bounded-above acyclic complexes

The family is constructed by filtering the actual small codes for complexes.
Every separator map into an acyclic complex factors through a monic map from
one of these representatives. No detection or replacement property is assumed.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- The actual set-sized small acyclic family needed by the transfinite
construction. Its factorization property comes from the constructed small
acyclic subcomplex, rather than from an assumed detecting family. -/
lemma exists_small_acyclic_family :
    ∃ (I : Type w) (R : I → CochainComplex C ℤ),
      (∀ i, (R i).Acyclic) ∧
      (∀ i, ∃ n : ℤ, (R i).IsStrictlyLE n) ∧
      (∀ i n, HasCardinalLT (Subobject ((R i).X n)) (smallAcyclicCardinal hG)) ∧
      ∀ (M : CochainComplex C ℤ), M.Acyclic → ∀ (n : ℤ) (ψ : G ⟶ M.X n),
        ∃ (i : I) (f : R i ⟶ M) (a : G ⟶ (R i).X n),
          (∀ m, Mono (f.f m)) ∧ a ≫ f.f n = ψ := by
  classical
  let κ := smallAcyclicCardinal hG
  obtain ⟨J, Q, hQ⟩ := exists_small_complex_representatives hG κ
  let P (j : J) : Prop := (Q j).Acyclic ∧ (∃ n : ℤ, (Q j).IsStrictlyLE n) ∧
    ∀ n, HasCardinalLT (Subobject ((Q j).X n)) κ
  refine ⟨{j : J // P j}, fun j ↦ Q j.val, (fun j ↦ j.property.1),
    (fun j ↦ j.property.2.1), (fun j ↦ j.property.2.2), ?_⟩
  intro M hM n ψ
  obtain ⟨L, f, hf, hL, hb, hs, a, ha⟩ :=
    exists_small_acyclic_subcomplex hG M hM n ψ
  have hbound (m : ℤ) : Cardinal.mk (Shrink.{w} (Subobject (L.X m))) ≤ κ := by
    have h := (hasCardinalLT_iff_of_equiv (equivShrink.{w} (Subobject (L.X m))) κ).1
      (hs m)
    exact ((hasCardinalLT_iff_cardinal_mk_lt _ κ).1 h).le
  obtain ⟨j, ⟨e⟩⟩ := hQ L hbound
  have hP : P j := by
    refine ⟨(fun m ↦ (hL m).of_iso e), ⟨n + 1, ?_⟩, ?_⟩
    · have := hb
      exact isStrictlyLE_of_iso e (n + 1)
    · intro m
      exact Subobject.hasCardinalLT_of_mono (hs m)
        (HomologicalComplex.Hom.isoApp e m).inv
  refine ⟨⟨j, hP⟩, e.inv ≫ f, a ≫ e.hom.f n, ?_, ?_⟩
  · intro m
    have := hf m
    change Mono (e.inv.f m ≫ f.f m)
    infer_instance
  · change (a ≫ (HomologicalComplex.Hom.isoApp e n).hom) ≫
        (HomologicalComplex.Hom.isoApp e n).inv ≫ f.f n = ψ
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ha

end CochainComplex
