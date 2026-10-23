/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.FiniteCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Strata
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantCompactness
public import Aglib.CategoryTheory.Sites.Torsion.Colimit

/-! # Positive global annihilators of actual constructible coefficients

Compactness factors the identity of a finitely presentable internally torsion
sheaf through its actual factorial-annihilator colimit. This constructs a
positive global annihilator; internal local torsion alone is not used as a
global bound. The index-size restriction is discharged by the native theorem
that preservation of filtered colimits descends to smaller index universes.

On a qcqs scheme, the actual finite constructible cover has qcqs source strata.
Its finite locally constant restrictions are compact, hence positively bounded.
Their finite product annihilator is positive (also for the empty cover), and
joint faithfulness of the original stratum inverse images detects the original
scalar identity equation on the original coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

/-- A finitely presentable internally torsion coefficient has a positive global
annihilator, by factorization of its identity through the original kernel colimit. -/
theorem exists_positive_annihilator_of_isFinitelyPresentable {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) [IsFinitelyPresentable.{u + 1} F]
    (hF : IsTorsion X F) : ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (op F)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, 0, 0} _
  have : IsFinitelyPresentable.{0} F :=
    isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr inferInstance
  obtain ⟨k, b, hb⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (Sheaf.factorialAnnihilatorCoconeIsColimit F hF) (𝟙 F)
  let q : F ⟶ Sheaf.annihilator F (k + 1).factorial := b
  have hq : q ≫ Sheaf.annihilatorι F (k + 1).factorial = 𝟙 F := hb
  refine ⟨(k + 1).factorial, Nat.factorial_pos _, ?_⟩
  calc
    (k + 1).factorial • 𝟙 F =
        (k + 1).factorial • (q ≫ Sheaf.annihilatorι F (k + 1).factorial) :=
      congrArg (fun a => (k + 1).factorial • a) hq.symm
    _ = q ≫ ((k + 1).factorial • Sheaf.annihilatorι F (k + 1).factorial) :=
      (Preadditive.comp_nsmul _ _ _).symm
    _ = 0 := by rw [Sheaf.nsmul_annihilatorι, comp_zero]

/-- A finite locally constant sheaf on a qcqs scheme has a positive global
annihilator; its actual compactness and torsion properties are both produced. -/
theorem exists_positive_annihilator_of_finiteLocallyConstant {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  have := isFinitelyPresentable_of_isFiniteLocallyConstant F hF
  exact exists_positive_annihilator_of_isFinitelyPresentable F
    (isTorsion_of_isConstructible F (isConstructible_of_isFiniteLocallyConstant hF))

/-- A constructible subset of a compact scheme is compact. This is the elementary
finite union of differences of compact open sets argument. -/
theorem isCompact_of_constructible {X : Scheme.{u}} [CompactSpace X]
    (s : Set X) (hs : Topology.IsConstructible s) : IsCompact s := by
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht => ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht => ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV => exact hU.2.isCompact.diff hV.1
  | sup s _ t _ hs ht => exact hs.union ht

namespace FiniteLocallyClosedCover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {F : AbelianSheaf.{u, u + 1} X} (t : FiniteLocallyClosedCover F)

omit [QuasiSeparatedSpace X] in
/-- The actual source of every constructible immersion in this finite cover is compact. -/
theorem compact_stratum (i : t.index) : CompactSpace (t.stratum i) := by
  have : IsImmersion (t.inclusion i) := t.immersion i
  constructor
  apply (t.inclusion i).isEmbedding.isCompact_iff.mpr
  rw [Set.image_univ]
  exact isCompact_of_constructible _ (t.constructible_range i)

omit [CompactSpace X] in
/-- The actual source of an immersion into the quasi-separated base is quasi-separated. -/
theorem quasiSeparated_stratum (i : t.index) : QuasiSeparatedSpace (t.stratum i) := by
  have : IsImmersion (t.inclusion i) := t.immersion i
  exact quasiSeparatedSpace_of_quasiSeparated (t.inclusion i)

/-- The original FLC restriction on each actual stratum has a positive annihilator. -/
theorem exists_positive_annihilator_on_stratum (i : t.index) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 ((inverseImage (t.inclusion i)).obj F) = 0 := by
  have := t.compact_stratum i
  have := t.quasiSeparated_stratum i
  exact exists_positive_annihilator_of_finiteLocallyConstant _ (t.locally_constant i)

include t in
/-- The finite product of the produced positive stratum bounds annihilates the
original coefficient. The empty index gives the positive bound one. -/
theorem exists_positive_annihilator : ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  classical
  have : Finite t.index := t.finite_index
  let : Fintype t.index := Fintype.ofFinite t.index
  choose n hn hk using t.exists_positive_annihilator_on_stratum
  let N := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hn i)
  have (i : t.index) : IsImmersion (t.inclusion i) := t.immersion i
  refine ⟨N, hN, ?_⟩
  apply (jointlyFaithful_immersionInverseImages t.stratum t.inclusion t.covers).map_injective
  intro i
  have hdiv : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := hdiv
  have hkill : N • 𝟙 ((inverseImage (t.inclusion i)).obj F) = 0 := by
    rw [hm, Nat.mul_comm (n i) m, mul_smul, hk i, nsmul_zero]
  have hid : (inverseImage (t.inclusion i)).map (𝟙 F) =
      𝟙 ((inverseImage (t.inclusion i)).obj F) := (inverseImage (t.inclusion i)).map_id F
  have hnormal : N • (inverseImage (t.inclusion i)).map (𝟙 F) = 0 :=
    (congrArg (fun q => N • q) hid).trans hkill
  simpa only [Functor.map_nsmul, Functor.map_zero] using hnormal

end FiniteLocallyClosedCover

/-- Every actual constructible abelian sheaf on a qcqs scheme has a positive
global annihilator, using original coefficient maps and genuine compactness. -/
theorem exists_positive_annihilator_of_isConstructible {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 :=
  (finiteLocallyClosedCover F hF).exists_positive_annihilator

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
