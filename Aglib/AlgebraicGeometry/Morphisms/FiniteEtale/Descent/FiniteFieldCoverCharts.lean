/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# A finite locally directed cover of a qcqs scheme

Close a finite open cover under nonempty finite intersections. All pieces stay
quasi-compact and quasi-separated; each piece lies in an original chart.
The index and arrow sets are finite, which is the finiteness input for choosing
one field stage for the local gluing maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u v
variable {X : Scheme.{u}} {ι : Type v}

/-- Nonempty finite subsets of the chart index type, ordered by reverse inclusion. -/
abbrev IntersectionIndex (ι : Type v) := OrderDual {s : Finset ι // s.Nonempty}

/-- The intersection of the opens indexed by the nonempty finite set `s`. -/
def intersectionOpen (U : ι → X.Opens) (s : IntersectionIndex ι) : X.Opens :=
  s.val.inf U

lemma intersectionOpen_le (U : ι → X.Opens) {s t : IntersectionIndex ι} (h : s ≤ t) :
    intersectionOpen U s ≤ intersectionOpen U t := by
  apply Finset.le_inf
  intro i hi
  exact Finset.inf_le (h hi)

lemma intersectionOpen_singleton (U : ι → X.Opens) (i : ι) :
    intersectionOpen U ⟨{i}, by simp⟩ = U i := by
  classical
  simp [intersectionOpen]

lemma isOpenCover_intersectionOpen (U : ι → X.Opens) (hU : IsOpenCover U) :
    IsOpenCover (intersectionOpen U) := by
  classical
  apply IsOpenCover.mk
  apply top_unique
  rw [← hU.iSup_eq_top]
  exact iSup_le fun i ↦ le_iSup_of_le ⟨{i}, by simp⟩ (by simp [intersectionOpen])

/-- The open cover consisting of all nonempty finite intersections of the given covering family. -/
def intersectionCover (U : ι → X.Opens) (hU : IsOpenCover U) : X.OpenCover :=
  X.openCoverOfIsOpenCover (intersectionOpen U) (isOpenCover_intersectionOpen U hU)

instance (U : ι → X.Opens) (hU : IsOpenCover U) :
    Category (intersectionCover U hU).I₀ :=
  inferInstanceAs (Category (IntersectionIndex ι))

instance (U : ι → X.Opens) (hU : IsOpenCover U) :
    Quiver.IsThin (intersectionCover U hU).I₀ :=
  inferInstanceAs (Quiver.IsThin (IntersectionIndex ι))

instance (U : ι → X.Opens) (hU : IsOpenCover U) [Finite ι] :
    Finite (intersectionCover U hU).I₀ := by
  classical
  let := Fintype.ofFinite ι
  change Finite (IntersectionIndex ι)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance intersectionCoverLocallyDirected (U : ι → X.Opens) (hU : IsOpenCover U) :
    (intersectionCover U hU).LocallyDirected where
  trans f := X.homOfLE (intersectionOpen_le U (leOfHom f))
  trans_id i := by
    change X.homOfLE _ = 𝟙 (intersectionOpen U i).toScheme
    simp
  trans_comp f g := by simp
  w f := by simp [intersectionCover]
  directed {i j} x := by
    classical
    let k : IntersectionIndex ι := ⟨i.val ∪ j.val, i.property.mono Finset.subset_union_left⟩
    let ki : k ⟶ i := homOfLE (show i.val ⊆ k.val from Finset.subset_union_left)
    let kj : k ⟶ j := homOfLE (show j.val ⊆ k.val from Finset.subset_union_right)
    let xi : intersectionOpen U i := pullback.fst ((intersectionCover U hU).f i)
      ((intersectionCover U hU).f j) x
    let xj : intersectionOpen U j := pullback.snd ((intersectionCover U hU).f i)
      ((intersectionCover U hU).f j) x
    have h : (xi : X) = (xj : X) := by
      have hc := congrArg (fun f : pullback ((intersectionCover U hU).f i)
        ((intersectionCover U hU).f j) ⟶ X ↦ f x)
        (pullback.condition (f := (intersectionCover U hU).f i) (g := (intersectionCover U hU).f j))
      exact hc
    let y : intersectionOpen U k := ⟨(xi : X), by
      change (xi : X) ∈ (i.val ∪ j.val).inf U
      rw [Finset.inf_union]
      exact ⟨xi.property, h.symm ▸ xj.property⟩⟩
    refine ⟨k, ki, kj, y, ?_⟩
    apply (pullback.fst ((intersectionCover U hU).f i)
      ((intersectionCover U hU).f j)).injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    apply Subtype.ext
    change ((X.homOfLE (intersectionOpen_le U (leOfHom ki))) y).val = xi.val
    rw [Scheme.homOfLE_apply]

lemma intersectionOpen_le_chart (U : ι → X.Opens) (s : IntersectionIndex ι) :
    ∃ i : ι, intersectionOpen U s ≤ U i := by
  obtain ⟨i, hi⟩ := s.property
  exact ⟨i, Finset.inf_le hi⟩

lemma isCompact_intersectionOpen [CompactSpace X] [QuasiSeparatedSpace X]
    (U : ι → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) (s : IntersectionIndex ι) :
    IsCompact (intersectionOpen U s : Set X) := by
  suffices ∀ t : Finset ι, IsCompact ((t.inf U : X.Opens) : Set X) from this s.val
  intro t
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isCompact_univ (X := X)
  | @insert i t hi ht =>
    simpa using (hU i).inter_of_isOpen ht (U i).isOpen (t.inf U).isOpen

theorem intersectionCover_compact [CompactSpace X] [QuasiSeparatedSpace X]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hcompact : ∀ i, IsCompact (U i : Set X))
    (s : (intersectionCover U hU).I₀) :
    CompactSpace ((intersectionCover U hU).X s) :=
  isCompact_iff_compactSpace.mp (isCompact_intersectionOpen U hcompact s)

instance intersectionCover_quasiSeparated [QuasiSeparatedSpace X]
    (U : ι → X.Opens) (hU : IsOpenCover U) (s : (intersectionCover U hU).I₀) :
    QuasiSeparatedSpace ((intersectionCover U hU).X s) :=
  quasiSeparatedSpace_of_quasiSeparated ((intersectionCover U hU).f s)

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 1dc9c7032e24b641cfda8e31974dea76b97bf00fe111211c77b390d14c59afc6.
Definitions, hypotheses and universes are retained modulo native names. -/
