/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual finite locally free sheaf ranks

`LocalBasisFibreDimension` is the primitive general theorem retained here:
pull back an actual finite local free presentation through a field-valued
point in its trivializing open, and evaluate it as a finite free vector space.
This is a corollary of Stacks 01C8 and the stalk-basis rank proof of 01C9,
not their literal statement. Official pages inspected 2026-10-09; 01C8 has
an omitted proof and no correction comments; 01C9 has only a notation comment.

The finite-local-freeness witness is identified with the canonical class
from `LocallyFreeSheaf.Basic` by the same local basis. Rank results consume
that class, and category objects inherit its existing instance.

Local constancy, connected constancy, and the two directions of detection at
all geometric points are proved from this primitive family. The reverse
removes empty basis opens and uses an algebraic closure of each residue field;
the empty scheme is not excluded. No morphism degree or point count is an input.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering7f86e4a with frozen pins.
-/

@[expose] public section
/-!
Provenance: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Mathematical-source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {Y : Scheme.{u}}
/-- The historical rank-input name is the canonical finite-local-freeness class. -/
abbrev SheafFiniteLocallyFree (M : Y.Modules) : Prop := IsFiniteLocallyFree Y M

/-- The existing finite-type data records exactly finite generator indices on
all cover members; it imposes no finiteness condition on the cover itself. -/
theorem localGeneratorsData_isFiniteType_iff (M : Y.Modules)
    (q : M.LocalGeneratorsData.{u}) :
    q.IsFiniteType ↔ ∀ i, Finite (q.generators i).I := by
  constructor
  · intro h i
    exact (h.isFiniteType i).finite
  · intro h
    exact ⟨fun i ↦ ⟨h i⟩⟩

/-- The canonical class and the original rank-input witness use the same
local basis. This equivalence neither changes the sheaf nor refines its cover. -/
theorem isFiniteLocallyFree_iff_exists_localBasis (M : Y.Modules) :
    IsFiniteLocallyFree Y M ↔ ∃ q : M.LocalGeneratorsData.{u},
      q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I := by
  constructor
  · intro h
    obtain ⟨q, hq, hf⟩ := h.exists_localBasis
    exact ⟨q, hq, (localGeneratorsData_isFiniteType_iff M q).mp hf⟩
  · rintro ⟨q, hq, hf⟩
    exact ⟨q, hq, (localGeneratorsData_isFiniteType_iff M q).mpr hf⟩

/-- A local basis of `M` with every generator index set equivalent to `Fin n`. -/
def SheafHasRank (M : Y.Modules) (n : ℕ) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
    ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

/-- A displayed finite rank is a finite local basis in the canonical class. -/
theorem SheafHasRank.isFiniteLocallyFree {M : Y.Modules} {n : ℕ}
    (h : SheafHasRank M n) : IsFiniteLocallyFree Y M := by
  obtain ⟨q, hq, hn⟩ := h
  apply (isFiniteLocallyFree_iff_exists_localBasis M).mpr
  exact ⟨q, hq, fun i ↦ Finite.of_equiv (Fin n) (hn i).some.symm⟩

/-- The assertion that finite local bases give finite field fibres whose finrank equals the
cardinality of the basis on every covering open containing the field-valued point. -/
def LocalBasisFibreDimension : Prop :=
  ∀ (Y : Scheme.{u}) (M : Y.Modules) (q : M.LocalGeneratorsData.{u}),
    q.IsLocallyFreeData → (∀ i, Finite (q.generators i).I) →
    ∀ (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y) (i : q.I),
      p default ∈ q.X i → Module.Finite K (moduleFibre K M p) ∧
        Module.finrank K (moduleFibre K M p) = Nat.card (q.generators i).I

/-- The finrank of the fibre of `M` over the residue field at `y`. -/
def sheafRank (M : Y.Modules) (y : Y) : ℕ :=
  Module.finrank (Y.residueField y) (moduleFibre (Y.residueField y) M (Y.fromSpecResidueField y))

theorem sheafRank_eq_card_of_mem (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) (q : M.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData)
    (hfin : ∀ i, Finite (q.generators i).I) (y : Y) (i : q.I) (hi : y ∈ q.X i) :
    sheafRank M y = Nat.card (q.generators i).I := by
  exact (hlocal Y M q hq hfin (Y.residueField y) (Y.fromSpecResidueField y) i
    (by
      have he : (Y.fromSpecResidueField y) default = y :=
        Scheme.fromSpecResidueField_apply (X := Y) y default
      exact (congrArg (fun z : Y ↦ z ∈ q.X i) he).mpr hi)).2

theorem sheafRank_locallyConstant (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M] : IsLocallyConstant (sheafRank M) := by
  obtain ⟨q, hq, hf⟩ := (isFiniteLocallyFree_iff_exists_localBasis M).mp inferInstance
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro y
  obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem y
  refine ⟨q.X i, (q.X i).isOpen, hi, fun y' hy' ↦ ?_⟩
  exact (sheafRank_eq_card_of_mem hlocal M q hq hf y' i hy').trans
    (sheafRank_eq_card_of_mem hlocal M q hq hf y i hi).symm

/-- The local generating family obtained from `q` by discarding empty covering opens. -/
def nonemptyLocalGenerators (M : Y.Modules) (q : M.LocalGeneratorsData.{u}) :
    M.LocalGeneratorsData.{u} where
  I := {i : q.I // (q.X i : Set Y).Nonempty}
  X i := q.X i.val
  coversTop := by
    apply (Opens.coversTop_iff Y _).mpr
    apply top_le_iff.mp
    intro y _
    obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem y
    exact Opens.mem_iSup.mpr ⟨⟨i, y, hi⟩, hi⟩
  generators i := q.generators i.val

theorem nonemptyLocalGenerators_isLocallyFree (M : Y.Modules)
    (q : M.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData) :
    (nonemptyLocalGenerators M q).IsLocallyFreeData := by
  constructor
  intro i
  exact hq.isIso i.val

theorem sheafHasRank_iff_geometric_fibres (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M] (n : ℕ) :
    SheafHasRank M n ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (p : Spec (CommRingCat.of K) ⟶ Y), Module.finrank K (moduleFibre K M p) = n := by
  constructor
  · rintro ⟨q, hq, hn⟩ K _ _ p
    have hfin : ∀ i, Finite (q.generators i).I :=
      fun i ↦ Finite.of_equiv (Fin n) (hn i).some.symm
    obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem (p default)
    exact (hlocal Y M q hq hfin K p i hi).2.trans
      ((Nat.card_congr (hn i).some).trans (by simp))
  · intro hgeom
    obtain ⟨q, hq, hfin⟩ := (isFiniteLocallyFree_iff_exists_localBasis M).mp inferInstance
    refine ⟨nonemptyLocalGenerators M q, nonemptyLocalGenerators_isLocallyFree M q hq, ?_⟩
    intro i
    obtain ⟨y, hy⟩ := i.property
    let K := AlgebraicClosure (Y.residueField y)
    let p : Spec (CommRingCat.of K) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
    have hp : p default ∈ q.X i.val := by
      change Y.fromSpecResidueField y _ ∈ q.X i.val
      rw [Scheme.fromSpecResidueField_apply]
      exact hy
    have hc : Nat.card (q.generators i.val).I = n :=
      (hlocal Y M q hq hfin K p i.val hp).2.symm.trans (hgeom K p)
    letI := hfin i.val
    letI := Fintype.ofFinite (q.generators i.val).I
    change Nonempty ((q.generators i.val).I ≃ Fin n)
    exact ⟨Fintype.equivFinOfCardEq (by simpa [Nat.card_eq_fintype_card] using hc)⟩
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {Y : Scheme.{u}}
theorem moduleFibre_finrank_eq_sheafRank (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M]
    (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y) :
    Module.finrank K (moduleFibre K M p) = sheafRank M (p default) := by
  obtain ⟨q, hq, hf⟩ := (isFiniteLocallyFree_iff_exists_localBasis M).mp inferInstance
  obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem (p default)
  exact (hlocal Y M q hq hf K p i hi).2.trans
    (sheafRank_eq_card_of_mem hlocal M q hq hf (p default) i hi).symm

theorem moduleFibre_finite (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M]
    (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y) :
    Module.Finite K (moduleFibre K M p) := by
  obtain ⟨q, hq, hf⟩ := (isFiniteLocallyFree_iff_exists_localBasis M).mp inferInstance
  obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem (p default)
  exact (hlocal Y M q hq hf K p i hi).1

theorem sheafHasRank_iff_rank_eq (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M] (n : ℕ) :
    SheafHasRank M n ↔ ∀ y, sheafRank M y = n := by
  constructor
  · rintro ⟨q, hq, hn⟩ y
    have hf : ∀ i, Finite (q.generators i).I :=
      fun i ↦ Finite.of_equiv (Fin n) (hn i).some.symm
    obtain ⟨i, hi⟩ := (Opens.coversTop_iff Y q.X).mp q.coversTop |>.exists_mem y
    exact (sheafRank_eq_card_of_mem hlocal M q hq hf y i hi).trans
      ((Nat.card_congr (hn i).some).trans (by simp))
  · intro h
    apply (sheafHasRank_iff_geometric_fibres hlocal M n).mpr
    intro K _ _ p
    exact (moduleFibre_finrank_eq_sheafRank hlocal M K p).trans (h _)

theorem exists_sheafHasRank (hlocal : LocalBasisFibreDimension.{u})
    (M : Y.Modules) [IsFiniteLocallyFree Y M] [ConnectedSpace Y] :
    ∃ n : ℕ, SheafHasRank M n := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  refine ⟨sheafRank M y, (sheafHasRank_iff_rank_eq hlocal M _).mpr ?_⟩
  exact fun z ↦ (sheafRank_locallyConstant hlocal M).apply_eq_of_preconnectedSpace z y
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.FiniteLocallyFree

universe u

variable {Y : Scheme.{u}}

/-- The actual residue-field fibre rank of a finite locally free category object. -/
def rank (M : Scheme.Modules.FiniteLocallyFree Y) : Y → ℕ := sheafRank M.obj

/-- The category-object rank uses its existing canonical local-freeness instance. -/
theorem rank_locallyConstant (hlocal : LocalBasisFibreDimension.{u})
    (M : Scheme.Modules.FiniteLocallyFree Y) : IsLocallyConstant (rank M) :=
  sheafRank_locallyConstant hlocal M.obj

/-- Constant rank on a category object is detected by its actual residue fibres. -/
theorem hasRank_iff_rank_eq (hlocal : LocalBasisFibreDimension.{u})
    (M : Scheme.Modules.FiniteLocallyFree Y) (n : ℕ) :
    SheafHasRank M.obj n ↔ ∀ y, rank M y = n :=
  sheafHasRank_iff_rank_eq hlocal M.obj n

/-- Connectedness gives a constant finite rank, retaining the same fibre premise. -/
theorem exists_hasRank (hlocal : LocalBasisFibreDimension.{u})
    (M : Scheme.Modules.FiniteLocallyFree Y) [ConnectedSpace Y] :
    ∃ n : ℕ, SheafHasRank M.obj n :=
  exists_sheafHasRank hlocal M.obj

end AlgebraicGeometry.Scheme.Modules.FiniteLocallyFree
