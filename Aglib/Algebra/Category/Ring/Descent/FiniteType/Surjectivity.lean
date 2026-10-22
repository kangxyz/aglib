/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.RingTheory.FiniteType

/-!
# Surjectivity at a finite stage

A finite-type map in a filtered diagram of commutative rings becomes surjective
at a later stage if its colimit map is surjective and the naturality squares
from the specified stage are pushouts. This is the categorical base-change
form of Stacks Project, Tag 07RH. A more general core only assumes that
the old target ring and the new source ring generate each later target.
Finite presentation is not required.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe vI uI u

namespace CommRingCat

/-- Surjectivity descends to a later stage for a finite-type ring map with
propagation by the two specified ring images. The specified colimit maps need not be
injective. The explicit preservation assumptions allow the index objects,
index morphisms, and rings to lie in independent universes. -/
lemma exists_surjective_app_of_isColimit_of_closure_eq_top
    {I : Type uI} [Category.{vI} I] [IsFiltered I]
    (F G : I ⥤ CommRingCat.{u}) (α : F ⟶ G)
    (cF : Cocone F) (hF : IsColimit cF)
    (cG : Cocone G) (hG : IsColimit cG)
    [PreservesColimit F (forget CommRingCat)]
    [PreservesColimit G (forget CommRingCat)]
    (φ : cF.pt ⟶ cG.pt)
    (hφ : ∀ j, α.app j ≫ cG.ι.app j = cF.ι.app j ≫ φ)
    (i : I) (hfinite : (α.app i).hom.FiniteType)
    (hgenerate : ∀ (j : I) (q : i ⟶ j),
      Subring.closure (Set.range (G.map q) ∪ Set.range (α.app j)) = ⊤)
    (hsurj : Function.Surjective φ) :
    ∃ (j : I) (_q : i ⟶ j), Function.Surjective (α.app j) := by
  classical
  let : Algebra (F.obj i) (G.obj i) := (α.app i).hom.toAlgebra
  let : Algebra.FiniteType (F.obj i) (G.obj i) := hfinite
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (F.obj i) (G.obj i)).FG)
  have hF' := isColimitOfPreserves (forget CommRingCat) hF
  have hG' := isColimitOfPreserves (forget CommRingCat) hG
  choose b hb using fun x : s ↦ hsurj (cG.ι.app i x.1)
  choose k a ha using fun x : s ↦ Types.jointly_surjective_of_isColimit hF' (b x)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (insert i (Finset.univ.image k))
  let q : i ⟶ j := (hj (Finset.mem_insert_self _ _)).some
  let r (x : s) : k x ⟶ j :=
    (hj (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))).some
  let a' (x : s) : F.obj j := F.map (r x) (a x)
  have heq (x : s) :
      cG.ι.app j (α.app j (a' x)) = cG.ι.app j (G.map q x.1) := by
    calc
      _ = φ (cF.ι.app j (a' x)) := congr($(hφ j).hom (a' x))
      _ = φ (b x) := by
        congr 1
        change (F.map (r x) ≫ cF.ι.app j) (a x) = b x
        rw [cF.w]
        exact ha x
      _ = cG.ι.app i x.1 := hb x
      _ = _ := by
        change cG.ι.app i x.1 = (G.map q ≫ cG.ι.app j) x.1
        rw [cG.w]
  choose l t ht using fun x : s ↦
    (Types.FilteredColimit.isColimit_eq_iff' hG'
      (α.app j (a' x)) (G.map q x.1)).mp (heq x)
  obtain ⟨C⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j l t)
  let p : j ⟶ C.pt := C.ι.app none
  let q' : i ⟶ C.pt := q ≫ p
  have hgen (x : s) : G.map q' x.1 ∈ (α.app C.pt).hom.range := by
    refine ⟨F.map p (a' x), ?_⟩
    have hx : G.map p (α.app j (a' x)) = G.map p (G.map q x.1) := by
      have hp : p = t x ≫ C.ι.app (some x) := (C.w (.init x)).symm
      rw [hp, G.map_comp]
      change G.map (C.ι.app (some x)) (G.map (t x) (α.app j (a' x))) =
        G.map (C.ι.app (some x)) (G.map (t x) (G.map q x.1))
      exact congrArg (fun z : G.obj (l x) ↦ G.map (C.ι.app (some x)) z) (ht x)
    calc
      _ = G.map p (α.app j (a' x)) := congr($(α.naturality p).hom (a' x))
      _ = G.map p (G.map q x.1) := hx
      _ = _ := by simp [q', G.map_comp]
  let T : Subalgebra (F.obj i) (G.obj i) :=
    { ((α.app C.pt).hom.range.comap (G.map q').hom).toSubsemiring with
      algebraMap_mem' r := by
        refine ⟨F.map q' r, ?_⟩
        exact congr($(α.naturality q').hom r) }
  have hT : (⊤ : Subalgebra (F.obj i) (G.obj i)) ≤ T := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    exact hgen ⟨x, hx⟩
  have hrange : Set.range (G.map q') ⊆ (α.app C.pt).hom.range := by
    rintro _ ⟨x, rfl⟩
    exact hT (show x ∈ (⊤ : Subalgebra (F.obj i) (G.obj i)) from trivial)
  refine ⟨C.pt, q', RingHom.range_eq_top.mp ?_⟩
  apply top_unique
  rw [← hgenerate C.pt q']
  apply Subring.closure_le.mpr
  exact Set.union_subset hrange (fun _ hx ↦ hx)

/-- Surjectivity descends to a later stage for a finite-type ring map with
actual pushout transition squares. The specified colimit maps need not be
injective. The explicit preservation assumptions allow the index objects,
index morphisms, and rings to lie in independent universes. -/
lemma exists_surjective_app_of_isColimit
    {I : Type uI} [Category.{vI} I] [IsFiltered I]
    (F G : I ⥤ CommRingCat.{u}) (α : F ⟶ G)
    (cF : Cocone F) (hF : IsColimit cF)
    (cG : Cocone G) (hG : IsColimit cG)
    [PreservesColimit F (forget CommRingCat)]
    [PreservesColimit G (forget CommRingCat)]
    (φ : cF.pt ⟶ cG.pt)
    (hφ : ∀ j, α.app j ≫ cG.ι.app j = cF.ι.app j ≫ φ)
    (i : I) (hfinite : (α.app i).hom.FiniteType)
    (hpush : ∀ (j : I) (q : i ⟶ j),
      IsPushout (α.app i) (F.map q) (G.map q) (α.app j))
    (hsurj : Function.Surjective φ) :
    ∃ (j : I) (_q : i ⟶ j), Function.Surjective (α.app j) := by
  exact exists_surjective_app_of_isColimit_of_closure_eq_top
    F G α cF hF cG hG φ hφ i hfinite
    (fun j q ↦ closure_range_union_range_eq_top_of_isPushout (hpush j q)) hsurj

end CommRingCat
