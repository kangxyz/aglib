/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed.Geometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed.PointLift
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Fibrewise-closed geometric points detect every small-etale covering sieve -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed

universe u v

variable {T S : Scheme.{u}} (p : T ⟶ S)

/-- The actual points of `T` closed in their literal relative fibres. -/
abbrev Index := {x : T // IsFibrewiseClosed p x}

/-- The actual native point family at the standard larger coefficient universe. -/
def pointFamily : ObjectProperty (GrothendieckTopology.Point.{u + 1}
    (Scheme.smallEtaleTopology T)) :=
  ObjectProperty.ofObj (fun x : Index p => largePoint (geometricPoint x.val))

variable [LocallyOfFiniteType p]

/-- On every etale test object, covering families are detected by the actual
algebraically closed geometric points whose images are closed in their fibres. -/
theorem ofArrows_mem_iff_geometricLifts
    {U : T.Etale} {ι : Type v} {V : ι → T.Etale} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ Scheme.smallEtaleTopology T U ↔
      ∀ (x : Index p) (l : Spec (.of (pointField x.val)) ⟶ U.left),
        l ≫ U.hom = geometricPoint x.val →
          ∃ (i : ι) (m : Spec (.of (pointField x.val)) ⟶ (V i).left),
            m ≫ (f i).left = l := by
  constructor
  · intro h x l _
    have htop := (ofArrows_mem_smallEtaleTopology_iff f).mp h
    have hmem := Set.mem_univ (l default)
    rw [← htop] at hmem
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨m, hm, _⟩ := exists_fac_of_etale_of_isSepClosed (f i).left l y hy
    exact ⟨i, m, hm⟩
  · intro h
    rw [ofArrows_mem_smallEtaleTopology_iff]
    by_contra htop
    let W : Set U.left := ⋃ i, Set.range (f i).left
    have hclosed : IsClosed Wᶜ :=
      (isOpen_iUnion (fun i => (f i).left.isOpenMap.isOpen_range)).isClosed_compl
    have hne : Wᶜ.Nonempty := by
      by_contra hn
      apply htop
      exact Set.eq_univ_iff_forall.mpr fun u => by
        by_contra hu
        exact hn ⟨u, hu⟩
    obtain ⟨u, hu, huc⟩ := exists_mem_image_fibrewiseClosed p U.hom Wᶜ hclosed hne
    let x : Index p := ⟨U.hom u, huc⟩
    obtain ⟨l, hl, hlu⟩ := exists_fac_of_etale_of_isSepClosed U.hom
      (geometricPoint x.val) u (geometricPoint_apply x.val default).symm
    obtain ⟨i, m, hm⟩ := h x l hl
    apply hu
    refine Set.mem_iUnion.mpr ⟨i, m default, ?_⟩
    have he := congrArg (fun q : Spec (.of (pointField x.val)) ⟶ U.left => q default) hm
    change (f i).left (m default) = l default at he
    exact he.trans hlu

/-- Fibrewise-closed geometric points are a conservative family for the
actual small-etale site, at the standard larger point/value universe. -/
theorem pointFamily_isConservative : (pointFamily p).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  apply (ofArrows_mem_iff_geometricLifts p f).mpr
  intro x l hl
  let t : (largePoint (geometricPoint x.val)).fiber.obj U :=
    ULift.up (Over.homMk l hl)
  obtain ⟨W, g, ⟨Z, k, _, ⟨i⟩, rfl⟩, y, hy⟩ :=
    hR ⟨largePoint (geometricPoint x.val), ⟨x⟩⟩ t
  refine ⟨i, y.down.left ≫ k.left, ?_⟩
  have hraw := congrArg ULift.down hy
  have hleft := congrArg
    (fun q : Over.mk (geometricPoint x.val) ⟶ (Scheme.Etale.forget T).obj U => q.left) hraw
  change y.down.left ≫ (k.left ≫ (f i).left) = l at hleft
  exact (Category.assoc _ _ _).trans hleft

end AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed
