/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Glue
public import Aglib.AlgebraicGeometry.Descent.IdealSheaf.Pullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing ideal sheaves along a disjoint open cover

Let `f i : U i ⟶ X` be a jointly surjective family of open immersions with pairwise disjoint
images, for an index type `ι` in any universe. Ideal sheaves `I i` on the `U i` then glue to an
ideal sheaf on `X` with no compatibility condition:

* `Scheme.IdealSheafData.eq_of_isEmpty`: ideal sheaves on an empty scheme are equal;
* `Scheme.IdealSheafData.comap_fst_eq_comap_snd_of_pairwise_disjoint`: the gluing condition of
  `IdealSheafData.glue` (`IdealSheaf/Glue`) holds for any `I i`, since the overlap of `f i` with
  itself is diagonal (`f i` is a monomorphism) and the other overlaps are empty
  (`Scheme.isEmpty_pullback_iff`);
* `Scheme.IdealSheafData.glueOfDisjoint`, with `comap_glueOfDisjoint` (it restricts to `I i` on
  `U i`) and `eq_glueOfDisjoint_iff` (it is the only such ideal sheaf, by
  `IdealSheafData.ext_of_comap_eq`).

Present consumer: closed subschemes over a disjoint union of bases (`IdealSheaf/GlueCoproduct`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **Ideal sheaves on an empty scheme are equal.** -/
theorem eq_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (I J : X.IdealSheafData) : I = J :=
  ext_of_comap_eq (U := fun _ : Empty => X) (fun _ => 𝟙 X)
    ((Set.iUnion_of_empty _).trans (Set.univ_eq_empty_iff.mpr inferInstance).symm)
    (fun i => i.elim)

variable {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
  [∀ i, IsOpenImmersion (f i)]

/-- **Ideal sheaves on the members of a disjoint open cover agree on the overlaps**: if the images
of the `f i` are pairwise disjoint, any ideal sheaves `I i` on the `U i` satisfy the gluing
condition of `IdealSheafData.glue`. The overlap of `f i` with itself is diagonal (`f i` is a
monomorphism) and the other overlaps are empty. -/
theorem comap_fst_eq_comap_snd_of_pairwise_disjoint
    (hdisj : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))
    (I : ∀ i, (U i).IdealSheafData) (i j : ι) :
    (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [(cancel_mono (f i)).1 (pullback.condition (f := f i) (g := f i))]
  · have := Scheme.isEmpty_pullback_iff.mpr (hdisj hij)
    exact eq_of_isEmpty _ _

variable (hcov : ∀ x : X, ∃ i y, f i y = x)
  (hdisj : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))

/-- **Gluing ideal sheaves along a disjoint open cover**: ideal sheaves `I i` on the members
`f i : U i ⟶ X` of a jointly surjective family of open immersions with pairwise disjoint images
glue to an ideal sheaf on `X`, with no compatibility condition. -/
def glueOfDisjoint (I : ∀ i, (U i).IdealSheafData) : X.IdealSheafData :=
  glue f I hcov (comap_fst_eq_comap_snd_of_pairwise_disjoint f hdisj I)

/-- The glued ideal sheaf restricts to `I i` on `U i`. -/
@[simp]
theorem comap_glueOfDisjoint (I : ∀ i, (U i).IdealSheafData) (i : ι) :
    (glueOfDisjoint f hcov hdisj I).comap (f i) = I i :=
  comap_glue hcov _ i

/-- The glued ideal sheaf is the only ideal sheaf restricting to `I i` on every `U i`. -/
theorem eq_glueOfDisjoint_iff (I : ∀ i, (U i).IdealSheafData) (K : X.IdealSheafData) :
    K = glueOfDisjoint f hcov hdisj I ↔ ∀ i, K.comap (f i) = I i := by
  refine ⟨fun h i => by rw [h, comap_glueOfDisjoint], fun h => ext_of_comap_eq f ?_ fun i =>
    (h i).trans (comap_glueOfDisjoint f hcov hdisj I i).symm⟩
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩

end AlgebraicGeometry.Scheme.IdealSheafData
