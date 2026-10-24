/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.Finiteness

/-!
# `Gr(E, k)` is locally the Grassmannian of `O^n`

If a presheaf `P` is represented by `Y` and `F ⊣ G`, then `F.op ⋙ P` is represented by
`G.obj Y` (`Functor.RepresentableBy.ofAdjunction`, the generalization of Mathlib's
`Adjunction.representableBy`). With Mathlib's adjunction
`Over.mapPullbackAdj j : Over.map j ⊣ Over.pullback j`, the restriction along `Over.map j` of a
presheaf on `Over S` represented by `G` is represented by the pullback `G ×_S U`. Hence, over a
trivializing chart `j : Spec R ⟶ S` of `E` the restriction
`Gr(E, k) ×_S Spec R` is F8's Grassmannian `schemeOver R k n`
(`grassmannianBundlePullbackIso`, both represent `Quot_k(O^n)`), and the structure morphism
`Gr(E, k) ⟶ S` is quasi-compact and locally of finite type
(`quasiCompact_grassmannianBundle_hom`, `locallyOfFiniteType_grassmannianBundle_hom`: both
properties are local on the target, and F8's `Finiteness` gives them for `schemeOver R k n`).

Sources: Nitsure, arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6 (`Grass(E, d)` is locally
`Grass(r, d)`); Stacks, Tag 089U (Definition 27.22.2, base change `G(n − k, n)_R` of Stacks'
`G(n − k, n)`) and Tag 089T (proof: finitely many affine charts of finite type). Premise:
`BaseChangeMkQFormula`, supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory Opposite Limits

namespace CategoryTheory.Functor.RepresentableBy

/-- If `P` is represented by `Y` and `F ⊣ G`, then `F.op ⋙ P` is represented by `G.obj Y`; for
`P = yoneda.obj Y` this is Mathlib's `Adjunction.representableBy`. -/
def ofAdjunction {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    {P : Dᵒᵖ ⥤ Type v} {Y : D} (R : P.RepresentableBy Y) (adj : F ⊣ G) :
    (F.op ⋙ P).RepresentableBy (G.obj Y) where
  homEquiv {X} := (adj.homEquiv X Y).symm.trans R.homEquiv
  homEquiv_comp {X X'} f g := by
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm, R.homEquiv_comp]
    rfl

end CategoryTheory.Functor.RepresentableBy

namespace AlgebraicGeometry.Grassmannian

variable {S : Scheme.{u}}

variable (E : S.Modules) (k n : ℕ)
variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **`Gr(E, k)` is locally the Grassmannian of `O^n`**: over a trivializing chart
`j : Spec R ⟶ S` of `E`, `Gr(E, k) ×_S Spec R ≅ schemeOver R k n` over `Spec R`. -/
def grassmannianBundlePullbackIso (h : Scheme.Modules.SheafHasRank E n)
    (c : TrivializingChart E n) :
    (Over.pullback c.j).obj (grassmannianBundle E k n h) ≅ schemeOver c.R k n :=
  ((grassmannianBundleRepresentableBy E k n h).ofAdjunction
    (Over.mapPullbackAdj c.j)).uniqueUpToIso (c.representableBy k)

/-- A property of morphisms that is local on the target and holds for the Grassmannians
`schemeOver R k n ⟶ Spec R` holds for `Gr(E, k) ⟶ S`. -/
theorem grassmannianBundle_hom_of_isZariskiLocalAtTarget {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] (hP : ∀ R : CommRingCat.{u}, P (schemeOver R k n).hom)
    (h : Scheme.Modules.SheafHasRank E n) : P (grassmannianBundle E k n h).hom := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P)
    (Scheme.Cover.mkOfCovers S (fun x ↦ Spec (TrivializingChart.chartAt h x).R)
      (fun x ↦ (TrivializingChart.chartAt h x).j) (fun x ↦ by
        obtain ⟨y, hy⟩ := TrivializingChart.mem_range_chartAt h x
        exact ⟨x, y, hy⟩) (fun _ ↦ inferInstance)) fun x ↦ ?_
  let c := TrivializingChart.chartAt h x
  let e := grassmannianBundlePullbackIso E k n h c
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have he : e.hom.left ≫ (schemeOver c.R k n).hom =
      ((Over.pullback c.j).obj (grassmannianBundle E k n h)).hom :=
    Over.w e.hom
  change P ((Over.pullback c.j).obj (grassmannianBundle E k n h)).hom
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso P e.hom.left _).mpr (hP c.R)

/-- `Gr(E, k) ⟶ S` is quasi-compact. -/
theorem quasiCompact_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    QuasiCompact (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @QuasiCompact)
    (fun _ ↦ inferInstance) h

/-- `Gr(E, k) ⟶ S` is locally of finite type. -/
theorem locallyOfFiniteType_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    LocallyOfFiniteType (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @LocallyOfFiniteType)
    (fun _ ↦ inferInstance) h

end AlgebraicGeometry.Grassmannian
