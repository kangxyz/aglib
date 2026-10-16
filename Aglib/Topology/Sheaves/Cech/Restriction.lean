/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Cech restriction on actual topological opens

Intersection with a fixed open defines the original presheaf restriction and
opens-below adjunction. Restriction to a selected family member makes the
actual Cech complex exact in positive degrees. The final comparison identifies
the original Cech cosimplicial object when every member lies in the fixed open.
These are presheaf statements; no sheaf condition is assumed.

Existing implementation split from
`Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness` and `.Comparison`
at source revision `451aeda6b8bb5b44402b574dd6cf60f912360f8c`.
The original declaration contexts, maps and proof bodies are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

open TopologicalSpace
namespace CategoryTheory.Cech

/-- Intersecting actual opens with a fixed open. -/
def intersectFunctor {X : TopCat.{u}} (W : Opens X) : Opens X ⥤ Opens X where
  obj U := U ⊓ W
  map h := homOfLE (inf_le_inf (leOfHom h) le_rfl)

/-- The actual inclusion of each intersection into its original open. -/
def intersectToId {X : TopCat.{u}} (W : Opens X) : intersectFunctor W ⟶ 𝟭 (Opens X) where
  app _ := homOfLE inf_le_left

/-- Restriction of a presheaf's actual sections to intersections with `W`. -/
def restrictPresheaf {X : TopCat.{u}} {A : Type*} [Category A]
    (P : (Opens X)ᵒᵖ ⥤ A) (W : Opens X) :
    P ⟶ (intersectFunctor W).op ⋙ P where
  app U := P.map (homOfLE (inf_le_left : U.unop ⊓ W ≤ U.unop)).op
  naturality U V h := by
    dsimp
    rw [← P.map_comp, ← P.map_comp]
    rfl

end CategoryTheory.Cech

open TopologicalSpace
namespace CategoryTheory.Cech

variable {X : TopCat.{u}} (W : Opens X)

theorem intersectionGaloisConnection : GaloisConnection
    (fun U : Set.Iic W => U.val) (fun U : Opens X => (⟨U ⊓ W, by exact (inf_le_right : U ⊓ W ≤ W)⟩ :
      Set.Iic W)) :=
  fun U V => ⟨fun h => le_inf h U.property, fun h => (show U.val ≤ V ⊓ W from h).trans inf_le_left⟩

/-- The functor sending an open `U` to `U ⊓ W`, viewed as an open below `W`. -/
abbrev intersectToIic : Opens X ⥤ Set.Iic W :=
  (intersectionGaloisConnection W).monotone_u.functor

/-- The inclusion of opens below `W` into all opens of `X`. -/
abbrev iicInclusion : Set.Iic W ⥤ Opens X :=
  (intersectionGaloisConnection W).monotone_l.functor

instance : (intersectToIic W).IsRightAdjoint :=
  (intersectionGaloisConnection W).adjunction.isRightAdjoint

/-- The Cech complex of sections restricted to one member of the cover
is exact in every positive degree. This statement concerns the original
Cech functor and actual intersection restrictions, with arbitrary coefficients. -/
lemma restrictedCech_exactAt_succ {A : Type u'} [Category.{v'} A]
    [Abelian A] [HasProducts.{w} A] {ι : Type w}
    (V : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ A) (i₀ : ι) (n : ℕ) :
    ((cechComplexFunctor V).obj ((intersectFunctor (V i₀)).op ⋙ P)).ExactAt (n + 1) := by
  let F := intersectToIic (V i₀)
  let Q := (iicInclusion (V i₀)).op ⋙ P
  have h := cechComplex_exactAt_succ_of_terminal_component (hT := isTerminalTop)
    Q (fun i => F.obj (V i)) (i₀ := i₀) (homOfLE (by
      change V i₀ ≤ V i₀ ⊓ V i₀
      exact le_inf le_rfl le_rfl)) n
  exact h.of_iso ((AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (cechCosimplicialChangeIso F V Q)).symm

end CategoryTheory.Cech

namespace CategoryTheory.Cech

variable {X : TopCat.{u}} {A : Type u'} [Category.{v} A] [HasProducts.{w} A]

/-- The comparison between the Cech cosimplicial object of `P` and that of its intersection
restriction to `W`, when every member of `U` lies in `W`. -/
def cechCosimplicialIntersectIso {ι : Type w} (U : ι → Opens X)
    (P : (Opens X)ᵒᵖ ⥤ A) (W : Opens X) (hU : ∀ i, U i ≤ W) :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((intersectFunctor W).op ⋙ P) := by
  have hprod (n : ℕ) (a : Fin (n + 1) → ι) : (∏ᶜ fun i => U (a i)) ⊓ W =
      (∏ᶜ fun i => U (a i)) :=
    inf_eq_left.mpr ((leOfHom (Limits.Pi.π _ 0)).trans (hU (a 0)))
  refine NatIso.ofComponents (fun n => Limits.Pi.mapIso fun a =>
    P.mapIso (eqToIso (hprod n.len a)).op) ?_
  intro n m g
  apply Limits.Pi.hom_ext
  intro a
  simp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    FormalCoproduct.cech, FormalCoproduct.mapPower, ← Functor.map_comp]
  congr 2

end CategoryTheory.Cech
