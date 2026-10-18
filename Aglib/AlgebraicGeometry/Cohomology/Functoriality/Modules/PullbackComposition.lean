/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Open
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors

/-!
# Geometric module pullback on cohomology along composites and equal morphisms

For `p : Y ⟶ X`, `q : Z ⟶ Y` and `M : X.Modules`, pulling a cohomology class back along `p`
and then along `q` is pulling it back along `q ≫ p`, followed by the coefficient comparison
`(q ≫ p)^* M ⟶ q^* p^* M` of Mathlib's `Scheme.Modules.pullbackComp`
(`moduleCohomologyPullback_comp_apply`). For equal morphisms the two pullbacks differ by
`Scheme.Modules.pullbackCongr` (`moduleCohomologyPullback_congr_apply`). For a commutative square
`g ≫ pK = p' ≫ p`, the two iterated pullbacks agree up to the coefficient comparison
`pullbackSquareCoefficientIso : g^* pK^* M ≅ p'^* p^* M`
(`moduleCohomologyPullback_pullbackSquare_apply`); in the `moduleCohomologyMapAlong` form, with
the coefficient arrow `pullbackSquareCoefficientArrow` (an isomorphism when `g` is), this is
`moduleCohomologyMapAlong_pullbackSquareCoefficientArrow`. These statements are made at variable
morphisms, so that instances at concrete fibre products only substitute.

The coefficient identity behind the first statement is that the unit of the composite
adjunction `p^* ⋙ q^* ⊣ q_* ⋙ p_*`, followed by the direct-image comparison, is the unit along
`q ≫ p` followed by `pullbackComp` (`pullbackPushforwardAdjunction_unit_comp`). It is the unit
form of Mathlib's `Scheme.Modules.conjugateEquiv_pullbackComp_inv`, through
`CategoryTheory.unit_conjugateEquiv`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}}

/-- The unit of the composite pullback–pushforward adjunction, followed by the direct-image
composition comparison, is the unit along the composite followed by `pullbackComp`. -/
theorem pullbackPushforwardAdjunction_unit_comp (p : Y ⟶ X) (q : Z ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
            ((Scheme.Modules.pullback p).obj M)) ≫
        (Scheme.Modules.pushforwardComp q p).hom.app
          ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ p)).unit.app M ≫
        (Scheme.Modules.pushforward (q ≫ p)).map
          ((Scheme.Modules.pullbackComp q p).inv.app M) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.pullbackPushforwardAdjunction q))
    (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ p))
    (Scheme.Modules.pullbackComp q p).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  rw [← Category.assoc]
  exact h

/-- **Pullback along a composite**: `q^* (p^* x) = (pullbackComp q p).inv ((q ≫ p)^* x)` on the
original module cohomology. -/
theorem moduleCohomologyPullback_comp_apply (p : Y ⟶ X) (q : Z ⟶ Y) (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyPullback q ((Scheme.Modules.pullback p).obj M) n
        (moduleCohomologyPullback p M n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
        ((Scheme.Modules.pullbackComp q p).inv.app M)) n
        (moduleCohomologyPullback (q ≫ p) M n x) := by
  unfold moduleCohomologyPullback
  rw [moduleCohomologyMapAlong_comp, pullbackPushforwardAdjunction_unit_comp,
    moduleCohomologyMapAlong_postcomp]

/-- **Pullback along equal morphisms**: for `h : r₁ = r₂`, the pullback along `r₂` is the
pullback along `r₁` followed by `pullbackCongr h`. -/
theorem moduleCohomologyPullback_congr_apply {r₁ r₂ : Y ⟶ X} (h : r₁ = r₂) (M : X.Modules)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyPullback r₂ M n x =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((Scheme.Modules.pullbackCongr h).hom.app M)) n
        (moduleCohomologyPullback r₁ M n x) := by
  subst h
  have he : (Scheme.Modules.pullbackCongr (rfl : r₁ = r₁)).hom.app M = 𝟙 _ := rfl
  rw [he]
  erw [CategoryTheory.Functor.map_id]
  exact (Sheaf.H.map_id_apply _).symm

/-- Functoriality of `Sheaf.H.map` on module morphisms, in applied form. -/
theorem sheafH_map_toSheaf_comp_apply {M N P : Y.Modules} (a : M ⟶ N) (b : N ⟶ P) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map b) n
        (Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map (a ≫ b)) n x := by
  rw [← Sheaf.H.map_comp_apply]
  erw [← CategoryTheory.Functor.map_comp]

/-- Two composites of module morphisms that agree induce the same iterated map on
cohomology. -/
theorem sheafH_map_toSheaf_comp_apply_eq {M N N' P : Y.Modules} {a : M ⟶ N} {b : N ⟶ P}
    {a' : M ⟶ N'} {b' : N' ⟶ P} (h : a ≫ b = a' ≫ b') (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map b) n
        (Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map b') n
        (Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map a') n x) := by
  rw [sheafH_map_toSheaf_comp_apply, sheafH_map_toSheaf_comp_apply]
  erw [h]
  rfl

section Square

variable {W : Scheme.{u}} {p : Y ⟶ X} {p' : Z ⟶ Y} {pK : W ⟶ X} {g : Z ⟶ W}

/-- For a commutative square `g ≫ pK = p' ≫ p`, the coefficient comparison
`g^* pK^* M ≅ p'^* p^* M`, through `(g ≫ pK)^* M = (p' ≫ p)^* M`. -/
def pullbackSquareCoefficientIso (hg : g ≫ pK = p' ≫ p) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback pK).obj M) ≅
      (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackComp g pK).app M ≪≫ (Scheme.Modules.pullbackCongr hg).app M ≪≫
    ((Scheme.Modules.pullbackComp p' p).app M).symm

/-- The comparison `pullbackSquareCoefficientIso` after the composite comparison of `g ≫ pK`. -/
theorem pullbackComp_inv_app_pullbackSquareCoefficientIso_hom (hg : g ≫ pK = p' ≫ p)
    (M : X.Modules) :
    (Scheme.Modules.pullbackComp g pK).inv.app M ≫ (pullbackSquareCoefficientIso hg M).hom =
      (Scheme.Modules.pullbackCongr hg).hom.app M ≫
        (Scheme.Modules.pullbackComp p' p).inv.app M :=
  Iso.inv_hom_id_app_assoc _ _ _

/-- **Pullback through the two sides of a commutative square**: for `g ≫ pK = p' ≫ p`,
`p'^* (p^* x) = c (g^* (pK^* x))` with `c = pullbackSquareCoefficientIso`. -/
theorem moduleCohomologyPullback_pullbackSquare_apply (hg : g ≫ pK = p' ≫ p) (M : X.Modules)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyPullback p' ((Scheme.Modules.pullback p).obj M) n
        (moduleCohomologyPullback p M n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
          (pullbackSquareCoefficientIso hg M).hom) n
        (moduleCohomologyPullback g ((Scheme.Modules.pullback pK).obj M) n
          (moduleCohomologyPullback pK M n x)) := by
  rw [moduleCohomologyPullback_comp_apply p p' M n x,
    moduleCohomologyPullback_comp_apply pK g M n x, moduleCohomologyPullback_congr_apply hg M n x]
  exact sheafH_map_toSheaf_comp_apply_eq
    (pullbackComp_inv_app_pullbackSquareCoefficientIso_hom hg M).symm n _

/-- The coefficient arrow along `g` for a commutative square `g ≫ pK = p' ≫ p`: the pullback
unit of `g` followed by `pullbackSquareCoefficientIso`. A regular definition, so that the kernel
compares it through its arguments. -/
def pullbackSquareCoefficientArrow (hg : g ≫ pK = p' ≫ p) (M : X.Modules) :
    (Scheme.Modules.pullback pK).obj M ⟶ (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback p).obj M)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _ ≫
    (Scheme.Modules.pushforward g).map (pullbackSquareCoefficientIso hg M).hom

instance [IsIso g] (hg : g ≫ pK = p' ≫ p) (M : X.Modules) :
    IsIso (pullbackSquareCoefficientArrow hg M) := by
  let : (Scheme.Modules.pullback g).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso g
  unfold pullbackSquareCoefficientArrow
  infer_instance

/-- The geometric map along `g` with the coefficient arrow `pullbackSquareCoefficientArrow` turns
the pullback along `pK` into the iterated pullback along `p` and `p'`, in every degree. -/
theorem moduleCohomologyMapAlong_pullbackSquareCoefficientArrow (hg : g ≫ pK = p' ≫ p)
    (M : X.Modules) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong g (pullbackSquareCoefficientArrow hg M) n
        (moduleCohomologyPullback pK M n x) =
      moduleCohomologyPullback p' ((Scheme.Modules.pullback p).obj M) n
        (moduleCohomologyPullback p M n x) := by
  rw [pullbackSquareCoefficientArrow, moduleCohomologyMapAlong_postcomp]
  exact (moduleCohomologyPullback_pullbackSquare_apply hg M n x).symm

end Square

end AlgebraicGeometry.Scheme.Cohomology
