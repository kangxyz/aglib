/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Original open restrictions of small-etale tests

The open chart and its arrow are native small-etale objects. Base change
retains the actual first-projection square, and local functions are pulled
back by the original appLE map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Etale

universe u

variable {X : Scheme.{u}} (U : X.Etale) (W : U.left.Opens)

/-- The actual open subscheme of an etale test, regarded as a test over the original base. -/
def openChart : X.Etale := Etale.mk (W.ι ≫ U.hom)

/-- The original open immersion as a morphism of small-etale tests. -/
def openChartHom : openChart U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl

/-- Original local functions pulled to global functions of the open chart. -/
def openChartSections : Γ(U.left, W) ⟶ Γ((openChart U W).left, ⊤) :=
  W.ι.appLE W ⊤ (fun x _ => x.property)

variable {S : Scheme.{u}} (j : S ⟶ X)

/-- The actual geometric base-change map of the open-chart arrow. -/
def openChartBaseChangeMap : pullback (W.ι ≫ U.hom) j ⟶ pullback U.hom j :=
  pullback.lift (pullback.fst (W.ι ≫ U.hom) j ≫ W.ι)
    (pullback.snd (W.ι ≫ U.hom) j)
    ((Category.assoc _ _ _).trans (pullback.condition (f := W.ι ≫ U.hom) (g := j)))

/-- Base change retains the original first-projection/open-immersion square. -/
@[reassoc]
theorem openChartBaseChangeMap_fst :
    openChartBaseChangeMap U W j ≫ pullback.fst U.hom j =
      pullback.fst (W.ι ≫ U.hom) j ≫ W.ι :=
  pullback.lift_fst _ _ _

/-- The first projection of every base-changed open-chart point lies in the original open. -/
theorem openChartBaseChangeMap_mem (q : (pullback (W.ι ≫ U.hom) j : Scheme.{u})) :
    (pullback.fst U.hom j) (openChartBaseChangeMap U W j q) ∈ W := by
  have h := congrArg (fun f : pullback (W.ι ≫ U.hom) j ⟶ U.left => f q)
    (openChartBaseChangeMap_fst U W j)
  exact h.symm ▸ (pullback.fst (W.ι ≫ U.hom) j q).property

private theorem appLE_of_eq {Q T : Scheme.{u}} (f g : Q ⟶ T) (h : f = g)
    (V : T.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) :
    f.appLE V ⊤ hf = g.appLE V ⊤ hg := by
  subst g
  rfl

private theorem appLE_top {Q T : Scheme.{u}} (f : Q ⟶ T) :
    f.appLE ⊤ ⊤ le_rfl = f.appTop := by
  change f.appTop ≫ Q.presheaf.map (𝟙 (Opposite.op ⊤)) = f.appTop
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Local functions have the same literal pullback before and after open-chart base change. -/
theorem openChartBaseChangeMap_appLE :
    (openChartBaseChangeMap U W j ≫ pullback.fst U.hom j).appLE W ⊤
      (fun q _ => openChartBaseChangeMap_mem U W j q) =
      openChartSections U W ≫ (pullback.fst (W.ι ≫ U.hom) j).appTop := by
  have h := Hom.appLE_comp_appLE (pullback.fst (W.ι ≫ U.hom) j) W.ι
    W ⊤ ⊤ (fun x _ => x.property) le_rfl
  have h' := appLE_of_eq _ _ (openChartBaseChangeMap_fst U W j) W
    (fun q _ => openChartBaseChangeMap_mem U W j q)
    (fun q _ => (pullback.fst (W.ι ≫ U.hom) j q).property)
  exact h'.trans (h.symm.trans
    (congrArg (fun k => W.ι.appLE W ⊤ (fun x _ => x.property) ≫ k)
      (appLE_top (pullback.fst (W.ι ≫ U.hom) j))))

end AlgebraicGeometry.Scheme.Etale
