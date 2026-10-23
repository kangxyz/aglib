/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleNaturality
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageUnitComposition

/-! # Original inverse-image units as relative sections -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

private theorem unit_diagonal_identity {C : Type*} [Category C]
    {A B D E H : C} (u : A ⟶ B) (m : B ⟶ D) (e : D ⟶ H)
    (e₀ : B ⟶ E) (v : E ⟶ H) (s : H ⟶ A) (r : A ⟶ E)
    (hn : m ≫ e = e₀ ≫ v) (hu : u ≫ e₀ = r) (ht : r ≫ v ≫ s = 𝟙 A) :
    (u ≫ m) ≫ (e ≫ s) = 𝟙 A := by
  rw [Category.assoc, ← Category.assoc m, hn]
  simp only [Category.assoc]
  rw [← Category.assoc u, hu, ht]

private theorem map_op_identity_triangle {C D : Type*} [Category C] [Category D]
    (P : Cᵒᵖ ⥤ D) {A B E : C} (s : A ⟶ B) (v : B ⟶ E) (r : E ⟶ A)
    (h : s ≫ v ≫ r = 𝟙 A) :
    P.map r.op ≫ P.map v.op ≫ P.map s.op = 𝟙 _ := by
  have hm : P.map r.op ≫ P.map v.op ≫ P.map s.op = P.map (𝟙 (op A)) := by
    simpa only [op_comp, Functor.map_comp, op_id, Category.assoc] using
      congrArg (fun a => P.map a.op) h
  exact hm.trans (P.map_id (op A))

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- The diagonal test morphism at an original étale chart. -/
def chartDiagonal {X : Scheme.{u}} (U : X.Etale) :
    etaleTerminal U.left ⟶ (siteBaseChange U.hom).obj U :=
  MorphismProperty.Over.homMk (pullback.diagonal U.hom)
    (by
      change pullback.diagonal U.hom ≫ pullback.snd U.hom U.hom = 𝟙 U.left
      exact pullback.diagonal_snd U.hom) (by trivial)

/-- The original site counit returns the original chart after its diagonal. -/
theorem chartDiagonal_counit {X : Scheme.{u}} (U : X.Etale) :
    (siteEtalePostcomposeTerminalIso U).inv ≫
        (siteEtalePostcompose U.hom).map (chartDiagonal U) ≫
        (siteEtalePostcomposeAdj U.hom).counit.app U = 𝟙 U := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 U.left ≫ pullback.diagonal U.hom ≫ pullback.fst U.hom U.hom = 𝟙 U.left
  exact (Category.id_comp _).trans (pullback.diagonal_fst U.hom)

/-- The inverse chart-evaluation isomorphism is the original unit at that chart,
restricted along its diagonal. This is an equality of actual section maps. -/
theorem pullbackSectionsEtaleEvaluationIso_inv {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    (pullbackSectionsEtaleEvaluationIso F U).inv =
      ((inverseImageAdjunction U.hom).unit.app F).hom.app (op U) ≫
        ((inverseImage U.hom).obj F).obj.map (chartDiagonal U).op := by
  let e := (inverseImageEtaleIso U.hom).hom.app F
  have hn := e.hom.naturality (chartDiagonal U).op
  have hu := inverseImageEtaleIso_unit_app U.hom F U
  have ht := map_op_identity_triangle F.obj (siteEtalePostcomposeTerminalIso U).inv
    ((siteEtalePostcompose U.hom).map (chartDiagonal U))
    ((siteEtalePostcomposeAdj U.hom).counit.app U) (chartDiagonal_counit U)
  have hp := unit_diagonal_identity
    (((inverseImageAdjunction U.hom).unit.app F).hom.app (op U))
    (((inverseImage U.hom).obj F).obj.map (chartDiagonal U).op)
    (e.hom.app (op (etaleTerminal U.left)))
    (e.hom.app (op ((siteBaseChange U.hom).obj U)))
    (F.obj.map ((siteEtalePostcompose U.hom).map (chartDiagonal U)).op)
    (F.obj.map (siteEtalePostcomposeTerminalIso U).inv.op)
    (F.obj.map ((siteEtalePostcomposeAdj U.hom).counit.app U).op) hn hu ht
  apply (cancel_mono (pullbackSectionsEtaleEvaluationIso F U).hom).1
  exact (pullbackSectionsEtaleEvaluationIso F U).inv_hom_id.trans hp.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
