/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Separation of original relative sections by an etale covering family -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The original global-section pullbacks to a covering family jointly detect
section equality. No replacement of either coefficient sheaf is made. -/
theorem globalSections_eq_of_etale_cover {Y : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} Y) {J : Type v} (W : J → Y.Etale)
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal Y).from (W j)) ∈
      Y.smallEtaleTopology (etaleTerminal Y))
    (s t : (globalSections Y).obj F)
    (h : ∀ j, globalSectionsPullback (W j).hom F s =
      globalSectionsPullback (W j).hom F t) : s = t := by
  have hlocal (j : J) :
      F.obj.map ((etaleTerminalIsTerminal Y).from (W j)).op s =
        F.obj.map ((etaleTerminalIsTerminal Y).from (W j)).op t := by
    have hs := ConcreteCategory.congr_hom (globalSectionsPullback_etaleEvaluation F (W j)) s
    have ht := ConcreteCategory.congr_hom (globalSectionsPullback_etaleEvaluation F (W j)) t
    exact hs.symm.trans
      ((congrArg (pullbackSectionsEtaleEvaluationIso F (W j)).hom (h j)).trans ht)
  apply F.isSeparated (etaleTerminal Y) _ hcover s t
  intro V f hf
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
  exact (ConcreteCategory.congr_hom
    (F.obj.map_comp ((etaleTerminalIsTerminal Y).from (W j)).op a.op) s).trans
    ((congrArg (F.obj.map a.op) (hlocal j)).trans
      (ConcreteCategory.congr_hom
        (F.obj.map_comp ((etaleTerminalIsTerminal Y).from (W j)).op a.op) t).symm)

/-- Actual relative section maps along an etale cover jointly detect equality.
The coefficient comparison is the native commuting-triangle isomorphism. -/
theorem pullbackSections_eq_of_etale_cover {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Y.Etale)
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal Y).from (W j)) ∈
      Y.smallEtaleTopology (etaleTerminal Y))
    (s t : (globalSections Y).obj ((inverseImage f).obj F))
    (h : ∀ j, pullbackSectionsMap F
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) s =
      pullbackSectionsMap F
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) t) :
    s = t := by
  apply globalSections_eq_of_etale_cover ((inverseImage f).obj F) W hcover s t
  intro j
  let a : Over.mk ((W j).hom ≫ f) ⟶ Over.mk f := Over.homMk (W j).hom
  let e := (globalSections (W j).left).mapIso
    ((pullbackTriangleIso ((W j).hom ≫ f) f (W j).hom (Over.w a)).symm.app F)
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  exact h j

end AlgebraicGeometry.Scheme.EtaleAffineBasis
