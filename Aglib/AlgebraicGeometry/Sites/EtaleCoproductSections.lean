/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaSections

/-! # Original sections on coproducts of etale test objects

The base is fixed; the coefficient is an arbitrary original abelian sheaf on
that base, rather than a replacement sheaf on the coproduct.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Etale)

instance coproductStructure_etale : Etale (Sigma.desc (fun i => (U i).hom)) :=
  IsZariskiLocalAtSource.sigmaDesc (fun i => (U i).prop)

/-- The literal scheme coproduct, with its original structure map to the fixed base. -/
def coproductChart : X.Etale := by
  let : Etale (Sigma.desc (fun i => (U i).hom)) := coproductStructure_etale U
  exact Etale.mk (Sigma.desc (fun i => (U i).hom))

/-- Original component inclusions as morphisms of etale test objects. -/
def coproductChartInclusion (i : ι) : U i ⟶ coproductChart U :=
  MorphismProperty.Over.homMk (Sigma.ι (fun j => (U j).left) i) (by
    change Sigma.ι (fun j => (U j).left) i ≫ Sigma.desc (fun j => (U j).hom) = (U i).hom
    exact Sigma.ι_comp_desc _ _)

/-- The original component cocone. -/
def coproductChartCofan : Cofan U := Cofan.mk (coproductChart U) (coproductChartInclusion U)

instance coproductChartInclusion_mono (i : ι) : Mono (coproductChartInclusion U i) := by
  apply Functor.mono_of_mono_map (Etale.forget X ⋙ Over.forget X)
  exact inferInstanceAs (Mono (Sigma.ι (fun j => (U j).left) i))

theorem coproductChart_cover :
    Sieve.ofArrows U (coproductChartInclusion U) ∈
      X.smallEtaleTopology (coproductChart U) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨⟨i, y⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun j => (U j).left)).surjective x
  exact ⟨i, y, (AlgebraicGeometry.sigmaMk_mk (fun j => (U j).left) i y).symm⟩

theorem coproductChart_disjoint [HasInitial X.Etale] :
    Pairwise fun i j => IsPullback (initial.to _) (initial.to _)
      (coproductChartInclusion U i) (coproductChartInclusion U j) := by
  intro i j hij
  let F := Etale.forget X ⋙ Over.forget X
  let hI := initialChartUnderlying (⊥_ X.Etale) initialIsInitial
  apply IsPullback.of_map F (initialIsInitial.hom_ext _ _)
  have h := CoproductDisjoint.isPullback_of_isInitial
    (coproductIsCoproduct (fun j => (U j).left)) hI hij
  change IsPullback (initial.to (U i)).left (initial.to (U j)).left
    (Sigma.ι (fun j => (U j).left) i) (Sigma.ι (fun j => (U j).left) j)
  rw [hI.hom_ext (initial.to (U i)).left (hI.to (U i).left),
    hI.hom_ext (initial.to (U j)).left (hI.to (U j).left)]
  exact h

/-- Actual restrictions from the coproduct give a bijection on original sections. -/
theorem coproductSections_bijective [Small.{v} ι]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}) :
    Function.Bijective (fun x : F.obj.obj (op (coproductChart U)) =>
      fun i => F.obj.map (coproductChartInclusion U i).op x) := by
  let : HasInitial X.Etale := (emptyChartIsInitial X).hasInitial
  let : ∀ i, Mono ((coproductChartCofan U).inj i) :=
    fun i => inferInstanceAs (Mono (coproductChartInclusion U i))
  have hF : Presieve.IsSheaf X.smallEtaleTopology
      (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v}) := by
    apply (isSheaf_iff_isSheaf_of_type _ _).mp
    exact ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{v})).obj F).property
  exact Sheaf.LargeCohomology.disjointSections_bijective
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v}) (emptyChartIsInitial X)
    (hF.isSheafFor _ (by
      simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using
        emptyChart_empty_cover X))
    (coproductChartCofan U) (coproductChart_disjoint U)
    (hF.isSheafFor _ (coproductChart_cover U))

end AlgebraicGeometry.Scheme.Etale
