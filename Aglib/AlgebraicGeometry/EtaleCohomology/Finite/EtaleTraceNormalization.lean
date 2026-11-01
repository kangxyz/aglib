/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleRepresentedTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Gluing
public import Aglib.CategoryTheory.Sites.Free.FiniteSumTransfer
public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.LocalFormula

/-!
# Local normalization of the original finite étale trace

The original free-representable arrow is glued with its full local sum data.
It is then an argument to the existing `etaleRepresentedTrace` construction.
No rank-only existential witness is identified with this normalized arrow.
The whole local equation uses the actual product graphs and also holds on
empty charts, by the original étale covering criterion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

attribute [local instance] Fintype.ofFinite

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- Glue the original represented sums with their local equations on every
splitting chart. No nonemptiness condition is imposed on a chart. -/
theorem exists_freeRepresentable_transfer_local (d : ℕ)
    (hd : ∀ x : X, Y.obj.hom.finrank x = d) :
    ∃ a : freeAbelianSheaf.{u + 1} X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) ⟶
        freeAbelianSheaf.{u + 1} X.smallEtaleTopology ((toEtale X).obj Y),
      (∀ (V : X.Etale) (A : FintypeCat.{u})
        (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y),
        (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
            ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
              V) ≫ a =
          ∑ b : A, (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
            (chartSiteSection Y e b)) ∧
      a ≫ (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
        ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
          ((toEtale X).obj Y)) = d • 𝟙 _ := by
  classical
  let J := X.smallEtaleTopology
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X
  let U := (toEtale X).obj Y
  let F := freeAbelianSheaf.{u + 1} J U
  let K := Σ V : X.Etale, Σ A : FintypeCat.{u},
    ((trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) × V.left
  let V : K → X.Etale := fun i => i.1
  let A : K → FintypeCat.{u} := fun i => i.2.1
  let e (i : K) : (trivialCoverFunctor (V i).left).obj (A i) ≅
      (baseChange (V i).hom).obj Y := i.2.2.1
  let p (i : K) : V i ⟶ T := hT.from (V i)
  have hp : Sieve.ofArrows V p ∈ J T := by
    apply SheafDescent.etaleFamily_covering V p
    intro x
    obtain ⟨V₀, A₀, e₀, v, hv⟩ := exists_labelled_chart Y x
    let i : K := ⟨V₀, A₀, e₀, v⟩
    refine ⟨i, v, ?_⟩
    have hw := MorphismProperty.Over.w (p i)
    change (p i).left ≫ 𝟙 X = V₀.hom at hw
    have hw' : (p i).left = V₀.hom := (Category.comp_id (p i).left).symm.trans hw
    exact (congrArg (fun k : V₀.left ⟶ X => k v) hw').trans hv
  obtain ⟨a, ha, hrank⟩ :=
    exists_freeRepresentable_transfer_of_cover.{u + 1, u, u + 1, u + 1, u} J hT V p hp
    (fun i => A i) (fun i => chartSiteSection Y (e i))
    (fun i j W f g _ => by
      change F.obj.map f.op (chartSum Y (e i)) = F.obj.map g.op (chartSum Y (e j))
      rw [chartSum_restrict, chartSum_restrict]
      exact chartSum_independent Y _ _)
    d (fun i => (chartSplitting_card Y (e i) i.2.2.2).trans (hd _))
  refine ⟨a, ?_, hrank⟩
  intro V₀ A₀ e₀
  apply (sectionsAddEquiv.{u + 1} J V₀ F).injective
  have hcov : Sieve.ofArrows (fun _ : V₀.left => V₀) (fun _ => 𝟙 V₀) ∈ J V₀ :=
    SheafDescent.etaleFamily_covering _ _ (fun v => ⟨v, v, rfl⟩)
  apply section_eq_of_cover.{u + 1, u, u + 1, u}
    J (fun _ : V₀.left => V₀) (fun _ => 𝟙 V₀) hcov
  intro v
  have hv := ha (⟨V₀, A₀, e₀, v⟩ : K)
  change (freeAbelianSheafFunctor.{u + 1} J).map (hT.from V₀) ≫ a =
    ∑ b : A₀, (freeAbelianSheafFunctor.{u + 1} J).map (chartSiteSection Y e₀ b) at hv
  exact congrArg (F.obj.map (𝟙 V₀).op)
    (congrArg (sectionsAddEquiv.{u + 1} J V₀ F) hv)

/-- Original free arrows are determined by their restrictions on all finite
étale splitting charts. This includes an empty base. -/
theorem freeRepresentable_transfer_ext
    (a b : freeAbelianSheaf.{u + 1} X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) ⟶
      freeAbelianSheaf.{u + 1} X.smallEtaleTopology ((toEtale X).obj Y))
    (hlocal : ∀ (V : X.Etale) (A : FintypeCat.{u})
      (_e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y),
      (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
          ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
            V) ≫ a =
        (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
          ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
            V) ≫ b) : a = b := by
  classical
  let J := X.smallEtaleTopology
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X
  let F := freeAbelianSheaf.{u + 1} J ((toEtale X).obj Y)
  choose V A e v hv using exists_labelled_chart Y
  let p (x : X) : V x ⟶ T := hT.from (V x)
  have hp : Sieve.ofArrows V p ∈ J T := by
    apply SheafDescent.etaleFamily_covering V p
    intro x
    refine ⟨x, v x, ?_⟩
    have hw := MorphismProperty.Over.w (p x)
    change (p x).left ≫ 𝟙 X = (V x).hom at hw
    have hw' : (p x).left = (V x).hom := (Category.comp_id (p x).left).symm.trans hw
    exact (congrArg (fun k : (V x).left ⟶ X => k (v x)) hw').trans (hv x)
  apply (sectionsAddEquiv.{u + 1} J T F).injective
  apply section_eq_of_cover.{u + 1, u, u + 1, u} J V p hp
  intro x
  change F.obj.map (p x).op (sectionsEquiv.{u + 1} J T F a) =
    F.obj.map (p x).op (sectionsEquiv.{u + 1} J T F b)
  rw [← Sheaf.BasisAcyclicity.sectionsEquiv_precomp,
    ← Sheaf.BasisAcyclicity.sectionsEquiv_precomp]
  exact congrArg (sectionsEquiv.{u + 1} J (V x) F) (hlocal (V x) (A x) (e x))

/-- The locally normalized original free arrow supplied to the existing trace constructor. -/
def finiteEtaleFreeTransfer (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d) :
    freeAbelianSheaf.{u + 1} X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) ⟶
      freeAbelianSheaf.{u + 1} X.smallEtaleTopology ((toEtale X).obj Y) :=
  (exists_freeRepresentable_transfer_local Y d hd).choose

/-- Every splitting has the original finite sum as its full free-arrow restriction. -/
theorem finiteEtaleFreeTransfer_local (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d)
    (V : X.Etale) (A : FintypeCat.{u})
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) :
    (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
        ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from V) ≫
      finiteEtaleFreeTransfer Y d hd =
        ∑ b : A, (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
          (chartSiteSection Y e b) :=
  (exists_freeRepresentable_transfer_local Y d hd).choose_spec.1 V A e

/-- The same original free arrow has the actual constant finite-flat rank. -/
theorem finiteEtaleFreeTransfer_rank (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d) :
    finiteEtaleFreeTransfer Y d hd ≫
      (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
        ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
          ((toEtale X).obj Y)) = d • 𝟙 _ :=
  (exists_freeRepresentable_transfer_local Y d hd).choose_spec.2

/-- The local normalization determines the original free arrow independently
of the rank witness used in its construction. -/
theorem finiteEtaleFreeTransfer_eq (d e : ℕ)
    (hd : ∀ x : X, Y.obj.hom.finrank x = d) (he : ∀ x : X, Y.obj.hom.finrank x = e) :
    finiteEtaleFreeTransfer Y d hd = finiteEtaleFreeTransfer Y e he := by
  apply freeRepresentable_transfer_ext Y
  intro V A s
  rw [finiteEtaleFreeTransfer_local Y d hd V A s, finiteEtaleFreeTransfer_local Y e he V A s]

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

open CategoryTheory.MorphismProperty.Over

variable {X : Scheme.{u}}

local instance genericEtaleProductTest_continuous (V : X.Etale) :
    (productTest (@Etale : MorphismProperty Scheme.{u}) V).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology := by
  change (etaleProductTest V).IsContinuous X.smallEtaleTopology X.smallEtaleTopology
  infer_instance

/-- The existing native restriction trace is the same original three-factor
generic construction, as a whole coefficient-natural map. -/
theorem etaleRepresentedRestrictionTrace_eq_generic (U : X.Etale)
    (a : freeAbelianSheaf.{u + 1} X.smallEtaleTopology (etaleTerminal X) ⟶
      freeAbelianSheaf.{u + 1} X.smallEtaleTopology U) :
    etaleRepresentedRestrictionTrace U a =
      representedRestrictionTrace (@Etale : MorphismProperty Scheme.{u})
        X.smallEtaleTopology U a := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

/-- The existing native trace constructor retains the whole graph-sum equation. -/
theorem etaleRepresentedRestrictionTrace_local (U : X.Etale)
    (a : freeAbelianSheaf.{u + 1} X.smallEtaleTopology (etaleTerminal X) ⟶
      freeAbelianSheaf.{u + 1} X.smallEtaleTopology U)
    (V : X.Etale) {I : Type u} [Fintype I] (s : I → (V ⟶ U))
    (ha : (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map
        ((etaleTerminalIsTerminal X).from V) ≫ a =
      ∑ i, (freeAbelianSheafFunctor.{u + 1} X.smallEtaleTopology).map (s i)) :
    Functor.whiskerRight (etaleRepresentedRestrictionTrace U a)
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V)) ≫
      (Functor.leftUnitor
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V))).hom =
      ∑ i, (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (productGraph (@Etale : MorphismProperty Scheme.{u}) (s i)).op := by
  rw [etaleRepresentedRestrictionTrace_eq_generic]
  exact representedRestrictionTrace_local.{u + 1, u, u + 1, u}
    (@Etale : MorphismProperty Scheme.{u}) X.smallEtaleTopology U a V s ha

variable (Y : Scheme.FiniteEtale X) (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d)

/-- The original trace constructor applied to its locally normalized original free arrow. -/
def finiteEtaleSheafTrace :
    inverseImage Y.obj.hom ⋙ directImage Y.obj.hom ⟶ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  etaleRepresentedTrace ((Scheme.FiniteEtale.toEtale X).obj Y)
    (Scheme.FiniteEtale.finiteEtaleFreeTransfer Y d hd)

/-- The entire original inverse-image unit has composite equal to the actual rank. -/
theorem finiteEtaleSheafTrace_rank :
    (inverseImageAdjunction Y.obj.hom).unit ≫ finiteEtaleSheafTrace Y d hd = d • 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact etaleRepresentedTrace_rank ((Scheme.FiniteEtale.toEtale X).obj Y)
    (Scheme.FiniteEtale.finiteEtaleFreeTransfer Y d hd) d
    (Scheme.FiniteEtale.finiteEtaleFreeTransfer_rank Y d hd) F

/-- The entire original trace on each splitting chart is the original
inverse-image comparison followed by the sum of graph restrictions. -/
theorem finiteEtaleSheafTrace_local (V : X.Etale) (A : FintypeCat.{u})
    (e : (Scheme.FiniteEtale.trivialCoverFunctor V.left).obj A ≅
      (Scheme.FiniteEtale.baseChange V.hom).obj Y) :
    Functor.whiskerRight (finiteEtaleSheafTrace Y d hd)
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V)) ≫
      (Functor.leftUnitor
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V))).hom =
      Functor.whiskerRight
          (Functor.whiskerRight (inverseImageEtaleIso Y.obj.hom).hom (directImage Y.obj.hom))
          ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V)) ≫
        ∑ a : A, (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (productGraph (@Etale : MorphismProperty Scheme.{u})
            (Scheme.FiniteEtale.chartSiteSection Y e a)).op := by
  rw [finiteEtaleSheafTrace, etaleRepresentedTrace, Adjunction.traceThroughLeftAdjointUniq,
    Functor.whiskerRight_comp, Category.assoc,
    etaleRepresentedRestrictionTrace_local _ _ V (Scheme.FiniteEtale.chartSiteSection Y e)
      (Scheme.FiniteEtale.finiteEtaleFreeTransfer_local Y d hd V A e)]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
