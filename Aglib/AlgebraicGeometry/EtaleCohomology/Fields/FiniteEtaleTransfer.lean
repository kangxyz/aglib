/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverLocalTransition
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.LocalSplitting
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSectionDescent
public import Aglib.CategoryTheory.Sites.Hypercohomology.FiniteSumDescent
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal

/-! # Actual finite-etale free-generator sums

The local sum is made in the original free abelian sheaf. Changes of
trivialization are compared on open neighbourhoods by their actual geometric
fibre permutations, and equality descends by sheaf separatedness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

attribute [local instance] Fintype.ofFinite

variable {X : Scheme.{u}} {V U : X.Etale}
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    (Y : Scheme.FiniteEtale V.left) (q : Y.obj.left ⟶ U.left)
    (hq : q ≫ U.hom = Y.obj.hom ≫ V.hom)

/-- The actual site section attached to a label in a finite-etale trivialization. -/
def trivializationSiteSection {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ Y) (a : A) : V ⟶ U :=
  MorphismProperty.Over.homMk
    ((trivialCoverι V.left A a).hom.left ≫ e.hom.hom.left ≫ q) (by
      simp only [Category.assoc]
      rw [hq, ← Category.assoc e.hom.hom.left,
        Over.w e.hom.hom, ← Category.assoc]
      change ((trivialCoverι V.left A a).hom.left ≫
        (trivialCover V.left A).obj.hom) ≫ V.hom = V.hom
      exact (congrArg (fun g : V.left ⟶ V.left => g ≫ V.hom)
        (trivialCoverι_struct V.left A a)).trans (Category.id_comp V.hom))
    (by trivial)

/-- A local finite sum in the original free abelian sheaf, with value universe `u+1`. -/
def trivializationSum {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ Y) :
    (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U).obj.obj (op V) :=
  representedSum (Scheme.smallEtaleTopology X) (trivializationSiteSection Y q hq e)

omit [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- Equality after base change yields equality of the original section maps
restricted to the actual open subscheme. -/
theorem trivialCoverSection_eq_of_baseChange_eq {A : FintypeCat.{u}}
    {Z : Scheme.FiniteEtale V.left}
    (f g : (trivialCoverFunctor V.left).obj A ⟶ Z)
    (W : V.left.Opens) (h : (baseChange W.ι).map f = (baseChange W.ι).map g) (a : A) :
    W.ι ≫ (trivialCoverι V.left A a).hom.left ≫ f.hom.left =
      W.ι ≫ (trivialCoverι V.left A a).hom.left ≫ g.hom.left := by
  have hh := congrArg (fun k =>
    (trivialCoverBaseChangeSection W.ι A a).hom.left ≫ k.hom.left ≫
      pullback.fst Z.obj.hom W.ι) h
  change (trivialCoverBaseChangeSection W.ι A a).hom.left ≫
      pullback.lift (pullback.fst _ _ ≫ f.hom.left) (pullback.snd _ _) _ ≫
        pullback.fst _ _ =
    (trivialCoverBaseChangeSection W.ι A a).hom.left ≫
      pullback.lift (pullback.fst _ _ ≫ g.hom.left) (pullback.snd _ _) _ ≫
        pullback.fst _ _ at hh
  change pullback.lift (W.ι ≫ (trivialCoverι V.left A a).hom.left) (𝟙 _) _ ≫
      pullback.lift (pullback.fst _ _ ≫ f.hom.left) (pullback.snd _ _) _ ≫
        pullback.fst _ _ =
    pullback.lift (W.ι ≫ (trivialCoverι V.left A a).hom.left) (𝟙 _) _ ≫
      pullback.lift (pullback.fst _ _ ≫ g.hom.left) (pullback.snd _ _) _ ≫
        pullback.fst _ _ at hh
  simpa only [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc] using hh

omit [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- Two trivializations agree up to a permutation locally around each point,
when read as the actual site sections into the original target. -/
theorem exists_open_trivializationSiteSection_eq {A B : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ Y)
    (f : (trivialCoverFunctor V.left).obj B ≅ Y) (x : V.left) :
    ∃ (W : V.left.Opens), x ∈ W ∧ ∃ (r : A ≃ B),
      ∀ a, W.ι ≫ (trivializationSiteSection Y q hq e a).left =
        W.ι ≫ (trivializationSiteSection Y q hq f (r a)).left := by
  let s := algebraicClosureResiduePoint V.left x
  let d := e ≪≫ f.symm
  let r := trivialCoverTransitionLabels s d
  obtain ⟨W, hx, hW⟩ := exists_open_trivialCoverTransition s d
  have hx' : x ∈ W := by
    simpa only [s, algebraicClosureResiduePoint_image] using hx
  let r' : A ≃ B := Equiv.ofBijective r.hom (ConcreteCategory.bijective_of_isIso r.hom)
  refine ⟨W, hx', r', fun a => ?_⟩
  have ha := trivialCoverSection_eq_of_baseChange_eq
    d.hom ((trivialCoverFunctor V.left).map r.hom) W hW a
  have hb := congrArg (fun k => k ≫ f.hom.hom.left ≫ q) ha
  have hr := congrArg (fun k => k.hom.left)
    (trivialCoverι_map V.left r.hom a)
  change (trivialCoverι V.left A a).hom.left ≫
      ((trivialCoverFunctor V.left).map r.hom).hom.left =
    (trivialCoverι V.left B (r.hom a)).hom.left at hr
  have hf : f.inv.hom.left ≫ f.hom.hom.left = 𝟙 Y.obj.left :=
    congrArg (fun k : Y ⟶ Y => k.hom.left) f.inv_hom_id
  change (W.ι ≫ (trivialCoverι V.left A a).hom.left ≫
      (e.hom.hom.left ≫ f.inv.hom.left)) ≫ f.hom.hom.left ≫ q = _ at hb
  have hfq : f.inv.hom.left ≫ f.hom.hom.left ≫ q = q :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : Y.obj.left ⟶ Y.obj.left => k ≫ q) hf).trans (Category.id_comp q))
  simp only [Category.assoc, hfq] at hb
  have hc := congrArg (fun k : V.left ⟶ (trivialCover V.left B).obj.left =>
    W.ι ≫ k ≫ f.hom.hom.left ≫ q) hr
  change W.ι ≫ (trivialCoverι V.left A a).hom.left ≫ e.hom.hom.left ≫ q =
    W.ι ≫ (trivialCoverι V.left B (r.hom a)).hom.left ≫ f.hom.hom.left ≫ q
  exact hb.trans (by simpa only [Category.assoc] using hc)

/-- The original sum is independent of the chosen finite-etale trivialization.
The comparison uses a separate open neighbourhood and permutation at each
point, so disconnected overlaps are included. -/
theorem trivializationSum_independent {A B : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ Y)
    (f : (trivialCoverFunctor V.left).obj B ≅ Y) :
    trivializationSum Y q hq e = trivializationSum Y q hq f := by
  choose W hx r hr using exists_open_trivializationSiteSection_eq Y q hq e f
  let T (x : V.left) : X.Etale := Scheme.Etale.mk ((W x).ι ≫ V.hom)
  let p (x : V.left) : T x ⟶ V :=
    MorphismProperty.Over.homMk (W x).ι rfl (by trivial)
  apply representedSum_eq_of_locally_reindexed (Scheme.smallEtaleTopology X)
    (trivializationSiteSection Y q hq e) (trivializationSiteSection Y q hq f) T p
    (SheafDescent.etaleFamily_covering T p (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)) r
  intro x a
  apply MorphismProperty.Over.Hom.ext
  exact hr x a

end AlgebraicGeometry.Scheme.FiniteEtale
