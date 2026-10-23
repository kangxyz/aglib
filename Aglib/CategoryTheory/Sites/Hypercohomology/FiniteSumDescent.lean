/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverEffacement
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Finite sums of original free-representable generators

Finite sums commute with restriction. Equality may be checked after a covering
family with a different permutation on every chart. This is the separatedness
step in finite-etale transfer descent, not a global-permutation assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

universe c h t i j k

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]

/-- The actual free generator of the represented sheaf at a site morphism. -/
def representedGenerator {V U : C} (f : V ⟶ U) :
    (freeAbelianSheaf.{t} J U).obj.obj (op V) :=
  sectionsAddEquiv J V _ ((freeAbelianSheafFunctor J).map f)

@[simp] theorem representedGenerator_restrict {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    (freeAbelianSheaf.{t} J U).obj.map g.op (representedGenerator J f) =
      representedGenerator J (g ≫ f) := by
  symm
  exact (congrArg (sectionsAddEquiv J W _) (Functor.map_comp _ g f)).trans
    (BasisAcyclicity.sectionsEquiv_precomp J g _ ((freeAbelianSheafFunctor J).map f))

/-- The original finite sum of generators on a split chart. -/
def representedSum {V U : C} {I : Type i} [Fintype I] (f : I → (V ⟶ U)) :
    (freeAbelianSheaf.{t} J U).obj.obj (op V) := ∑ a, representedGenerator J (f a)

@[simp] theorem representedSum_restrict {W V U : C} {I : Type i} [Fintype I]
    (g : W ⟶ V) (f : I → (V ⟶ U)) :
    (freeAbelianSheaf.{t} J U).obj.map g.op (representedSum J f) =
      representedSum J (fun a => g ≫ f a) := by
  simp only [representedSum, map_sum, representedGenerator_restrict]

/-- Relabeling a finite family leaves its sum unchanged. -/
theorem representedSum_reindex {V U : C} {I : Type i} {I' : Type j}
    [Fintype I] [Fintype I'] (e : I ≃ I') (f : I → (V ⟶ U)) (g : I' → (V ⟶ U))
    (hfg : ∀ a, f a = g (e a)) : representedSum J f = representedSum J g :=
  Fintype.sum_equiv e _ _ (fun a => congrArg (representedGenerator J) (hfg a))

omit [HasSheafify J AddCommGrpCat.{max h t}] in
/-- Equality of sections can be tested on a covering family, without any
assumption that the base or the cover is connected. -/
theorem section_eq_of_cover {F : Sheaf J AddCommGrpCat.{max h t}} {V : C}
    {K : Type k} (W : K → C) (p : ∀ a, W a ⟶ V)
    (hp : Sieve.ofArrows W p ∈ J V) {a b : F.obj.obj (op V)}
    (hab : ∀ k, F.obj.map (p k).op a = F.obj.map (p k).op b) : a = b := by
  have hF := Presheaf.isSheaf_comp_of_isSheaf J F.obj
    (forget AddCommGrpCat.{max h t}) F.property
  have hh : (↾fun _ : PUnit => a) = (↾fun _ : PUnit => b) :=
    hF.hom_ext_ofArrows p hp (fun k => by ext z; exact hab k)
  exact congrArg (fun f => f PUnit.unit) hh

/-- The finite sum is unchanged by genuinely locally varying reindexing:
each covering chart can carry its own permutation. -/
theorem representedSum_eq_of_locally_reindexed {V U : C}
    {I : Type i} {I' : Type j} [Fintype I] [Fintype I']
    (f : I → (V ⟶ U)) (g : I' → (V ⟶ U))
    {K : Type k} (W : K → C) (p : ∀ a, W a ⟶ V)
    (hp : Sieve.ofArrows W p ∈ J V)
    (e : K → (I ≃ I')) (hfg : ∀ k a, p k ≫ f a = p k ≫ g (e k a)) :
    representedSum J f = representedSum J g := by
  apply section_eq_of_cover J W p hp
  intro k
  rw [representedSum_restrict, representedSum_restrict]
  exact representedSum_reindex J (e k) _ _ (hfg k)

/-- Postcomposition carries each actual generator to its composite generator. -/
theorem representedGenerator_map {V U U' : C} (f : V ⟶ U) (g : U ⟶ U') :
    ((freeAbelianSheafFunctor.{t} J).map g).hom.app (op V)
      (representedGenerator J f) = representedGenerator J (f ≫ g) := by
  symm
  exact (congrArg (sectionsEquiv J V _) (Functor.map_comp _ f g)).trans
    (sectionsEquiv_naturality J V ((freeAbelianSheafFunctor J).map f)
      ((freeAbelianSheafFunctor J).map g))

omit [HasSheafify J AddCommGrpCat.{max h t}] in
/-- Glue actual additive sections along a covering family. -/
theorem existsUnique_section_of_cover (F : Sheaf J AddCommGrpCat.{max h t}) {V : C}
    {K : Type k} (W : K → C) (p : ∀ a, W a ⟶ V)
    (hp : Sieve.ofArrows W p ∈ J V) (a : ∀ k, F.obj.obj (op (W k)))
    (ha : ∀ i j (T : C) (f : T ⟶ W i) (g : T ⟶ W j),
      f ≫ p i = g ≫ p j → F.obj.map f.op (a i) = F.obj.map g.op (a j)) :
    ∃! b : F.obj.obj (op V), ∀ k, F.obj.map (p k).op b = a k := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J F.obj
      (forget AddCommGrpCat.{max h t}) F.property)
  exact (Presieve.isSheafFor_arrows_iff (P := F.obj ⋙ forget _) p).mp
    (hF.isSheafFor _ hp) a ha

end CategoryTheory.Sheaf.Hypercohomology
