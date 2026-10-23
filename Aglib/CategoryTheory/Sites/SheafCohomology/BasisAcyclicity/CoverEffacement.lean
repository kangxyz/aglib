/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Cover effacement of individual positive Ext classes

An original Ext class from the free representable is represented by a cocycle
in an actual injective resolution. The boundary-to-cycles map is epimorphic.
Its image sieve at that cocycle section is covering; each local lift gives a
boundary and therefore kills the original restricted class. No vanishing of
positive sheaf cohomology is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

open Hypercohomology

universe c h w e

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h w}]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original free-representable evaluation respects restriction of the base. -/
theorem sectionsEquiv_precomp {U V : C} (g : V ⟶ U)
    (F : Sheaf J AddCommGrpCat.{max h w}) (a : freeAbelianSheaf J U ⟶ F) :
    sectionsEquiv J V F ((freeAbelianSheafFunctor J).map g ≫ a) =
      F.obj.map g.op (sectionsEquiv J U F a) := by
  let adj₁ := sheafificationAdjunction J AddCommGrpCat.{max h w}
  let adj₂ := AddCommGrpCat.adj.whiskerRight Cᵒᵖ
  let a' := adj₁.homEquiv _ F a
  have h₁ := adj₁.homEquiv_naturality_left
    (((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free).map
      (uliftYoneda.{w}.map g)) a
  have h₂ := adj₂.homEquiv_naturality_left (uliftYoneda.{w}.map g) a'
  exact (congrArg (fun z => uliftYonedaEquiv (adj₂.homEquiv _ F.obj z)) h₁).trans
    ((congrArg uliftYonedaEquiv h₂).trans (uliftYonedaEquiv_naturality _ g.op).symm)

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max h w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max h w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max h w})]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A genuine covering image sieve kills an individual positive original Ext
class. The displayed injective resolution is used to produce the sieve. -/
theorem exists_covering_sieve_ext_eq_zero_of_resolution
    {U : C} {A : Sheaf J AddCommGrpCat.{max h w}}
    (R : InjectiveResolution A) (n : ℕ)
    (α : Ext (freeAbelianSheaf J U) A (n + 1)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      (Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp α (Nat.zero_add _) = 0 := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
  let d := R.cocomplex.d (n + 1) (n + 2)
  let k : freeAbelianSheaf J U ⟶ kernel d := kernel.lift d f hf
  let q : R.cocomplex.X n ⟶ kernel d :=
    kernel.lift d (R.cocomplex.d n (n + 1)) (R.cocomplex.d_comp_d _ _ _)
  let : Epi q := (R.exact_succ n).epi_kernelLift
  let : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat q).mpr inferInstance
  let s := sectionsEquiv J U (kernel d) k
  refine ⟨Presheaf.imageSieve q.hom s, Presheaf.imageSieve_mem J q.hom s, ?_⟩
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  let b : freeAbelianSheaf J V ⟶ R.cocomplex.X n :=
    (sectionsEquiv J V (R.cocomplex.X n)).symm t
  have hbq : b ≫ q = (freeAbelianSheafFunctor J).map g ≫ k := by
    apply (sectionsEquiv J V (kernel d)).injective
    rw [sectionsEquiv_naturality, sectionsEquiv_precomp]
    simpa only [b, Equiv.apply_symm_apply, s] using ht
  have hb : b ≫ R.cocomplex.d n (n + 1) =
      (freeAbelianSheafFunctor J).map g ≫ f := by
    have h := congrArg (fun z => z ≫ kernel.ι d) hbq
    simpa only [Category.assoc, q, k, kernel.lift_ι] using h
  rw [R.mk₀_comp_extMk]
  exact (R.extMk_eq_zero_iff _ (n + 2) rfl _ n rfl).mpr ⟨b, hb⟩

/-- Every positive original Ext class from a free representable vanishes on a
covering sieve, using the native chosen injective resolution. -/
theorem exists_covering_sieve_ext_eq_zero
    {U : C} {A : Sheaf J AddCommGrpCat.{max h w}} [HasInjectiveResolution A]
    (n : ℕ) (α : Ext (freeAbelianSheaf J U) A (n + 1)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      (Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp α (Nat.zero_add _) = 0 :=
  exists_covering_sieve_ext_eq_zero_of_resolution J (injectiveResolution A) n α

end CategoryTheory.Sheaf.BasisAcyclicity
