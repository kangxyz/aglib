/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.LocalLifting
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ProjectiveHomComplex

/-! # Stability of basis Čech acyclicity under injective quotients -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

open ModuleCoefficients

universe c h w

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasSheafify J AddCommGrpCat.{max w h}]

/-- Positive exactness of the original tuple cochains on selected covers only. -/
def CechAcyclic (B : CoverBasis.{c, h, w} J)
    (F : Sheaf J AddCommGrpCat.{max w h}) : Prop :=
  ∀ (W : C) (ι : Type w) (U : ι → Over W), B.selected W ι U → ∀ (n : ℕ),
    (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) F.obj).ExactAt (n + 1)

variable [J.WEqualsLocallyBijective (Type (max w h))]
  [J.PreservesSheafification AddCommGrpCat.free.{max w h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w h}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max w h})]
  {B : CoverBasis.{c, h, w} J}

/-- Actual section lifting holds on every basis object. -/
theorem CechAcyclic.sections_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max w h})) (hS : S.ShortExact)
    (hF : CechAcyclic B S.X₁) (W : C) (hW : B.objects W) :
    Function.Surjective (S.g.hom.app (op W)) :=
  sections_surjective_of_cech_h1 B S hS (fun W ι U hU => hF W ι U hU 0) W hW

/-- Maps from a free tuple term lift along the quotient, because all its
representing intersections belong to the basis. -/
theorem CechAcyclic.freeTuple_hom_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max w h})) (hS : S.ShortExact)
    (hF : CechAcyclic B S.X₁) {W : C} {ι : Type w} (U : ι → Over W)
    (hU : B.selected W ι U) (n : ℕ) :
    Function.Surjective (fun a :
      Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) n ⋙ AddCommGrpCat.free ⟶
        S.X₂.obj => a ≫ S.g.hom) := by
  let V := fun a : Fin (n + 1) → ι => (∏ᶜ fun i => U (a i)).left
  let e := ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso
    (Presheaf.Cech.tupleProductIso U n)
  intro z
  obtain ⟨a, ha⟩ : ∃ a : Presheaf.Cech.familyPresheaf V ⋙ AddCommGrpCat.free ⟶ S.X₂.obj,
      a ≫ S.g.hom = e.inv ≫ z := by
    let t := Presheaf.Cech.freeFamilyHomEquiv V S.X₃.obj (e.inv ≫ z)
    choose s hs using fun i => hF.sections_surjective S hS (V i) (B.intersections hU n i) (t i)
    refine ⟨(Presheaf.Cech.freeFamilyHomEquiv V S.X₂.obj).symm s, ?_⟩
    apply (Presheaf.Cech.freeFamilyHomEquiv V S.X₃.obj).injective
    funext i
    change S.g.hom.app (op (V i))
      (((Presheaf.Cech.freeFamilyHomEquiv V S.X₂.obj).symm s).app (op (V i))
        (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)) = t i
    have hi := congrFun ((Presheaf.Cech.freeFamilyHomEquiv V S.X₂.obj).apply_symm_apply s) i
    rw [Presheaf.Cech.freeFamilyHomEquiv_apply] at hi
    rw [hi]
    exact hs i
  refine ⟨e.hom ≫ a, ?_⟩
  change (e.hom ≫ a) ≫ S.g.hom = z
  rw [Category.assoc, ha, Iso.hom_inv_id_assoc]

/-- The original tuple Hom complexes form a short exact sequence, even though
forgetting sheaf exactness need not give a pointwise epimorphism on the whole site. -/
theorem CechAcyclic.homComplex_shortExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max w h})) (hS : S.ShortExact)
    (hF : CechAcyclic B S.X₁) {W : C} {ι : Type w} (U : ι → Over W)
    (hU : B.selected W ι U) :
    ((S.map (sheafToPresheaf J AddCommGrpCat)).map
      (additiveHomFunctor (Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)))).ShortExact := by
  let : Mono S.f := hS.mono_f
  let T := S.map (sheafToPresheaf J AddCommGrpCat)
  let : Mono T.f := by
    change Mono ((sheafToPresheaf J AddCommGrpCat).map S.f)
    infer_instance
  have hT : T.Exact := hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf J AddCommGrpCat) inferInstance inferInstance
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (T.map (preadditiveCoyoneda.obj
    (op ((Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)).X n)))).ShortExact
  refine { exact := hT.map_of_mono_of_preservesKernel _ inferInstance inferInstance
           mono_f := by
             change Mono ((preadditiveCoyoneda.obj
               (op ((Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)).X n))).map T.f)
             infer_instance
           epi_g := ?_ }
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  exact hF.freeTuple_hom_surjective S hS U hU n

/-- The Čech-acyclic class is stable under a quotient whose middle term is
Čech-acyclic. The quotient is not required to be quasi-coherent. -/
theorem CechAcyclic.quotient
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max w h})) (hS : S.ShortExact)
    (hF : CechAcyclic B S.X₁) (hG : CechAcyclic B S.X₂) : CechAcyclic B S.X₃ := by
  intro W ι U hU n
  have hT := hF.homComplex_shortExact S hS U hU
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) (n + 2) rfl).isZero_X₂
    ((hG W ι U hU n).isZero_homology.eq_of_src _ _)
    ((hF W ι U hU (n + 1)).isZero_homology.eq_of_tgt _ _)

end CategoryTheory.Sheaf.BasisAcyclicity
