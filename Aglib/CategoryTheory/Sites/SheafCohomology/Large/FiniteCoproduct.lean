/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverEffacement
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite disjoint-cover decomposition of original represented cohomology

The input is bijectivity of the actual section restrictions for every abelian
sheaf. The free-representable universal property gives an actual coproduct
source, and native Ext finite-biproduct comparison gives all cohomology degrees.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.LargeCohomology

universe c h t e r

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]
  {ι : Type r} {U : ι → C} (V : C) (f : ∀ i, U i ⟶ V)

open Hypercohomology

/-- The original free-representable maps form the source cocone. -/
def freeRepresentableCofan : Cofan (fun i => freeAbelianSheaf.{t} J (U i)) :=
  Cofan.mk (freeAbelianSheaf J V) (fun i => (freeAbelianSheafFunctor J).map (f i))

/-- Actual section-product bijectivity gives the free-representable coproduct property. -/
def freeRepresentableCofanIsColimit
    (hs : ∀ F : Sheaf J AddCommGrpCat.{max h t}, Function.Bijective
      (fun x : F.obj.obj (op V) => fun i => F.obj.map (f i).op x)) :
    IsColimit (freeRepresentableCofan J V f) := by
  let d (s : Cofan (fun i => freeAbelianSheaf.{t} J (U i))) :=
    (sectionsEquiv J V s.pt).symm
      ((Equiv.ofBijective _ (hs s.pt)).symm
        (fun i => sectionsEquiv J (U i) s.pt (s.inj i)))
  have hd (s : Cofan (fun i => freeAbelianSheaf.{t} J (U i))) (i : ι) :
      (freeAbelianSheafFunctor J).map (f i) ≫ d s = s.inj i := by
    apply (sectionsEquiv J (U i) s.pt).injective
    rw [BasisAcyclicity.sectionsEquiv_precomp]
    dsimp only [d]
    rw [Equiv.apply_symm_apply]
    exact congrFun ((Equiv.ofBijective _ (hs s.pt)).apply_symm_apply
      (fun i => sectionsEquiv J (U i) s.pt (s.inj i))) i
  refine Cofan.IsColimit.mk _ d hd ?_
  intro s m hm
  change freeAbelianSheaf J V ⟶ s.pt at m
  change ∀ i, (freeAbelianSheafFunctor J).map (f i) ≫ m = s.inj i at hm
  apply (sectionsEquiv J V s.pt).injective
  apply (hs s.pt).injective
  funext i
  change s.pt.obj.map (f i).op (sectionsEquiv J V s.pt m) =
    s.pt.obj.map (f i).op (sectionsEquiv J V s.pt (d s))
  rw [← BasisAcyclicity.sectionsEquiv_precomp,
    ← BasisAcyclicity.sectionsEquiv_precomp, hm i, hd s i]

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max h t})]

/-- Finite actual disjoint section decomposition yields original represented cohomology. -/
def finiteCoproductAddEquiv [Fintype ι]
    (hs : ∀ F : Sheaf J AddCommGrpCat.{max h t}, Function.Bijective
      (fun x : F.obj.obj (op V) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{max h t}) (n : ℕ) :
    H.{e} J F n V ≃+ ∀ i, H.{e} J F n (U i) := by
  let d := fun i => freeAbelianSheaf.{t} J (U i)
  let hc := freeRepresentableCofanIsColimit J V f hs
  letI : HasCoproduct d := ⟨⟨freeRepresentableCofan J V f, hc⟩⟩
  letI : HasBiproduct d := HasBiproduct.of_hasCoproduct d
  let e := (coproductIsCoproduct d).coconePointUniqueUpToIso hc
  let e₁ := (((extFunctor n).mapIso e.op).app F).addCommGroupIsoToAddEquiv
  let e₂ := (((extFunctor n).mapIso (biproduct.isoCoproduct d).op).app F)
  exact e₁.trans (e₂.addCommGroupIsoToAddEquiv.trans
    (Ext.biproductAddEquiv (biproduct.isBilimit d) F n))

end CategoryTheory.Sheaf.LargeCohomology
