/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.SectionComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection.Transport

/-! # Original section comparisons at their actual functor values

Equality transport is evaluated before any concrete coefficient is supplied.
The original composition/identity data then prove the whole function law for
the actual supplied coefficient functor and pullback values. This avoids a
second cohomology presentation at a native H1 boundary.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe uI uC vC uD vD e uV uW

/-- Evaluate the original equality-transported comparison at a variable object. -/
theorem comparison_transport_hom_app
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (F : I → C ⥤ D)
    {i j : I} (h : i = j) {G : C ⥤ D} (t : F j ≅ G) (A : C) :
    (eqToIso (congrArg F h) ≪≫ t).hom.app A =
      eqToHom (congrArg (fun k => (F k).obj A) h) ≫ t.hom.app A := by
  cases h
  rfl

/-- The whole original unit law may retain its final literal identity component. -/
theorem coefficientIso_identity_of_unit_composite
    {C : Type uC} [Category.{vC} C] (F : C ⥤ C) {K : C ⥤ C}
    (i : F ≅ 𝟭 C) (c : K ≅ F ⋙ F) (A : C)
    (j : K.obj A ⟶ F.obj A) (q : F.obj A ≅ A)
    (hcomp : c.hom.app A ≫ F.map q.hom ≫ q.hom = j ≫ q.hom)
    (hunit : c.hom.app A ≫ F.map (i.hom.app A) ≫ 𝟙 (F.obj A) = j) :
    q.hom = i.hom.app A := by
  apply coefficientIso_identity F i c A j q hcomp
  exact (congrArg (fun k => c.hom.app A ≫ k)
    (Category.comp_id (F.map (i.hom.app A)))).symm.trans hunit

/-- Original coefficient composition and source comparison prove the whole function
square at the supplied cohomology functor, before any native class is evaluated. -/
theorem sectionCoefficient_map_values
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F : C ⥤ D} {H : D ⥤ C} {K : C ⥤ C}
    (c : K ≅ F ⋙ H) (i : K ≅ 𝟭 C)
    {A : C} {B : D} (q : F.obj A ≅ B) (r : H.obj B ≅ A) (k : K.obj A ≅ A)
    (hcomp : c.hom.app A ≫ H.map q.hom ≫ r.hom = k.hom)
    (hid : k.hom = i.hom.app A)
    (φ : H.obj (F.obj A) ⟶ A) (hφ : φ = (sourceSectionIso c i).hom.app A)
    (T : C ⥤ AddCommGrpCat.{e}) {V : Type uV} {W : Type uW}
    (E : V → T.obj A) (P : V → T.obj (H.obj (F.obj A)))
    (PB : W → T.obj (H.obj B)) (Q : W → V) (R : W → T.obj A)
    (hE : E = fun b => T.map φ (P b))
    (hR : R = fun b => T.map r.hom (PB b))
    (hP : ∀ b, P (Q b) = T.map (H.map q.inv) (PB b)) :
    E ∘ Q = R := by
  have hs := sectionCoefficient_of_composition c i q r k hcomp hid
  have hinv : H.map q.inv ≫ φ = r.hom := by
    rw [hφ, ← hs, ← Category.assoc, ← H.map_comp, q.inv_hom_id, H.map_id,
      Category.id_comp]
  funext b
  rw [hE, hR]
  change T.map φ (P (Q b)) = T.map r.hom (PB b)
  rw [hP]
  exact (ConcreteCategory.congr_hom (T.map_comp (H.map q.inv) φ) (PB b)).symm.trans
    (congrArg (fun f => T.map f (PB b)) hinv)


/-- Transport the original coefficient family before choosing the indexing data.
The unit equation is the already proved original identity comparison. -/
theorem coefficientFamily_transport_hom
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    (K : I → C ⥤ C) (A : C) (q : ∀ k, (K k).obj A ≅ A)
    {i j : I} (h : i = j) (e : K j ≅ 𝟭 C)
    (hid : (q j).hom = e.hom.app A) :
    (q i).hom = (eqToIso (congrArg K h) ≪≫ e).hom.app A := by
  cases h
  simpa using hid

universe eC eD

/-- The original pullback followed by coefficient change, with independent
source and target value universes. This selects no cohomology model. -/
def coefficientValueTransfer
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (H : D ⥤ C) (S : D ⥤ AddCommGrpCat.{eD}) (T : C ⥤ AddCommGrpCat.{eC})
    (P : ∀ B : D, S.obj B →+ T.obj (H.obj B))
    {B : D} {A : C} (φ : H.obj B ⟶ A) : S.obj B →+ T.obj A :=
  (T.map φ).hom.comp (P B)

/-- A whole equality of the actual original additive maps. The coefficient
contraction follows from the original composition and identity comparisons;
the pullback law is its ordinary coefficient naturality. Each supplied map
is identified with its original construction before any value is evaluated. -/
theorem sectionCoefficient_transfer_original
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F : C ⥤ D} {H : D ⥤ C} {K : C ⥤ C}
    (c : K ≅ F ⋙ H) (i : K ≅ 𝟭 C)
    {A : C} {B : D} (q : F.obj A ≅ B) (r : H.obj B ≅ A) (k : K.obj A ≅ A)
    (hcomp : c.hom.app A ≫ H.map q.hom ≫ r.hom = k.hom)
    (hid : k.hom = i.hom.app A)
    (φ : H.obj (F.obj A) ⟶ A) (hφ : φ = (sourceSectionIso c i).hom.app A)
    (S : D ⥤ AddCommGrpCat.{eD}) (T : C ⥤ AddCommGrpCat.{eC})
    (P : ∀ B : D, S.obj B →+ T.obj (H.obj B))
    (hP : ∀ {M N : D} (f : M ⟶ N),
      (P N).comp (S.map f).hom = (T.map (H.map f)).hom.comp (P M))
    (E : S.obj (F.obj A) →+ T.obj A)
    (Q : S.obj B →+ S.obj (F.obj A)) (R : S.obj B →+ T.obj A)
    (hE : E = coefficientValueTransfer H S T P φ)
    (hQ : Q = (S.map q.inv).hom)
    (hR : R = coefficientValueTransfer H S T P r.hom) : E.comp Q = R := by
  have hs := sectionCoefficient_of_composition c i q r k hcomp hid
  have hinv : H.map q.inv ≫ φ = r.hom := by
    rw [hφ, ← hs, ← Category.assoc, ← H.map_comp, q.inv_hom_id, H.map_id,
      Category.id_comp]
  rw [hE, hQ, hR]
  ext x
  change T.map φ (P (F.obj A) (S.map q.inv x)) = T.map r.hom (P B x)
  have hp := congrArg
    (fun f : S.obj B →+ T.obj (H.obj (F.obj A)) => f x) (hP q.inv)
  change P (F.obj A) (S.map q.inv x) = T.map (H.map q.inv) (P B x) at hp
  rw [hp]
  exact (ConcreteCategory.congr_hom (T.map_comp (H.map q.inv) φ) (P B x)).symm.trans
    (congrArg (fun f => T.map f (P B x)) hinv)

/-- Combine the original objectwise transport and original identity equation
before specializing either coefficient arrow. The supplied congruence is the
producer's literal equation, not a reconstructed comparison family. -/
theorem comparison_transport_hom_app_of_original
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    (K : I → C ⥤ C) {i j : I} (h : i = j) (e : K j ≅ 𝟭 C) (A : C)
    {k : (K i).obj A ⟶ A} {q : (K j).obj A ⟶ A}
    (hcongr : eqToHom (congrArg (fun l => (K l).obj A) h) ≫ q = k)
    (hid : q = e.hom.app A) :
    k = (eqToIso (congrArg K h) ≪≫ e).hom.app A := by
  have ht := comparison_transport_hom_app K h e A
  exact hcongr.symm.trans
    ((congrArg (fun f : (K j).obj A ⟶ A =>
      eqToHom (congrArg (fun l => (K l).obj A) h) ≫ f) hid).trans ht.symm)

end CategoryTheory.Functor
