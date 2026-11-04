/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSectionsEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DerivedUnit
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Finite splitting by original derived field-unit classes

A finite family of graded bases gives a map from the native biproduct of
original field units in the corresponding degrees. Its components are the
original maps represented by the given homology classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe r u v w

private theorem isIso_desc_of_basis {R : Type r} [CommRing R] {I : Type} [Finite I]
    {F : I → ModuleCat.{r} R} {M : ModuleCat.{r} R} (p : I → Prop)
    (f : ∀ i, F i ⟶ M) (hzero : ∀ i, ¬ p i → IsZero (F i))
    (e : ∀ i : Subtype p, ModuleCat.of R R ≅ F i.val)
    (b : Module.Basis (Subtype p) R M) (hvalue : ∀ i : Subtype p, f i.val ((e i).hom 1) = b i) :
    IsIso (biproduct.desc f) := by
  classical
  let value (s : Cofan F) (i : Subtype p) : s.pt := s.inj i.val ((e i).hom 1)
  let lift (s : Cofan F) : M ⟶ s.pt := ModuleCat.ofHom (b.constr R (value s))
  have hfac (s : Cofan F) (i : I) : f i ≫ lift s = s.inj i := by
    by_cases hi : p i
    · let j : Subtype p := ⟨i, hi⟩
      apply (cancel_epi (e j).hom).mp
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      change lift s (f i ((e j).hom 1)) = value s j
      rw [show f i ((e j).hom 1) = b j from hvalue j]
      exact b.constr_basis R (value s) j
    · exact (hzero i hi).eq_of_src _ _
  let hc : IsColimit (Cofan.mk M f) := Cofan.IsColimit.mk _ lift hfac (by
    intro s m hm
    apply ModuleCat.hom_ext
    apply b.ext
    intro i
    change m (b i) = lift s (b i)
    calc
      m (b i) = m (f i.val ((e i).hom 1)) := congrArg m (hvalue i).symm
      _ = value s i :=
        congrArg (fun g : F i.val ⟶ s.pt => g ((e i).hom 1)) (hm i.val)
      _ = lift s (b i) := (b.constr_basis R (value s) i).symm)
  exact (IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) hc).isIso_hom

private theorem isIso_graded_desc_of_basis {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {R : Type r} [CommRing R] (G : C ⥤ ModuleCat.{r} R)
    [G.Additive] [G.ReflectsIsomorphisms] (U : C) (e : ModuleCat.of R R ≅ G.obj U)
    {I : Type} [Finite I] (d : I → ℤ) (K : DerivedCategory.Plus C)
    (f : ∀ i, (DerivedCategory.Plus.singleFunctor C (d i)).obj U ⟶ K)
    (b : ∀ q : ℤ, Module.Basis {i : I // d i = q} R
      (G.obj ((DerivedCategory.Plus.homologyFunctor C q).obj K)))
    (hf : ∀ i, (G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso C (d i)).inv.app U ≫
      (DerivedCategory.Plus.homologyFunctor C (d i)).map (f i))) (e.hom 1) = b (d i) ⟨i, rfl⟩) :
    IsIso (biproduct.desc f) := by
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro q
  let H := DerivedCategory.Plus.homologyFunctor C q
  let F := H ⋙ G
  let S (q : ℤ) : DerivedCategory.Plus C := (DerivedCategory.Plus.singleFunctor C q).obj U
  let eH : H.obj (S q) ≅ U := (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).app U
  let eJ (j : {i : I // d i = q}) : ModuleCat.of R R ≅ F.obj (S (d j.val)) :=
    e ≪≫ G.mapIso eH.symm ≪≫ F.mapIso (eqToIso (congrArg S j.property.symm))
  have hzero (i : I) (hi : d i ≠ q) : IsZero (F.obj (S (d i))) := by
    apply G.map_isZero
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.Plus.isZero_homology_of_isLE (S (d i)) (d i) q h
    · exact DerivedCategory.Plus.isZero_homology_of_isGE (S (d i)) (d i) q h
  have hvalue (j : {i : I // d i = q}) : (F.map (f j.val)) ((eJ j).hom 1) = b q j := by
    obtain ⟨i, hi⟩ := j
    subst q
    have he : eJ ⟨i, rfl⟩ = e ≪≫ G.mapIso eH.symm := by
      change e ≪≫ G.mapIso eH.symm ≪≫ F.mapIso (Iso.refl _) = _
      rw [Functor.mapIso_refl]
      change e ≪≫ (G.mapIso eH.symm ≪≫ Iso.refl (G.obj (H.obj (S (d i))))) = _
      rw [Iso.trans_refl]
    rw [he]
    let h := G.map eH.inv
    let k := G.map (H.map (f i))
    change (h ≫ k) (e.hom 1) = b (d i) ⟨i, rfl⟩
    exact (congrArg (fun g : G.obj U ⟶ F.obj K => g (e.hom 1))
      (G.map_comp eH.inv (H.map (f i)))).symm.trans (hf i)
  let t : (⨁ fun i => F.obj (S (d i))) ⟶ F.obj K := biproduct.desc fun i => F.map (f i)
  let : IsIso t :=
    isIso_desc_of_basis (fun i => d i = q) (fun i => F.map (f i)) hzero eJ (b q) hvalue
  let k := F.mapBiproduct (fun i => S (d i)) ≪≫ asIso t
  have hk : k.hom = F.map (biproduct.desc f) :=
    biproduct.mapBiproduct_hom_desc F (fun i => S (d i)) f
  have hF : IsIso (F.map (biproduct.desc f)) := hk ▸ k.isIso_hom
  let : IsIso (G.map (H.map (biproduct.desc f))) := hF
  exact isIso_of_reflects_iso (H.map (biproduct.desc f)) G

private theorem plus_hasBiproduct_of_finite {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {I : Type} [Finite I] (F : I → DerivedCategory.Plus C) :
    HasBiproduct F := inferInstance

section Field

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]

private def fieldUnitGeneratorIso :
    ModuleCat.of Λ Λ ≅ (moduleGlobalSections (Spec (.of Ω)) Λ).obj
      (moduleUnit (Spec (.of Ω)) Λ) := by
  let a := moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ
  letI : IsIso (a.unit.app (ModuleCat.of Λ Λ)) :=
    moduleFieldGlobalSectionsAdjunction_unit_isIso Ω Λ _
  exact asIso (a.unit.app (ModuleCat.of Λ Λ)) ≪≫
    (moduleGlobalSections (Spec (.of Ω)) Λ).mapIso (moduleUnitConstantIso (Spec (.of Ω)) Λ)

private theorem fieldUnitSectionsEquiv_eq_eval
    {M : ModuleSheaf (Spec (.of Ω)) Λ} (f : moduleUnit (Spec (.of Ω)) Λ ⟶ M) :
    moduleFieldUnitSectionsEquiv Ω Λ M f =
      ((moduleGlobalSections (Spec (.of Ω)) Λ).map f) ((fieldUnitGeneratorIso Ω Λ).hom 1) := by
  let a := moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ
  let e := moduleUnitConstantIso (Spec (.of Ω)) Λ
  let G := moduleGlobalSections (Spec (.of Ω)) Λ
  have h : a.homEquiv (ModuleCat.of Λ Λ) M (e.hom ≫ f ≫ 𝟙 M) =
      (a.unit.app (ModuleCat.of Λ Λ) ≫ G.map e.hom) ≫ G.map f := by
    rw [Category.comp_id, a.homEquiv_unit, G.map_comp, Category.assoc]
  exact congrArg (fun g : ModuleCat.of Λ Λ ⟶ G.obj M => g 1) h

variable [HasDerivedCategory.{w} (ModuleSheaf (Spec (.of Ω)) Λ)]

/-- The original field unit placed in a specified degree in the native derived category. -/
def moduleFieldSingleUnit (i : ℤ) : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ) :=
  (DerivedCategory.Plus.singleFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj
    (moduleUnit (Spec (.of Ω)) Λ)

variable {I : Type} [Finite I] (d : I → ℤ)
  (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
  (b : ∀ q : ℤ, Module.Basis {i : I // d i = q} Λ
    ((moduleGlobalSections (Spec (.of Ω)) Λ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q).obj K)))

/-- The family of original units in the specified degrees of the native derived category. -/
def moduleFieldDerivedFreeSplitUnits : I → DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ) :=
  fun i => moduleFieldSingleUnit Ω Λ (d i)

local instance fieldSplit_hasBiproduct : HasBiproduct (moduleFieldDerivedFreeSplitUnits Ω Λ d) :=
  plus_hasBiproduct_of_finite (C := ModuleSheaf (Spec (.of Ω)) Λ)
    (moduleFieldDerivedFreeSplitUnits Ω Λ d)

/-- The original map represented by the specified graded basis vector. -/
def moduleFieldDerivedFreeSplitComponent (i : I) :
    moduleFieldDerivedFreeSplitUnits Ω Λ d i ⟶ K :=
  (moduleFieldDerivedUnitHomologyEquiv Ω Λ (d i) K).symm (b (d i) ⟨i, rfl⟩)

/-- The original class of each graded basis vector gives a component of the finite sum map. -/
def moduleFieldDerivedFreeSplitMap :
    (⨁ moduleFieldDerivedFreeSplitUnits Ω Λ d) ⟶ K :=
  biproduct.desc (moduleFieldDerivedFreeSplitComponent Ω Λ d K b)

/-- The finite sum map has the original inverse comparison on each chosen basis vector. -/
@[reassoc]
theorem moduleFieldDerivedFreeSplitMap_ι (i : I) :
    biproduct.ι (moduleFieldDerivedFreeSplitUnits Ω Λ d) i ≫
        moduleFieldDerivedFreeSplitMap Ω Λ d K b =
      moduleFieldDerivedFreeSplitComponent Ω Λ d K b i :=
  biproduct.ι_desc _ _

/-- The native graded basis map is an isomorphism in the original bounded-below derived category. -/
theorem moduleFieldDerivedFreeSplitMap_isIso :
    IsIso (moduleFieldDerivedFreeSplitMap Ω Λ d K b) := by
  let G := moduleGlobalSections (Spec (.of Ω)) Λ
  let E := moduleFieldSectionsEquivalence Ω Λ
  let : G.ReflectsIsomorphisms := by
    have h : E.inverse = G := moduleFieldSectionsEquivalence_inverse Ω Λ
    rw [← h]
    infer_instance
  let C := ModuleSheaf (Spec (.of Ω)) Λ
  let U : C := moduleUnit (Spec (.of Ω)) Λ
  let f := moduleFieldDerivedFreeSplitComponent Ω Λ d K b
  change IsIso (biproduct.desc f)
  apply isIso_graded_desc_of_basis G U (fieldUnitGeneratorIso Ω Λ) d K f b
  intro i
  let H := DerivedCategory.Plus.homologyFunctor C (d i)
  let eH : H.obj ((DerivedCategory.Plus.singleFunctor C (d i)).obj U) ≅ U :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C (d i)).app U
  let x : U ⟶ H.obj K := eH.inv ≫ H.map (f i)
  have hEval := fieldUnitSectionsEquiv_eq_eval Ω Λ x
  have hBasis := (moduleFieldDerivedUnitHomologyEquiv Ω Λ (d i) K).apply_symm_apply
    (b (d i) ⟨i, rfl⟩)
  exact hEval.symm.trans hBasis

end Field

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
