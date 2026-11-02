/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomPresentationComplex
public import Aglib.Algebra.Category.ModuleCat.Sheaf.LocalHomExactness
public import Aglib.Algebra.Category.ModuleCat.Sheaf.LocalExactness
public import Aglib.Algebra.Category.ModuleCat.Sheaf.SliceExactness
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FiniteConstantCharts
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Local boundaries through the original constant-chart complex comparison

A chart's whole presheaf-complex isomorphism transports a closed internal-Hom
section to an actual module-linear cocycle. The inverse complex map transports
its local boundary back. All restrictions and differentials remain the
original maps; no sectionwise exactness of arbitrary sheaf epimorphisms is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type (max c h)) [CommRing Λ]
  [HasWeakSheafify J RingCat.{max c h}] [J.WEqualsLocallyBijective RingCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  [HasWeakSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) RingCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective RingCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose
    (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  (U : C)

attribute [local instance] ModuleCat.Sheaf.hasSheafify

/-- The original coefficient equivalence followed by original slice restriction. -/
abbrev moduleValuedOverFunctor : ModuleSheaf.{c, h, max c h, max c h} J Λ ⥤
    Sheaf (J.over U) (ModuleCat.{max c h} Λ) :=
  (moduleSheafEquivalence J Λ).inverse ⋙ J.overPullback (ModuleCat.{max c h} Λ) U

/-- The original composite is additive. -/
instance moduleValuedOverFunctor_additive : (moduleValuedOverFunctor J Λ U).Additive := by
  infer_instance

variable (M : ModuleSheaf.{c, h, max c h, max c h} J Λ) (M₀ : ModuleCat.{max c h} Λ)
  (η : (Functor.const (Over U)ᵒᵖ).obj M₀ ⟶
    ((J.overPullback (ModuleCat.{max c h} Λ) U).obj
      ((moduleSheafEquivalence J Λ).inverse.obj M)).obj)
  [CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η]
  [CategoryTheory.Presheaf.IsLocallyInjective (J.over U) η]

include η in
set_option backward.isDefEq.respectTransparency false in
/-- Original chart-Hom local boundaries become original internal-Hom local boundaries. -/
theorem exists_cover_boundary_of_presentation
    (I : CochainComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ) ℕ) (q : ℕ)
    (hI : ModuleCat.Sheaf.LocallyBoundary (J.over U)
      (((moduleValuedOverFunctor J Λ U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I)
        M₀ q)
    (x : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M (I.X (q + 1))).val.obj
      (op U))
    (hx : (SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M)
      (I.d (q + 1) (q + 2))).val.app (op U) x = 0) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ y : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M (I.X q)).val.obj
          (op V),
        (SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M)
          (I.d q (q + 1))).val.app (op V) y =
        (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M
          (I.X (q + 1))).val.map f.op x := by
  let K := ((moduleValuedOverFunctor J Λ U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let e := presentationComplexIso J Λ U M M₀ η (ComplexShape.up ℕ) I
  let V₀ : Over U := Over.mk (𝟙 U)
  let g : M₀ ⟶ (K.X (q + 1)).obj.obj (op V₀) :=
    ((e.hom.f (q + 1)).app (op V₀)) x
  have hg : g ≫ (K.d (q + 1) (q + 2)).hom.app (op V₀) = 0 := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (e.hom.comm (q + 1) (q + 2)) (op V₀)) x
    change g ≫ (K.d (q + 1) (q + 2)).hom.app (op V₀) =
      ((e.hom.f (q + 2)).app (op V₀))
        ((SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M)
          (I.d (q + 1) (q + 2))).val.app (op U) x) at h
    rw [hx, map_zero] at h
    exact h
  let S := ModuleCat.Sheaf.boundarySieve (J.over U) K M₀ q g
  have hS : S ∈ (J.over U) V₀ := hI V₀ g hg
  refine ⟨Sieve.overEquiv V₀ S, hS, ?_⟩
  intro V f hf
  have hf' := (Sieve.overEquiv_iff S f).mp hf
  obtain ⟨a, ha⟩ := hf'
  let W : Over U := Over.mk (f ≫ 𝟙 U)
  let k : W ⟶ V₀ := Over.homMk f
  change a ≫ (K.d q (q + 1)).hom.app (op W) =
    g ≫ (K.X (q + 1)).obj.map k.op at ha
  let y := ((e.inv.f q).app (op W)) a
  refine ⟨y, ?_⟩
  have hd := ConcreteCategory.congr_hom
    (NatTrans.congr_app (e.inv.comm q (q + 1)) (op W)) a
  change (SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M)
      (I.d q (q + 1))).val.app (op V) y =
    ((e.inv.f (q + 1)).app (op W))
      (a ≫ (K.d q (q + 1)).hom.app (op W)) at hd
  rw [hd, ha]
  have hn := ConcreteCategory.congr_hom ((e.inv.f (q + 1)).naturality k.op) g
  change ((e.inv.f (q + 1)).app (op W))
      (g ≫ (K.X (q + 1)).obj.map k.op) =
    (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M
      (I.X (q + 1))).val.map f.op (((e.inv.f (q + 1)).app (op V₀)) g) at hn
  rw [hn]
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (HomologicalComplex.congr_hom e.hom_inv_id (q + 1)) (op V₀)) x
  change ((e.inv.f (q + 1)).app (op V₀)) g = x at he
  rw [he]

end ModuleCat.Sheaf.ConstantRing

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type (max c h)) [CommRing Λ]
  [HasWeakSheafify J RingCat.{max c h}] [J.WEqualsLocallyBijective RingCat.{max c h}]
  [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

variable [IsNoetherianRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- The original injective resolution has local finite-source Hom boundaries on each slice. -/
theorem locallyBoundary_injectiveResolution_of_constantTarget
    (N : ModuleSheaf.{c, h, max c h, max c h} J Λ)
    (Q : ModuleCat.{max c h} Λ) [Injective Q]
    (θ : (Functor.const Cᵒᵖ).obj Q ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J θ]
    [CategoryTheory.Presheaf.IsLocallyInjective J θ]
    (I : InjectiveResolution N) (U : C)
    (M₀ : ModuleCat.{max c h} Λ) [Module.Finite Λ M₀] (q : ℕ) :
    ModuleCat.Sheaf.LocallyBoundary (J.over U)
      (((moduleValuedOverFunctor J Λ U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex) M₀ q := by
  let F := moduleValuedOverFunctor J Λ U
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  let θU : (Functor.const (Over U)ᵒᵖ).obj Q ⟶ (F.obj N).obj :=
    Functor.whiskerLeft (Over.forget U).op θ
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) θU :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) θ
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) θU :=
    CategoryTheory.Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) θ
  let i : F.obj N ⟶ K.X 0 := F.map (I.ι.f 0)
  have hi : i ≫ K.d 0 1 = 0 := by
    change F.map (I.ι.f 0) ≫ F.map (I.cocomplex.d 0 1) = 0
    rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero]
  let : Mono i := by dsimp only [i]; infer_instance
  have hN : (ShortComplex.mk i (K.d 0 1) hi).Exact := I.exact₀.map F
  have hK (j : ℕ) : K.ExactAt (j + 1) := (I.cocomplex_exactAt_succ j).map F
  let : ∀ (j : ℕ) (V : Over U), Injective ((K.X j).obj.obj (op V)) := by
    intro j V
    change Injective (((sheafSections (J.over U) (ModuleCat.{max c h} Λ)).obj (op V)).obj
      (F.obj (I.cocomplex.X j)))
    infer_instance
  exact ModuleCat.Sheaf.locallyBoundary_finite_of_constantInjective
    (J.over U) K (F.obj N) Q θU i hi hN hK M₀ q

variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) RingCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective RingCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose
    (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]

set_option backward.isDefEq.respectTransparency false in
/-- Finite-type constant charts give exactness of original internal Hom in every positive degree. -/
theorem homFunctor_exactAt_of_finiteConstantCharts
    (M N : ModuleSheaf.{c, h, max c h, max c h} J Λ)
    (hM : ModuleCat.Sheaf.HasFiniteTypeConstantCharts J
      ((moduleSheafEquivalence J Λ).inverse.obj M))
    (Q : ModuleCat.{max c h} Λ) [Injective Q]
    (θ : (Functor.const Cᵒᵖ).obj Q ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J θ]
    [CategoryTheory.Presheaf.IsLocallyInjective J θ]
    (I : InjectiveResolution N) (q : ℕ) :
    (((SheafOfModules.InternalHom.homFunctor.{c, h, 0}
      (commutativeSheaf J Λ) M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).ExactAt (q + 1) := by
  let K := ((SheafOfModules.InternalHom.homFunctor.{c, h, 0}
    (commutativeSheaf J Λ) M).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  apply SheafOfModules.exactAt_of_local_boundaries K (q + 1)
  intro U x hx
  rw [CochainComplex.next] at hx
  change (K.d (q + 1) (q + 2)).val.app (op U) x = 0 at hx
  let T : Sieve U := {
    arrows V f := ∃ y : (K.X q).val.obj (op V),
      (K.d q (q + 1)).val.app (op V) y = (K.X (q + 1)).val.map f.op x
    downward_closed := by
      rintro V W f ⟨y, hy⟩ g
      refine ⟨(K.X q).val.map g.op y, ?_⟩
      rw [PresheafOfModules.naturality_apply, hy, ← PresheafOfModules.map_comp_apply,
        ← op_comp] }
  refine ⟨T, ?_, ?_⟩
  · apply J.transitive (hM U) T
    intro V f hf
    obtain ⟨M₀, hfinite, η, hsurj, hinj⟩ := hf
    let := hfinite
    let := hsurj
    let := hinj
    let xV : (K.X (q + 1)).val.obj (op V) := (K.X (q + 1)).val.map f.op x
    have hxV : (K.d (q + 1) (q + 2)).val.app (op V) xV = 0 := by
      dsimp only [xV]
      exact (PresheafOfModules.naturality_apply (K.d (q + 1) (q + 2)).val f.op x).trans
        ((congrArg (fun z : (K.X (q + 2)).val.obj (op U) =>
          ((K.X (q + 2)).val.map f.op z : (K.X (q + 2)).val.obj (op V))) hx).trans
            (map_zero _))
    obtain ⟨S, hS, h⟩ := exists_cover_boundary_of_presentation J Λ V M M₀ η I.cocomplex q
      (locallyBoundary_injectiveResolution_of_constantTarget J Λ N Q θ I V M₀ q) xV hxV
    apply J.superset_covering _ hS
    intro W g hg
    obtain ⟨y, hy⟩ := h g hg
    refine ⟨y, ?_⟩
    rw [op_comp, PresheafOfModules.map_comp_apply]
    exact hy
  · intro V f hf
    rw [CochainComplex.prev_nat_succ]
    exact hf

end ModuleCat.Sheaf.ConstantRing
