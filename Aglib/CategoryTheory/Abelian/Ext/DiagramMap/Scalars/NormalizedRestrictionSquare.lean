/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.RestrictionSquare
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.NormalizedRestrictionMap
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.TopComparison
public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer.SourceNaturality

/-! # The complete original normalized scalar Ext restriction square

The same original raw restriction square and source top comparison are
assembled before specialization. Their lower arrows are identified at this
variable-source layer, and the resulting square has the original global mate
as its literal lower edge. No additional cohomology or joint-data model is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ChangeOfRings TensorProduct

namespace CategoryTheory.Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ i₀ j₀ i₁ j₁ i₂ j₂ i₃ j₃ r w

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{max r w} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{max r w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{max r w} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{max r w} C₃]
  {I₀ : Type i₀} [Category.{j₀} I₀] {I₁ : Type i₁} [Category.{j₁} I₁]
  {I₂ : Type i₂} [Category.{j₂} I₂] {I₃ : Type i₃} [Category.{j₃} I₃]
  (Lp : C₀ ⥤ C₁) [Lp.Additive] [PreservesFiniteLimits Lp] [PreservesFiniteColimits Lp]
  (La : C₁ ⥤ C₃) [La.Additive] [PreservesFiniteLimits La] [PreservesFiniteColimits La]
  (Lj : C₀ ⥤ C₂) [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
  (Lb : C₂ ⥤ C₃) [Lb.Additive] [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
  (F₀ : I₀ ⥤ C₀) (F₁ : I₁ ⥤ C₁) (F₂ : I₂ ⥤ C₂) (F₃ : I₃ ⥤ C₃)
  (Hp : I₀ ⥤ I₁) (Ha : I₁ ⥤ I₃) (Hj : I₀ ⥤ I₂) (Hb : I₂ ⥤ I₃)
  (ep : F₀ ⋙ Lp ≅ Hp ⋙ F₁) (ea : F₁ ⋙ La ≅ Ha ⋙ F₃)
  (ej : F₀ ⋙ Lj ≅ Hj ⋙ F₂) (eb : F₂ ⋙ Lb ≅ Hb ⋙ F₃)
  {A₀ : C₀} {A₁ : C₁} {A₂ : C₂} {A₃ : C₃}
  (φp : Lp.obj A₀ ⟶ A₁) (φa : La.obj A₁ ⟶ A₃)
  (φj : Lj.obj A₀ ⟶ A₂) (φb : Lb.obj A₂ ⟶ A₃) (n : ℕ)
  {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
  (ρ₀ : R →+* End A₀) (ρ₁ : S →+* End A₁)
  (ρ₂ : R →+* End A₂) (ρ₃ : S →+* End A₃)
  (hp : ∀ a : R, Lp.map (ρ₀ a) ≫ φp = φp ≫ ρ₁ (σ a))
  (ha : ∀ a : S, La.map (ρ₁ a) ≫ φa = φa ≫ ρ₃ a)
  (hj : ∀ a : R, Lj.map (ρ₀ a) ≫ φj = φj ≫ ρ₂ a)
  (hb : ∀ a : R, Lb.map (ρ₂ a) ≫ φb = φb ≫ ρ₃ (σ a))
  (τ : ∀ i : I₀ᵒᵖ, Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj (Hj.op.obj i))
  (i : I₀ᵒᵖ) {d : I₂ᵒᵖ} (κJ : Hj.op.obj i ⟶ d)
  (κA : Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj d)
  (hk : τ i ≫ Hb.op.map κJ = κA)
  (h : ∀ v,
    ((Lp.extDiagramMap F₀ (Hp ⋙ F₁) ep φp n).app v ≫
      (La.extDiagramMap F₁ (Ha ⋙ F₃) ea φa n).app (Hp.op.obj v)) ≫
        ((F₃.op ⋙ extFunctor.{max r w} n).flip.obj A₃).map (τ v) =
    (Lj.extDiagramMap F₀ (Hj ⋙ F₂) ej φj n).app v ≫
      (Lb.extDiagramMap F₂ (Hb ⋙ F₃) eb φb n).app (Hj.op.obj v))

variable {Z₂ : C₂} {Z₃ : C₃}
  (e₂ : F₂.obj d.unop ≅ Z₂) (e₃ : F₃.obj (Hb.op.obj d).unop ≅ Z₃)
  (sg : Z₃ ⟶ Lb.obj Z₂)
  (hc : e₃.inv ≫ eb.inv.app d.unop = sg ≫ Lb.map e₂.inv)

/-- Normalize the original additive square at the original global sources,
then perform scalar extension once on that complete square. -/
def extScalarNormalizedRestrictionSquare : Square (ModuleCat.{max r w} S) := by
  let s := Lp.extDiagramRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb ep ea ej eb
    φp φa φj φb n τ i κJ κA hk h
  let C := F₂.extModuleDiagram A₂ ρ₂ n
  let E := (𝟭 C₂).extModuleDiagram A₂ ρ₂ n
  let jA := ((F₂.op ⋙ extFunctor.{max r w} n).flip.obj A₂).map κJ
  let eA := (((extFunctor.{max r w} n).mapIso e₂.op).app A₂).symm
  let eB := (((extFunctor.{max r w} n).mapIso e₃.op).app A₃).symm
  let g := AddCommGrpCat.ofHom (Lb.extCoefficientTransfer sg φb n)
  have ht : (Lb.extDiagramMap F₂ (Hb ⋙ F₃) eb φb n).app d ≫ eB.hom = eA.hom ≫ g := by
    ext x
    change Ext.{max r w} (F₂.obj d.unop) A₂ n at x
    exact Lb.extCoefficientTransfer_source_naturality e₂.inv e₃.inv
      (eb.inv.app d.unop) sg hc φb n x
  have hb' : s.f₃₄ ≫ eB.hom = (jA ≫ eA.hom) ≫ g :=
    (Category.assoc jA _ _).trans
      ((congrArg (fun f => jA ≫ f) ht).trans (Category.assoc _ _ _).symm)
  let t : Square AddCommGrpCat.{max r w} :=
    { X₁ := s.X₁, X₂ := s.X₂
      X₃ := AddCommGrpCat.of (Ext.{max r w} Z₂ A₂ n)
      X₄ := AddCommGrpCat.of (Ext.{max r w} Z₃ A₃ n)
      f₁₂ := s.f₁₂
      f₁₃ := s.f₁₃ ≫ jA ≫ eA.hom
      f₂₄ := s.f₂₄ ≫ eB.hom
      f₃₄ := g
      fac := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ eB.hom) s.fac).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => s.f₁₃ ≫ f) hb').trans
              (Category.assoc _ _ _).symm))) }
  let l := (Lj.extScalarDiagramMap F₀ F₂ Hj ej (RingHom.id R) A₀ A₂ ρ₀ ρ₂ φj hj n).app i ≫
    (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κJ) ≫
    (ModuleCat.restrictScalars (RingHom.id R)).map (E.map e₂.inv.op)
  let r := La.extScalarNormalizedRestrictionMap F₁ F₃ Ha ea A₁ A₃ ρ₁ ρ₃ φa ha n
    (Hp.op.obj i) κA e₃
  let bg := Lb.extScalarSourceMap σ A₂ A₃ ρ₂ ρ₃ φb hb n sg
  letI : Module R (Ext.{max r w} Z₂ A₂ n) :=
    (𝟭 C₂).extCoefficientModule A₂ ρ₂ n (op Z₂)
  letI : Module S (Ext.{max r w} Z₃ A₃ n) :=
    (𝟭 C₃).extCoefficientModule A₃ ρ₃ n (op Z₃)
  let scalarSquare : Square (ModuleCat.{max r w} S) := by
    refine ModuleCat.extendAdditiveSquare σ t
      (F₀.extCoefficientModule A₀ ρ₀ n i)
      (F₁.extCoefficientModule A₁ ρ₁ n (Hp.op.obj i))
      ((𝟭 C₂).extCoefficientModule A₂ ρ₂ n (op Z₂))
      ((𝟭 C₃).extCoefficientModule A₃ ρ₃ n (op Z₃)) ?_ ?_ ?_ ?_
    · intro a x
      exact Lp.extCoefficientTransfer_smul F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n i a x
    · intro a x
      exact l.hom.map_smul a x
    · intro a x
      exact r.hom.map_smul a x
    · intro a x
      change Ext.{max r w} Z₂ A₂ n at x
      exact (Lb.extScalarSourceMap_apply σ A₂ A₃ ρ₂ ρ₃ φb hb n sg (a • x)).symm.trans
        ((bg.hom.map_smul a x).trans
          (congrArg (fun y => σ a • y)
            (Lb.extScalarSourceMap_apply σ A₂ A₃ ρ₂ ρ₃ φb hb n sg x)))
  exact { scalarSquare with
    f₂₄ := r
    fac := scalarSquare.fac }


/-- The upper edge remains the original whole-diagram scalar mate. -/
theorem extScalarNormalizedRestrictionSquare_top :
    (Lp.extScalarNormalizedRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb
      ep ea ej eb φp φa φj φb n
      (σ := σ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
      (hp := hp) (ha := ha) (hj := hj) (hb := hb)
      (τ := τ) (i := i) (κJ := κJ) (κA := κA) (hk := hk) (h := h)
      (e₂ := e₂) (e₃ := e₃) (sg := sg) (hc := hc)).f₁₂ =
      (Lp.extScalarTensorDiagramMap F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n).app i := by
  exact (CategoryTheory.Adjunction.whiskerRight_homEquiv_symm_app
    (ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ)
    (F₀.extModuleDiagram A₀ ρ₀ n) (Hp.op ⋙ F₁.extModuleDiagram A₁ ρ₁ n)
    (Lp.extScalarDiagramMap F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n) i).symm

/-- The lower edge is the same original source-transfer scalar mate. -/
theorem extScalarNormalizedRestrictionSquare_bottom :
    (Lp.extScalarNormalizedRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb
      ep ea ej eb φp φa φj φb n
      (σ := σ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
      (hp := hp) (ha := ha) (hj := hj) (hb := hb)
      (τ := τ) (i := i) (κJ := κJ) (κA := κA) (hk := hk) (h := h)
      (e₂ := e₂) (e₃ := e₃) (sg := sg) (hc := hc)).f₃₄ =
      Lb.extScalarSourceMate σ A₂ A₃ ρ₂ ρ₃ φb hb n sg := by
  let : Module R (Ext.{max r w} Z₂ A₂ n) :=
    (𝟭 C₂).extCoefficientModule A₂ ρ₂ n (op Z₂)
  let : Module S (Ext.{max r w} Z₃ A₃ n) :=
    (𝟭 C₃).extCoefficientModule A₃ ρ₃ n (op Z₃)
  let : Module R (Ext.{max r w} Z₃ A₃ n) := Module.compHom _ σ
  apply congrArg ((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).homEquiv _ _).symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Ext.{max r w} Z₂ A₂ n at x
  exact (Lb.extScalarSourceMap_apply σ A₂ A₃ ρ₂ ρ₃ φb hb n sg x).symm

/-- The normalized left edge retains the original source index and source iso. -/
theorem extScalarNormalizedRestrictionSquare_left :
    (Lp.extScalarNormalizedRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb
      ep ea ej eb φp φa φj φb n
      (σ := σ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
      (hp := hp) (ha := ha) (hj := hj) (hb := hb)
      (τ := τ) (i := i) (κJ := κJ) (κA := κA) (hk := hk) (h := h)
      (e₂ := e₂) (e₃ := e₃) (sg := sg) (hc := hc)).f₁₃ =
      (ModuleCat.extendScalars σ).map
        ((Lj.extScalarDiagramMap F₀ F₂ Hj ej (RingHom.id R) A₀ A₂ ρ₀ ρ₂ φj hj n).app i ≫
          (ModuleCat.restrictScalars (RingHom.id R)).map
            ((F₂.extModuleDiagram A₂ ρ₂ n).map κJ) ≫
          (ModuleCat.restrictScalars (RingHom.id R)).map
            (((𝟭 C₂).extModuleDiagram A₂ ρ₂ n).map e₂.inv.op)) := rfl

/-- The normalized right edge retains the original target index and target iso. -/
theorem extScalarNormalizedRestrictionSquare_right :
    (Lp.extScalarNormalizedRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb
      ep ea ej eb φp φa φj φb n
      (σ := σ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
      (hp := hp) (ha := ha) (hj := hj) (hb := hb)
      (τ := τ) (i := i) (κJ := κJ) (κA := κA) (hk := hk) (h := h)
      (e₂ := e₂) (e₃ := e₃) (sg := sg) (hc := hc)).f₂₄ =
      (La.extScalarDiagramMap F₁ F₃ Ha ea (RingHom.id S) A₁ A₃ ρ₁ ρ₃ φa ha n).app
          (Hp.op.obj i) ≫
        (ModuleCat.restrictScalars (RingHom.id S)).map
          ((F₃.extModuleDiagram A₃ ρ₃ n).map κA) ≫
        (ModuleCat.restrictScalars (RingHom.id S)).map
          (((𝟭 C₃).extModuleDiagram A₃ ρ₃ n).map e₃.inv.op) := rfl

end CategoryTheory.Functor
