/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartExchangeMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartRelative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-! # Original higher exchange on arbitrary pointed neighborhood classes

Literal chart normalization and original global exchange give the section
equation after the target chart exchange. The target chart is etale, so its
original higher exchange can be cancelled. Taking the original germs then
gives the arbitrary-neighborhood equality with the original stalk unit,
pulled-back point and cohomology transfer.

The two chart cohomology groups use the common Ext universe required by
`Continuity.cohomologyTransfer`. The original and slice Ext universes and all
eight derived models remain independent. No Cartesian, properness or torsion
hypothesis is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe v

namespace CategoryTheory

/-- The original represented-section construction from its actual edge and equivalence. -/
def representedSectionHomOfEquiv
    {A : Type*} [AddCommGroup A] {P Q : AddCommGrpCat.{v}}
    (edge : P ⟶ Q) (resolution : A ≃+ P) : A →+ Q :=
  edge.hom.comp resolution.toAddMonoidHom

/-- The actual unit followed by its section-level coefficient map. -/
def unitSectionMapOfHom {A B C : AddCommGrpCat.{v}}
    (unit : A ⟶ B) (coefficient : B ⟶ C) : A ⟶ C :=
  unit ≫ coefficient

end CategoryTheory

private theorem iso_section_injective {A B : AddCommGrpCat.{v}} (e : A ≅ B)
    {x y : A} (h : e.hom x = e.hom y) : x = y :=
  (ConcreteCategory.congr_hom e.hom_inv_id x).symm.trans
    ((congrArg e.inv h).trans (ConcreteCategory.congr_hom e.hom_inv_id y))

private theorem addHom_eq_of_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A →+ B) (h : ∀ x, f x = g x) : f = g :=
  AddMonoidHom.ext h

private theorem originalChartHom_of_scalar
    {C : Type*} [Category* C] (Γ : C ⥤ AddCommGrpCat.{v})
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {U V : C} {P Q : AddCommGrpCat.{v}}
    (E : Γ.obj U ≅ Q) (β : U ⟶ V)
    (resolution : A ≃+ P) (edge : P ⟶ Q)
    (comparison : A ≃+ B) (higher : B →+ Γ.obj V)
    (h : ∀ x, Γ.map β (E.inv (edge (resolution x))) = higher (comparison x)) :
    (chartSectionMapOfHom Γ E β).hom.comp
        (representedSectionHomOfEquiv edge resolution) =
      higher.comp comparison.toAddMonoidHom := by
  exact AddMonoidHom.ext h

private theorem chartHom_normalize
    {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    (e : A ≃+ B) (s : A →+ C) (m : C →+ D) (t : B →+ D)
    (source : B →+ C) (hsource : source = s.comp e.symm.toAddMonoidHom)
    (h : m.comp s = t.comp e.toAddMonoidHom) : m.comp source = t := by
  subst source
  apply AddMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun h (e.symm x)
  exact hx.trans (congrArg t (e.apply_symm_apply x))

private theorem mapped_coefficient_hom
    {C : Type*} [Category* C] (Γ : C ⥤ AddCommGrpCat.{v})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    {P R T : Type*} [AddCommGroup P] [AddCommGroup R] [AddCommGroup T]
    (a : P →+ Γ.obj A) (b : R →+ Γ.obj B) (c : T →+ Γ.obj D)
    (r : P →+ R) (t : R →+ T)
    (hf : (Γ.map f).hom.comp a = b.comp r)
    (hg : (Γ.map g).hom.comp b = c.comp t) :
    (Γ.map (f ≫ g)).hom.comp a = c.comp (t.comp r) := by
  rw [Γ.map_comp]
  calc
    _ = (Γ.map g).hom.comp ((Γ.map f).hom.comp a) := rfl
    _ = (Γ.map g).hom.comp (b.comp r) := congrArg ((Γ.map g).hom.comp) hf
    _ = ((Γ.map g).hom.comp b).comp r := rfl
    _ = (c.comp t).comp r := congrArg (fun z => z.comp r) hg
    _ = _ := rfl

private theorem relative_square_reassociate
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {U V : C} {A B P W : D} (α : G.obj U ⟶ A) (k : A ⟶ B) (e : B ⟶ W)
    (b : U ⟶ V) (c : G.obj V ⟶ P) (r : P ⟶ W)
    (h : α ≫ k ≫ e = G.map b ≫ c ≫ r) :
    G.map b ≫ (c ≫ r) = (α ≫ k) ≫ e := by
  simpa only [Category.assoc] using h.symm

private theorem sectionMap_paste
    {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B)
    (ΓA : A ⥤ AddCommGrpCat.{v}) (ΓB : B ⥤ AddCommGrpCat.{v})
    (s : ΓA ⟶ G ⋙ ΓB) {U V : A} {Q W : B}
    (b : U ⟶ V) (c : G.obj V ⟶ W) (d : G.obj U ⟶ Q) (e : Q ⟶ W)
    (hsquare : G.map b ≫ c = d ≫ e)
    {Z T J : AddCommGrpCat.{v}} (EU : ΓA.obj U ≅ Z) (EV : ΓB.obj Q ≅ T)
    (u : Z ⟶ J) (v : J ⟶ T)
    (hpre : u ≫ v ≫ EV.inv = (EU.inv ≫ s.app U) ≫ ΓB.map d) :
    unitSectionMapOfHom u v ≫ chartSectionMapOfHom ΓB EV e =
      chartSectionMapOfHom ΓA EU b ≫ s.app V ≫ ΓB.map c := by
  dsimp only [unitSectionMapOfHom, chartSectionMapOfHom]
  have hn : ΓA.map b ≫ s.app V = s.app U ≫ ΓB.map (G.map b) := s.naturality b
  calc
    _ = (u ≫ v ≫ EV.inv) ≫ ΓB.map e := by simp only [Category.assoc]
    _ = ((EU.inv ≫ s.app U) ≫ ΓB.map d) ≫ ΓB.map e :=
      congrArg (fun z => z ≫ ΓB.map e) hpre
    _ = (EU.inv ≫ s.app U) ≫ ΓB.map (d ≫ e) := by rw [ΓB.map_comp, Category.assoc]
    _ = (EU.inv ≫ s.app U) ≫ ΓB.map (G.map b ≫ c) :=
      congrArg (fun z => (EU.inv ≫ s.app U) ≫ ΓB.map z) hsquare.symm
    _ = EU.inv ≫ (s.app U ≫ ΓB.map (G.map b)) ≫ ΓB.map c := by
      rw [ΓB.map_comp]; simp only [Category.assoc]
    _ = EU.inv ≫ (ΓA.map b ≫ s.app V) ≫ ΓB.map c :=
      congrArg (fun z => EU.inv ≫ z ≫ ΓB.map c) hn.symm
    _ = _ := by simp only [Category.assoc]

private theorem sectionHom_cancel
    {A B C D : AddCommGrpCat.{v}} (k : A ⟶ B) (a : A ⟶ C)
    (b : B ⟶ D) (c : C ⟶ D) [IsIso b]
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    (source : P →+ A) (target : R →+ B) (r : P →+ R)
    (sourceHigher : P →+ C) (targetHigher : R →+ D)
    (hsquare : k ≫ b = a ≫ c)
    (hsource : a.hom.comp source = sourceHigher)
    (hglobal : c.hom.comp sourceHigher = targetHigher.comp r)
    (htarget : b.hom.comp target = targetHigher) :
    k.hom.comp source = target.comp r := by
  have hh : b.hom.comp (k.hom.comp source) = b.hom.comp (target.comp r) := by
    calc
      _ = (k ≫ b).hom.comp source := rfl
      _ = (a ≫ c).hom.comp source := congrArg (fun z => z.hom.comp source) hsquare
      _ = c.hom.comp (a.hom.comp source) := rfl
      _ = c.hom.comp sourceHigher := congrArg c.hom.comp hsource
      _ = targetHigher.comp r := hglobal
      _ = (b.hom.comp target).comp r := congrArg (fun z => z.comp r) htarget.symm
      _ = _ := rfl
  apply AddMonoidHom.ext
  intro x
  exact iso_section_injective (asIso b) (DFunLike.congr_fun hh x)

private theorem germHom_of_sectionHom
    {A B C D E F : AddCommGrpCat.{v}}
    (a : A ⟶ B) (σ : B ⟶ D) (u : A ⟶ C) (b : C ⟶ E)
    (c : C ⟶ D) (β : D ⟶ F) (t : E ⟶ F) (k : A ⟶ E)
    (hk : k = u ≫ b) (hu : a ≫ σ = u ≫ c) (hn : c ≫ β = b ≫ t)
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    (source : P →+ A) (target : R →+ E) (r : P →+ R)
    (sourceGerm : P →+ B) (targetGerm : R →+ F)
    (hsource : sourceGerm = a.hom.comp source)
    (htarget : targetGerm = t.hom.comp target)
    (hsection : k.hom.comp source = target.comp r)
    (left right : P →+ F)
    (hleft : left = (σ ≫ β).hom.comp sourceGerm)
    (hright : right = targetGerm.comp r) : left = right := by
  subst left
  subst right
  have hd : a ≫ σ ≫ β = k ≫ t := by
    calc
      _ = (a ≫ σ) ≫ β := (Category.assoc _ _ _).symm
      _ = (u ≫ c) ≫ β := congrArg (fun z => z ≫ β) hu
      _ = u ≫ (c ≫ β) := Category.assoc _ _ _
      _ = u ≫ (b ≫ t) := congrArg (fun z => u ≫ z) hn
      _ = (u ≫ b) ≫ t := (Category.assoc _ _ _).symm
      _ = k ≫ t := congrArg (fun z => z ≫ t) hk.symm
  calc
    _ = (σ ≫ β).hom.comp (a.hom.comp source) := congrArg (σ ≫ β).hom.comp hsource
    _ = (a ≫ σ ≫ β).hom.comp source := rfl
    _ = (k ≫ t).hom.comp source := congrArg (fun z => z.hom.comp source) hd
    _ = t.hom.comp (k.hom.comp source) := rfl
    _ = t.hom.comp (target.comp r) := congrArg t.hom.comp hsection
    _ = (t.hom.comp target).comp r := rfl
    _ = _ := congrArg (fun z => z.comp r) htarget.symm

private theorem germHom_apply
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    {A B C : AddCommGrpCat.{v}} (σ : A ⟶ B) (β : B ⟶ C)
    (source : P →+ A) (target : R →+ C) (r : P →+ R)
    (h : (σ ≫ β).hom.comp source = target.comp r) (x : P) :
    β (σ (source x)) = target (r x) :=
  DFunLike.congr_fun h x

universe u w w' s s' e dX dS dX' dS' dZU dU dZV dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge


/-- Normalize the coefficient object before specializing its additive-group carrier. -/
private theorem chartScalar_comp_obj {X S Z : Scheme.{u}} (U : S.Etale)
    (P : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S)
    (K : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} Z)
    (R : AbelianSheaf.{u, u + 1} Z ⥤
      AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left))
    (α : P ⋙ @inverseImage.{u} S U.left U.hom ⟶ K ⋙ R)
    (α₀ : P ⋙ @inverseImage.{u} S ((𝟭 Scheme.{u}).obj U.left) U.hom ⟶ K ⋙ R)
    (hα : α = α₀) (F : AbelianSheaf.{u, u + 1} X) {T : Type*}
    (source : T → (P.obj F).obj.obj (op U))
    (target : T → (R.obj (K.obj F)).obj.obj
      (op (etaleTerminal ((𝟭 Scheme.{u}).obj U.left))))
    (h : ∀ x, @Eq ((globalSections U.left).obj ((K ⋙ R).obj F))
      ((globalSections U.left).map (α₀.app F)
        ((Continuity.pullbackSectionsEtaleEvaluationIso (P.obj F) U).inv (source x)))
      (target x)) (x : T) :
    @Eq ((globalSections U.left).obj (R.obj (K.obj F)))
      ((chartSectionMapOfHom (globalSections U.left)
        (Continuity.pullbackSectionsEtaleEvaluationIso (P.obj F) U) (α.app F)).hom
          (source x)) (target x) := by
  have hcomponent : α.app F = α₀.app F := NatTrans.congr_app hα F
  have hx := (congrArg
    (fun b => (globalSections U.left).map b
      ((Continuity.pullbackSectionsEtaleEvaluationIso (P.obj F) U).inv (source x)))
    hcomponent).trans (h x)
  simpa only [Functor.comp_obj, chartSectionMapOfHom, AddCommGrpCat.Hom.hom,
    ConcreteCategory.comp_apply] using hx

section ChartNormalization

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [hOriginalExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original resolution edge on represented cohomology as an additive map. -/
def originalCohomologySectionHom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      X.smallEtaleTopology F q ((siteBaseChange f).obj U) →+
        ((higherDirectImage f q).obj F).obj.obj (op U) :=
  representedSectionHomOfEquiv
    (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U))
    (originalCohomologyResolutionEquiv f U F q)

variable
  [hSliceExt : HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})]
  [hChart : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance neighborhoodChartNormalization_chartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hChart

local instance neighborhoodChartNormalization_chartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hChart

/-- The original resolution edge and original class comparisons as one additive map. -/
def fibreProductCohomologySectionHom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q →+
      ((higherDirectImage f q).obj F).obj.obj (op U) :=
  (originalCohomologySectionHom f U F q).comp
    (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
      hOriginalExt hSliceExt hChart F q).symm.toAddMonoidHom

/-- The section hom is exactly the original edge, resolution comparison and inverse
fibre-product class comparison, with their original additive structures. -/
theorem fibreProductCohomologySectionHom_eq_original
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductCohomologySectionHom.{u, w, s, e} f U F q =
      ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)).hom.comp
        (originalCohomologyResolutionEquiv f U F q).toAddMonoidHom).comp
          (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
            hOriginalExt hSliceExt hChart F q).symm.toAddMonoidHom := rfl

private theorem fibreProductGerm_eq_sectionHom
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U) :
    fibreProductCohomologyGerm.{u, w, s, e} f U F q η p =
      ((pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) := rfl

variable
  [hSourceDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hTargetDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hChartDerived : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hBase : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]

local instance neighborhoodChartNormalization_baseDerived : HasDerivedCategory.{dU}
    (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left)) := hBase

omit hOriginalExt hSliceExt hChart in
/-- Compare the original exchange values before taking a coefficient component. -/
private theorem originalChartExchange_value_eq_primitive (q : ℕ) :
    (@higherBaseChangeMap.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
      hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
      U.hom (pullback.snd U.hom f) pullback.condition q) =
    (@higherBaseChangeMap.{u, dX, dS, dZU, dU} X S (pullback U.hom f)
      ((𝟭 Scheme.{u}).obj U.left)
      hSourceDerived hTargetDerived hChartDerived
      (@baseChangeChartSections_targetIdentityHasDerivedCategory.{u, dU} S U hBase)
      f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f) pullback.condition q) := rfl

private theorem originalChartSection_hom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom.comp
        (originalCohomologySectionHom f U F q) =
      (cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q).comp
          (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
            hOriginalExt hSliceExt hChart F q).toAddMonoidHom := by
  apply addHom_eq_of_apply
  intro x
  simp only [AddMonoidHom.comp_apply]
  rw [fibreProductChartSectionMap_eq_constructor.{u, dX, dS, dZU, dU} f U
    (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
    (hChartDerived := hChartDerived) (hBase := hBase) F q]
  exact chartScalar_comp_obj U
    (@higherDirectImage.{u} X S f q)
    (@inverseImage.{u} X (pullback U.hom f) (pullback.snd U.hom f))
    (higherDirectImage (pullback.fst U.hom f) q)
    (@higherBaseChangeMap.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
      hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
      U.hom (pullback.snd U.hom f) pullback.condition q)
    (@higherBaseChangeMap.{u, dX, dS, dZU, dU} X S (pullback U.hom f)
      ((𝟭 Scheme.{u}).obj U.left)
      hSourceDerived hTargetDerived hChartDerived
      (@baseChangeChartSections_targetIdentityHasDerivedCategory.{u, dU} S U hBase)
      f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f) pullback.condition q)
    (originalChartExchange_value_eq_primitive f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) q) F
    (originalCohomologySectionHom f U F q)
    (fun z => cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q
        (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
          hOriginalExt hSliceExt hChart F q z))
    (@higherBaseChangeMap_originalChart.{u, w, s, e, dX, dS, dZU, dU}
      X S f U hOriginalExt hSliceExt hChart
      hSourceDerived hTargetDerived hChartDerived hBase F q) x

private theorem fibreProductChartSection_hom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q :=
  chartHom_normalize
    (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U hOriginalExt hSliceExt hChart F q)
    (originalCohomologySectionHom f U F q)
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom
    (cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q)
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) rfl
    (originalChartSection_hom.{u, w, s, e, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q)

end ChartNormalization

private theorem higherBaseChangeMap_coefficientSections_hom
    {X S Y T : Scheme.{u}}
    [hDomainExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [hCodomainExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    [hDomainDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [hDomainBaseDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [hCodomainDerived : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} Y)]
    [hCodomainBaseDerived : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} T)]
    (f : X ⟶ S) (fT : Y ⟶ T) (b : T ⟶ S) (r : Y ⟶ X)
    (h : fT ≫ b = r ≫ f) (F : AbelianSheaf.{u, u + 1} X)
    (G : AbelianSheaf.{u, u + 1} Y) (φ : (inverseImage r).obj F ⟶ G) (q : ℕ) :
    (globalSectionsPullback b ((higherDirectImage f q).obj F) ≫
      (globalSections T).map
        ((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S Y T
          hDomainDerived hDomainBaseDerived hCodomainDerived hCodomainBaseDerived
          f fT b r h q).app F ≫
          (higherDirectImage fT q).map φ)).hom.comp (cohomologyToHigherSections f F q) =
      (cohomologyToHigherSections fT G q).comp
        ((Sheaf.H.map φ q).comp (cohomologyPullback.{u, w, w'} r F q)) := by
  let Γ : AbelianSheaf.{u, u + 1} T ⥤ AddCommGrpCat.{u + 1} := globalSections T
  let β : (inverseImage b).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage fT q).obj ((inverseImage r).obj F) :=
    (@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S Y T
    hDomainDerived hDomainBaseDerived hCodomainDerived hCodomainBaseDerived f fT b r h q).app F
  have hs : (Γ.map β).hom.comp
      ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
        (cohomologyToHigherSections f F q)) =
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q).comp
        (cohomologyPullback.{u, w, w'} r F q) :=
    addHom_eq_of_apply _ _
      (@higherBaseChangeMap_cohomologyToHigherSections.{u, w, w', dX, dS, dX', dS'}
        X S Y T hDomainExt hCodomainExt
        hDomainDerived hDomainBaseDerived hCodomainDerived hCodomainBaseDerived f fT b r h F q)
  have ht : (Γ.map ((higherDirectImage fT q).map φ)).hom.comp
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q) =
      (cohomologyToHigherSections fT G q).comp (Sheaf.H.map φ q) :=
    addHom_eq_of_apply _ _ (cohomologyToHigherSections_naturality fT φ q)
  exact mapped_coefficient_hom Γ β ((higherDirectImage fT q).map φ)
    ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
      (cohomologyToHigherSections f F q))
    (cohomologyToHigherSections fT ((inverseImage r).obj F) q)
    (cohomologyToHigherSections fT G q) (cohomologyPullback.{u, w, w'} r F q)
    (Sheaf.H.map φ q) hs ht

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (U : S.Etale)

variable
  [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hX'Ext : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlice : HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})]
  [hTargetSlice : HasExt.{s'} (Sheaf ((Scheme.smallEtaleTopology X').over
    ((siteBaseChange f').obj ((siteBaseChange g).obj U)))
    AddCommGrpCat.{u + 1})]
  [hZU : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hZV : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  [hDX : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hDS : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hDX' : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hDS' : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [hDZU : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hDU : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
  [hDZV : HasDerivedCategory.{dZV}
    (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  [hDV : HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} ((siteBaseChange g).obj U).left)]

local instance neighborhoodBaseChange_sourceBaseIdentityHasDerivedCategory :
    HasDerivedCategory.{dU}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left)) := hDU

local instance neighborhoodBaseChange_targetBaseIdentityHasDerivedCategory :
    HasDerivedCategory.{dV}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj ((siteBaseChange g).obj U).left)) := hDV

local instance neighborhoodBaseChange_sourceChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hZU

local instance neighborhoodBaseChange_sourceChartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hZU

local instance neighborhoodBaseChange_targetChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f').obj ((siteBaseChange g).obj U)).left) := hZV

local instance neighborhoodBaseChange_targetChartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj
      ((siteBaseChange f').obj ((siteBaseChange g).obj U)).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hZV

section SectionMaps

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV

section OriginalMap

omit hDZU hDU hDZV hDV

/-- The complete original unit-and-higher-exchange map at the original section carriers. -/
def fibreProductBaseChangeSectionMap (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    ((higherDirectImage f q).obj F).obj.obj (op U) ⟶
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)).obj.obj
        (op ((siteBaseChange g).obj U)) :=
  unitSectionMapOfHom
    (((inverseImageAdjunction g).unit.app ((higherDirectImage f q).obj F)).hom.app (op U))
    (((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F).hom.app (op ((siteBaseChange g).obj U)))

/-- This is literally the original unit followed by the original higher exchange. -/
theorem fibreProductBaseChangeSectionMap_eq_original
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q =
      ((inverseImageAdjunction g).unit.app ((higherDirectImage f q).obj F)).hom.app (op U) ≫
        ((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F).hom.app
          (op ((siteBaseChange g).obj U)) := rfl

end OriginalMap

private theorem higherBaseChangeMap_sectionChart_square
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q ≫
        fibreProductChartSectionMap.{u, dX', dS', dZV, dV}
          f' ((siteBaseChange g).obj U)
          (hSourceDerived := hDX') (hTargetDerived := hDS')
          (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q =
      fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q ≫
        globalSectionsPullback (pullback.fst U.hom g)
          ((higherDirectImage (pullback.fst U.hom f) q).obj
            ((inverseImage (pullback.snd U.hom f)).obj F)) ≫
        (globalSections ((siteBaseChange g).obj U).left).map
          ((@higherBaseChangeMap.{u, dZU, dU, dZV, dV}
            (pullback U.hom f) U.left
            (pullback ((siteBaseChange g).obj U).hom f') ((siteBaseChange g).obj U).left
            hDZU hDU hDZV hDV (pullback.fst U.hom f)
            (pullback.fst ((siteBaseChange g).obj U).hom f')
            (pullback.fst U.hom g) (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_fst f f' g g' h U).symm q).app
              ((inverseImage (pullback.snd U.hom f)).obj F) ≫
            (higherDirectImage (pullback.fst ((siteBaseChange g).obj U).hom f') q).map
              ((inverseImageSquareIso (pullback.snd U.hom f)
                (pullback.snd ((siteBaseChange g).obj U).hom f') g'
                (fibreProductBaseChangeMap f f' g g' h U)
                (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F)) := by
  rw [fibreProductChartSectionMap_eq_constructor.{u, dX', dS', dZV, dV}
    f' ((siteBaseChange g).obj U)
    (hSourceDerived := hDX') (hTargetDerived := hDS')
    (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q,
    fibreProductChartSectionMap_eq_constructor.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q]
  let V : S'.Etale := (siteBaseChange g).obj U
  let fU : pullback U.hom f ⟶ U.left := pullback.fst U.hom f
  let fV : pullback V.hom f' ⟶ V.left := pullback.fst V.hom f'
  let piU := pullback.snd U.hom f
  let piV := pullback.snd V.hom f'
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  let rU : pullback V.hom f' ⟶ pullback U.hom f :=
    fibreProductBaseChangeMap f f' g g' h U
  let hrU : piV ≫ g' = rU ≫ piU := (fibreProductBaseChangeMap_snd f f' g g' h U).symm
  let hR : fV ≫ b = rU ≫ fU := (fibreProductBaseChangeMap_fst f f' g g' h U).symm
  let L := (higherDirectImage f q).obj F
  let G := (inverseImage g').obj F
  let L' := (higherDirectImage f' q).obj G
  let β : (inverseImage g).obj L ⟶ L' :=
    (@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F
  let βU : (inverseImage U.hom).obj L ⟶
      (higherDirectImage fU q).obj ((inverseImage piU).obj F) :=
    (@higherBaseChangeMap.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
      hDX hDS hDZU hDU f fU U.hom piU pullback.condition q).app F
  let βV : (inverseImage V.hom).obj L' ⟶
      (higherDirectImage fV q).obj ((inverseImage piV).obj G) :=
    (@higherBaseChangeMap.{u, dX', dS', dZV, dV} X' S' (pullback V.hom f') V.left
      hDX' hDS' hDZV hDV f' fV V.hom piV pullback.condition q).app G
  let βR : (inverseImage b).obj ((higherDirectImage fU q).obj ((inverseImage piU).obj F)) ⟶
      (higherDirectImage fV q).obj ((inverseImage rU).obj ((inverseImage piU).obj F)) :=
    (@higherBaseChangeMap.{u, dZU, dU, dZV, dV}
      (pullback U.hom f) U.left (pullback V.hom f') V.left
      hDZU hDU hDZV hDV fU fV b rU hR q).app ((inverseImage piU).obj F)
  let δ : (inverseImage rU).obj ((inverseImage piU).obj F) ⟶
      (inverseImage piV).obj G := (inverseImageSquareIso piU piV g' rU hrU).inv.app F
  let δS : (inverseImage b).obj ((inverseImage U.hom).obj L) ⟶
      (inverseImage V.hom).obj ((inverseImage g).obj L) :=
    (inverseImageSquareIso U.hom V.hom g b pullback.condition.symm).inv.app L
  have hrel := @higherBaseChangeMap_chartRelative_square.{u, dX, dS, dX', dS', dZU, dU, dZV, dV}
    X S X' S' (pullback U.hom f) U.left (pullback V.hom f') V.left
    hDX hDS hDX' hDS' hDZU hDU hDZV hDV f f' g g' h fU fV U.hom V.hom piU piV b rU
    pullback.condition pullback.condition pullback.condition.symm hrU hR q F
  have hsquare := relative_square_reassociate (inverseImage b) δS
    ((inverseImage V.hom).map β) βV βU βR ((higherDirectImage fV q).map δ) hrel
  exact sectionMap_paste (inverseImage b) (globalSections U.left) (globalSections V.left)
    (globalSectionsPullbackNatTrans b) βU (βR ≫ (higherDirectImage fV q).map δ)
    (δS ≫ (inverseImage V.hom).map β) βV hsquare
    (Continuity.pullbackSectionsEtaleEvaluationIso L U)
    (Continuity.pullbackSectionsEtaleEvaluationIso L' V)
    (((inverseImageAdjunction g).unit.app L).hom.app (op U)) (β.hom.app (op V))
    (unitSectionMap_baseChangeChart_coefficient g U β)

end SectionMaps

-- Allow finite extra elaboration for this eight-model native specialization.
-- Its comparisons and cancellation are equalities of whole additive maps.
set_option maxHeartbeats 500000 in
private theorem higherBaseChangeMap_fibreProductSection_whole
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      (fibreProductCohomologySectionHom.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom := by
  let V : S'.Etale := (siteBaseChange g).obj U
  let fU := pullback.fst U.hom f
  let fV := pullback.fst V.hom f'
  let piU := pullback.snd U.hom f
  let piV := pullback.snd V.hom f'
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  let rU := fibreProductBaseChangeMap f f' g g' h U
  let hR := (fibreProductBaseChangeMap_fst f f' g g' h U).symm
  let δ : (inverseImage rU).obj ((inverseImage piU).obj F) ⟶
      (inverseImage piV).obj ((inverseImage g').obj F) :=
    (inverseImageSquareIso piU piV g' rU
    (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F
  let G := (inverseImage g').obj F
  let βR : (inverseImage b).obj ((higherDirectImage fU q).obj ((inverseImage piU).obj F)) ⟶
      (higherDirectImage fV q).obj ((inverseImage rU).obj ((inverseImage piU).obj F)) :=
    (@higherBaseChangeMap.{u, dZU, dU, dZV, dV}
    (pullback U.hom f) U.left (pullback V.hom f') V.left
    hDZU hDU hDZV hDV fU fV b rU hR q).app
    ((inverseImage piU).obj F)
  have : IsIso (fibreProductChartSectionMap.{u, dX', dS', dZV, dV} f' V
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) G q) :=
    fibreProductChartSectionMap_isIso.{u, dX', dS', dZV, dV} f' V
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) G q
  exact sectionHom_cancel
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q)
    (fibreProductChartSectionMap.{u, dX', dS', dZV, dV} f' V
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) G q)
    (globalSectionsPullback b ((higherDirectImage fU q).obj ((inverseImage piU).obj F)) ≫
      (globalSections V.left).map (βR ≫ (higherDirectImage fV q).map δ))
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q)
    (fibreProductCohomologySectionHom.{u, w', s', e} f' V G q)
    (Continuity.cohomologyTransfer.{u, e} rU δ q).hom
    (cohomologyToHigherSections fU ((inverseImage piU).obj F) q)
    (cohomologyToHigherSections fV ((inverseImage piV).obj G) q)
    (higherBaseChangeMap_sectionChart_square.{u, dX, dS, dX', dS', dZU, dU, dZV, dV}
      f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q)
    (fibreProductChartSection_hom.{u, w, s, e, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q)
    (higherBaseChangeMap_coefficientSections_hom.{u, e, e, dZU, dU, dZV, dV}
      (hDomainExt := hZU) (hCodomainExt := hZV)
      (hDomainDerived := hDZU) (hDomainBaseDerived := hDU)
      (hCodomainDerived := hDZV) (hCodomainBaseDerived := hDV)
      fU fV b rU hR ((inverseImage piU).obj F) ((inverseImage piV).obj G) δ q)
    (fibreProductChartSection_hom.{u, w', s', e, dX', dS', dZV, dV} f' V
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) G q)

/-- The original unit-and-exchange section map commutes with the exact original
coefficient-square cohomology transfer as an equality of additive maps. -/
theorem higherBaseChangeMap_fibreProductSection
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      (fibreProductCohomologySectionHom.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom :=
  higherBaseChangeMap_fibreProductSection_whole.{u, w, w', s, s', e,
    dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
    (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
    (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q

private theorem higherBaseChangeMap_fibreProductGerm_hom
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U) :
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F) ≫
      (pointSmallEtale ζ).sheafFiber.map
        ((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F)).hom.comp
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p) =
      (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q ζ
        (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom := by
  let V : S'.Etale := (siteBaseChange g).obj U
  let L := (higherDirectImage f q).obj F
  let G := (inverseImage g').obj F
  let L' := (higherDirectImage f' q).obj G
  let β : (inverseImage g).obj L ⟶ L' :=
    (@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F
  let p' := CoefficientStalkBaseChange.pulledBackPoint g ζ U p
  exact germHom_of_sectionHom
    ((pointSmallEtale (ζ ≫ g)).toPresheafFiber U p L.obj)
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F))
    (((inverseImageAdjunction g).unit.app L).hom.app (op U)) (β.hom.app (op V))
    ((pointSmallEtale ζ).toPresheafFiber V p' ((inverseImage g).obj L).obj)
    ((pointSmallEtale ζ).sheafFiber.map
      ((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F))
    ((pointSmallEtale ζ).toPresheafFiber V p' L'.obj)
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (fibreProductBaseChangeSectionMap_eq_original.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (StalkInverseImage.germ_stalkUnitNatIso g ζ L U p)
    ((pointSmallEtale ζ).toPresheafFiber_naturality β.hom V p')
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q)
    (fibreProductCohomologySectionHom.{u, w', s', e} f' V G q)
    (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom
    (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (fibreProductGerm_eq_sectionHom.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductGerm_eq_sectionHom.{u, w', s', e} f' V G q ζ p')
    (higherBaseChangeMap_fibreProductSection.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q)
    (((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F) ≫
      (pointSmallEtale ζ).sheafFiber.map
        ((@higherBaseChangeMap.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F)).hom.comp
            (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p))
    ((fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ
      (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)).comp
        (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
          ((inverseImageSquareIso (pullback.snd U.hom f)
            (pullback.snd ((siteBaseChange g).obj U).hom f') g'
            (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom) rfl rfl

/-- The original arbitrary-neighborhood germ exchange, retaining its original
stalk unit, actual pulled-back point and exact coefficient-square transfer. -/
theorem higherBaseChangeMap_fibreProductCohomologyGerm
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (pointSmallEtale ζ).sheafFiber.map
        ((higherBaseChangeMap.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y)) =
      fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q ζ
        (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
        (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
          ((inverseImageSquareIso (pullback.snd U.hom f)
            (pullback.snd ((siteBaseChange g).obj U).hom f')
            g' (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y) := by
  exact germHom_apply
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F))
    ((pointSmallEtale ζ).sheafFiber.map
      ((higherBaseChangeMap.{u, dX, dS, dX', dS'} f f' g g' h q).app F))
    (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom
    (higherBaseChangeMap_fibreProductGerm_hom.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q ζ p) y

end AlgebraicGeometry.Scheme.EtaleCohomology
