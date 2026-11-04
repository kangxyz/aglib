/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived.Connecting
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.SingleAdjunct
public import Aglib.CategoryTheory.Adjunction.ShiftedHom
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv.Composition
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleShiftHomology

/-!
# Original derived adjuncts and higher-image sections

The actual right-derived single unit, the original injective-resolution cycle, and the
original integer-source adjunction identify the H¹ map of the source-shifted derived adjunct.
The comparison retains the independent Ext and derived-category universes and uses no
properness or injectivity of the global-cohomology edge map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Adjunction

universe u₀ v₀ u₁ v₁ u₂ v₂

private theorem homEquiv_leftAdjointCompIso_hom
    {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂]
    {K : C₀ ⥤ C₁} {Γ : C₁ ⥤ C₀} {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁}
    {K' : C₀ ⥤ C₂} {Δ : C₂ ⥤ C₀}
    (a₀ : K ⊣ Γ) (a₁ : L ⊣ R) (a₂ : K' ⊣ Δ) (e : R ⋙ Γ ≅ Δ)
    {M : C₀} {N : C₂} (f : K'.obj M ⟶ N) :
    (a₀.comp a₁).homEquiv M N ((leftAdjointCompIso a₀ a₁ a₂ e).hom.app M ≫ f) =
      a₂.homEquiv M N f ≫ e.inv.app N := by
  let c := leftAdjointCompIso a₀ a₁ a₂ e
  have h := CategoryTheory.homEquiv_conjugate (a₀.comp a₁) a₂ c.inv (c.hom.app M ≫ f)
  rw [show conjugateEquiv (a₀.comp a₁) a₂ c.inv = e.hom from
    conjugateEquiv_leftAdjointCompIso_inv a₀ a₁ a₂ e] at h
  simp only [Iso.inv_hom_id_app_assoc] at h
  apply (cancel_mono (e.hom.app N)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact h.symm

universe t

private theorem integerHomSectionsAdjunct
    {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    {K : AddCommGrpCat.{t} ⥤ A} {Γ : A ⥤ AddCommGrpCat.{t}}
    {L : A ⥤ B} {R : B ⥤ A}
    {K' : AddCommGrpCat.{t} ⥤ B} {Δ : B ⥤ AddCommGrpCat.{t}}
    [K.Additive] [K'.Additive]
    (a₀ : K ⊣ Γ) (a₁ : L ⊣ R) (a₂ : K' ⊣ Δ) (e : R ⋙ Γ ≅ Δ)
    {N : B} (f : K'.obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ N) :
    integerHomSectionsAddEquiv a₀ (R.obj N)
      (a₁.homEquiv _ N
        ((leftAdjointCompIso a₀ a₁ a₂ e).hom.app (AddCommGrpCat.of (ULift.{t} ℤ)) ≫ f)) =
      e.inv.app N (integerHomSectionsAddEquiv a₂ N f) := by
  have h := homEquiv_leftAdjointCompIso_hom a₀ a₁ a₂ e f
  rw [Adjunction.comp_homEquiv] at h
  exact ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
attribute [local instance] hasSheafifyLarge

/-- The actual constant-source adjunct evaluates to the original inverse terminal transport. -/
private theorem constantIntegerAdjunct_sections {X S : Scheme.{u}} (p : X ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X)
    (a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    (constantIntegerHomGlobalSectionsIso S).hom.app ((directImage p).obj F)
      ((inverseImageAdjunction p).homEquiv _ F
        (((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a)) =
    (directImageGlobalSectionsIso p).inv.app F
      ((constantIntegerHomGlobalSectionsIso X).hom.app F a) := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have h := Adjunction.integerHomSectionsAdjunct
    (constantAdjunction S) (inverseImageAdjunction p) (constantAdjunction X)
    (directImageGlobalSectionsIso p) a
  change Adjunction.integerHomSectionsAddEquiv (constantAdjunction S)
      ((directImage p).obj F)
      ((inverseImageAdjunction p).homEquiv _ F
        ((inverseImageConstantCanonicalIso p).hom.app Z ≫ a)) =
    (directImageGlobalSectionsIso p).inv.app F
      (Adjunction.integerHomSectionsAddEquiv (constantAdjunction X) F a) at h
  rw [inverseImageConstantCanonicalIso_eq] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace CategoryTheory.InjectiveResolution

universe u v e d u' v' d'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]
    [EnoughInjectives C] [HasExt.{e} C]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{d'} B]
    (F : C ⥤ B) [F.Additive]

/-- The original cycle projects to the original right-derived object through its original iso. -/
private theorem derivedUnit_cocycle_rightDerived
    {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (f : M ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    let H := DerivedCategory.Plus.homologyFunctor B 0
    let c := Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf
    let a : Ext.{e} M N n := I.extEquivCohomologyClass.symm (.mk c)
    let K := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
      H.shiftMap (F.rightDerivedSingleUnit M ≫ a.homPlus.map F.rightDerivedFunctorPlus)
        0 (n : ℤ) (by omega) ≫
      (F.rightDerivedSingleHomologyIso n).inv.app N =
    K.liftCycles (F.map f) ((n : ℤ) + 1) (by simp)
      (by
        change F.map f ≫ F.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0
        rw [← F.map_comp, hf, F.map_zero]) ≫ K.homologyπ (n : ℤ) ≫
      (I.isoRightDerivedObjCochain F n).inv := by
  dsimp only
  apply (cancel_mono ((F.rightDerivedSingleHomologyIso n).hom.app N)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [F.rightDerivedSingleHomologyIso_hom_app I n, isoRightDerivedSingleHomology_hom]
  simp only [Iso.inv_hom_id_assoc]
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (Category.comp_id _).trans (derivedUnit_cocycle_homology F I n f hf)

end CategoryTheory.InjectiveResolution

namespace DerivedCategory.Plus
universe u v d
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- Coefficient precomposition retains the original single/homology normalization. -/
private theorem single_homology_shiftMap_precomp {U V : C} (b : U ⟶ V)
    {K : Plus C} (q : ℤ) (c : ShiftedHom ((singleFunctor C 0).obj V) K q) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app U ≫
        (homologyFunctor C 0).shiftMap ((singleFunctor C 0).map b ≫ c)
          0 q (by omega) =
      b ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app V ≫
        (homologyFunctor C 0).shiftMap c 0 q (by omega) := by
  let H := homologyFunctor C 0
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso C 0
  have hn : b ≫ E.inv.app V = E.inv.app U ≫ H.map ((singleFunctor C 0).map b) :=
    E.inv.naturality b
  rw [Functor.shiftMap_comp']
  change E.inv.app U ≫ H.map ((singleFunctor C 0).map b) ≫ H.shiftMap c 0 q _ =
    b ≫ E.inv.app V ≫ H.shiftMap c 0 q _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ H.shiftMap c 0 q (by omega)) hn.symm).trans
      (Category.assoc _ _ _))

end DerivedCategory.Plus

namespace CategoryTheory.Adjunction

universe u v d u' v' d'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
    [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{d'} B] [EnoughInjectives B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]
    (adj : L ⊣ R)

/-- The original shifted adjunct keeps the ordinary adjunct and native single unit. -/
private theorem rightDerivedFunctorPlus_shiftedHomEquiv_single
    {U : A} {M N : B} (f : L.obj U ⟶ M) (q : ℤ)
    (c : ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj M)
      ((DerivedCategory.Plus.singleFunctor B 0).obj N) q) :
    adj.rightDerivedFunctorPlus.shiftedHomEquiv q
        ((DerivedCategory.Plus.singleFunctor A 0).obj U)
        ((DerivedCategory.Plus.singleFunctor B 0).obj N)
        (((L.rightDerivedFunctorPlusSingleIso 0).hom.app U ≫
          (DerivedCategory.Plus.singleFunctor B 0).map f) ≫ c) =
      (DerivedCategory.Plus.singleFunctor A 0).map (adj.homEquiv U M f) ≫
        R.rightDerivedSingleUnit M ≫ c.map R.rightDerivedFunctorPlus := by
  rw [Adjunction.shiftedHomEquiv_apply, Adjunction.homEquiv_naturality_right,
    adj.rightDerivedFunctorPlus_homEquiv_single f]
  simp only [ShiftedHom.map, Category.assoc]

end CategoryTheory.Adjunction


namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u dX dS w
attribute [local instance] hasSheafifyLarge

private theorem integerSections_comp {S : Scheme.{u}}
    {A B : AbelianSheaf.{u, u + 1} S}
    (a : (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A) (f : A ⟶ B) :
    (constantIntegerHomGlobalSectionsIso S).hom.app B (a ≫ f) =
      (globalSections S).map f ((constantIntegerHomGlobalSectionsIso S).hom.app A a) :=
  Adjunction.integerHomSectionsAddEquiv_naturality (constantAdjunction S) f a

variable {X S : Scheme.{u}} (p : X ⟶ S)
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original single-unit action on a cycle has the original global higher-image section. -/
private theorem cohomologyToHigherSections_unitAction_cocycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cochainComplex.X (q : ℤ))
    (ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    let c : Sheaf.H.{w} F q := I.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha))
    let b : (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (directImage p).obj (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := (inverseImageAdjunction p).homEquiv _ _
      ((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F)
      (b ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 0).inv.app ((directImage p).obj (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
          ((directImage p).rightDerivedSingleUnit (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
            c.homPlus.map (derivedDirectImage p)) 0 (q : ℤ) (by omega) ≫
        (higherDirectImageIso p q).inv.app F) = cohomologyToHigherSections p F q c := by
  intro c b
  let R := directImage p
  let Γ := globalSections S
  let T := (R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  have hRa : R.map a ≫ T.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    change R.map a ≫ R.map (I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1)) = 0
    rw [← R.map_comp, ha, R.map_zero]
  let l := T.liftCycles (R.map a) ((q : ℤ) + 1) (by simp) hRa
  let v : R.obj (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (higherDirectImage p q).obj F :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (AbelianSheaf.{u, u + 1} S) 0).inv.app
        (R.obj (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
        (R.rightDerivedSingleUnit (Functor.obj
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ c.homPlus.map (derivedDirectImage p))
        0 (q : ℤ) (by omega) ≫ (higherDirectImageIso p q).inv.app F
  let E := I.isoRightDerivedObjCochain R q
  have hv : v = l ≫ T.homologyπ (q : ℤ) ≫ E.inv :=
    InjectiveResolution.derivedUnit_cocycle_rightDerived R I q a ha
  let z' := (constantIntegerHomGlobalSectionsIso S).hom.app (T.cycles (q : ℤ)) (b ≫ l)
  obtain ⟨z, hz, hx⟩ := cohomologyToHigherSections_exists_resolution_cycle p I q a ha
  have hl : l ≫ T.iCycles (q : ℤ) = R.map a :=
    T.liftCycles_i (R.map a) ((q : ℤ) + 1) (by simp) hRa
  have hb : b ≫ R.map a = (inverseImageAdjunction p).homEquiv _ _
      (((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a) :=
    ((inverseImageAdjunction p).homEquiv_naturality_right _ a).symm
  have hz' : Γ.map (T.iCycles (q : ℤ)) z' =
      (directImageGlobalSectionsIso p).inv.app (I.cochainComplex.X (q : ℤ))
        ((constantIntegerHomGlobalSectionsIso X).hom.app (I.cochainComplex.X (q : ℤ)) a) := by
    calc
      _ = (constantIntegerHomGlobalSectionsIso S).hom.app (T.X (q : ℤ))
          ((b ≫ l) ≫ T.iCycles (q : ℤ)) := (integerSections_comp (b ≫ l) _).symm
      _ = (constantIntegerHomGlobalSectionsIso S).hom.app (T.X (q : ℤ))
          ((inverseImageAdjunction p).homEquiv _ _
            (((inverseImageConstantIso p).hom.app
              (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a)) := by rw [Category.assoc, hl, hb]
      _ = _ := constantIntegerAdjunct_sections p (I.cochainComplex.X (q : ℤ)) a
  have hzz : z' = z :=
    (AddCommGrpCat.mono_iff_injective (Γ.map (T.iCycles (q : ℤ)))).mp inferInstance
      (hz'.trans hz.symm)
  have he : (b ≫ v) ≫ E.hom = (b ≫ l) ≫ T.homologyπ (q : ℤ) := by
    rw [hv]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hvalue : Γ.map E.hom
      ((constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F) (b ≫ v)) =
      Γ.map (T.homologyπ (q : ℤ)) z' := by
    calc
      _ = (constantIntegerHomGlobalSectionsIso S).hom.app (T.homology (q : ℤ))
          ((b ≫ v) ≫ E.hom) := (integerSections_comp (b ≫ v) E.hom).symm
      _ = (constantIntegerHomGlobalSectionsIso S).hom.app (T.homology (q : ℤ))
          ((b ≫ l) ≫ T.homologyπ (q : ℤ)) := congrArg
            ((constantIntegerHomGlobalSectionsIso S).hom.app (T.homology (q : ℤ))) he
      _ = _ := integerSections_comp (b ≫ l) (T.homologyπ (q : ℤ))
  change (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F)
    (b ≫ v) = cohomologyToHigherSections p F q c
  apply (ConcreteCategory.bijective_of_isIso (Γ.map E.hom)).injective
  exact hvalue.trans ((congrArg (Γ.map (T.homologyπ (q : ℤ))) hzz).trans hx.symm)

/-- Every original global class has its original right-derived single-unit section value. -/
private theorem cohomologyToHigherSections_unitAction
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let M := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let b : U ⟶ (directImage p).obj M := (inverseImageAdjunction p).homEquiv _ _
      ((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F)
      (b ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 0).inv.app ((directImage p).obj M) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
          ((directImage p).rightDerivedSingleUnit M ≫
            c.homPlus.map (derivedDirectImage p)) 0 (q : ℤ) (by omega) ≫
        (higherDirectImageIso p q).inv.app F) = cohomologyToHigherSections p F q c := by
  let I := injectiveResolution F
  obtain ⟨a, rfl⟩ := I.extEquivCohomologyClass.symm.surjective c
  obtain ⟨z, rfl⟩ := a.mk_surjective
  obtain ⟨f, hf, rfl⟩ :=
    Cocycle.fromSingleMk_surjective z (q : ℤ) (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl
  exact cohomologyToHigherSections_unitAction_cocycle p I q f hf

/-- The ORIGINAL shifted derived adjunct evaluates to the ORIGINAL terminal higher-image section. -/
private theorem cohomologyToHigherSections_shiftedAdjunct_value
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let M := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let e : (derivedInverseImage p).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj U) ≅
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj M :=
      ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
        ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    let z := (derivedImageAdjunction p).shiftedHomEquiv (q : ℤ)
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj U)
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
      (e.hom ≫ c.homPlus)
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 0).inv.app U ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
          z 0 (q : ℤ) (by omega) ≫ (higherDirectImageIso p q).inv.app F) =
      cohomologyToHigherSections p F q c := by
  intro U M e z
  let b : U ⟶ (directImage p).obj M := (inverseImageAdjunction p).homEquiv _ _
    ((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  have hz : z =
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).map b ≫
        (directImage p).rightDerivedSingleUnit M ≫ c.homPlus.map (derivedDirectImage p) :=
    (inverseImageAdjunction p).rightDerivedFunctorPlus_shiftedHomEquiv_single
      ((inverseImageConstantIso p).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (q : ℤ) c.homPlus
  have hpre := DerivedCategory.Plus.single_homology_shiftMap_precomp b (q : ℤ)
    ((directImage p).rightDerivedSingleUnit M ≫ c.homPlus.map (derivedDirectImage p))
  have hm : (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 0).inv.app U ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
        z 0 (q : ℤ) (by omega) ≫ (higherDirectImageIso p q).inv.app F =
      b ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 0).inv.app ((directImage p).obj M) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
          ((directImage p).rightDerivedSingleUnit M ≫ c.homPlus.map (derivedDirectImage p))
          0 (q : ℤ) (by omega) ≫ (higherDirectImageIso p q).inv.app F := by
    rw [hz]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ (higherDirectImageIso p q).inv.app F) hpre
  exact (congrArg
    ((constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p q).obj F)) hm).trans
      (cohomologyToHigherSections_unitAction p F q c)

/-- Exactly the original shifted-target adjunct, transported to the original degree-one single. -/
abbrev cohomologyOriginalDerivedAdjunct
    (F : AbelianSheaf.{u, u + 1} X) (c : Sheaf.H.{w} F 1) :
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 1).obj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (derivedDirectImage p).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F) :=
  let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let U₀ := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj U
  let M₀ := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
  let K := (derivedDirectImage p).obj M₀
  let e := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let z := (derivedImageAdjunction p).shiftedHomEquiv (1 : ℤ) U₀ M₀ (e.hom ≫ c.homPlus)
  let η := ((DerivedCategory.Plus.singleFunctors (AbelianSheaf.{u, u + 1} S)).shiftIso
    (-1) 1 0 (by omega)).app U
  η.inv ≫ ((shiftEquiv' (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S))
    (-1) 1 (by omega)).toAdjunction.homEquiv U₀ K).symm z

/-- The actual H1 of the original adjunct has the original higher-image section value. -/
theorem cohomologyOriginalDerivedAdjunct_h1_value
    (F : AbelianSheaf.{u, u + 1} X) (c : Sheaf.H.{w} F 1) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p 1).obj F)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 1).inv.app U ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
          (cohomologyOriginalDerivedAdjunct p F c) ≫ (higherDirectImageIso p 1).inv.app F) =
      cohomologyToHigherSections p F 1 c := by
  intro U
  let M₀ := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
  let K := (derivedDirectImage p).obj M₀
  let e := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let z := (derivedImageAdjunction p).shiftedHomEquiv (1 : ℤ)
    ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj U)
    M₀ (e.hom ≫ c.homPlus)
  have hs := DerivedCategory.Plus.shiftedSingleHomologyOne U K z
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 1).inv.app U ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
        (cohomologyOriginalDerivedAdjunct p F c) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 0).inv.app U ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).shiftMap
        z 0 1 (by omega) at hs
  have hv := congrArg (fun k =>
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p 1).obj F)
      (k ≫ (higherDirectImageIso p 1).inv.app F)) hs
  exact hv.trans (cohomologyToHigherSections_shiftedAdjunct_value p F 1 c)

/-- The whole original H1 map is fixed by the original constant-source section adjunction. -/
theorem cohomologyOriginalDerivedAdjunct_h1_map
    (F : AbelianSheaf.{u, u + 1} X) (c : Sheaf.H.{w} F 1) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
        (cohomologyOriginalDerivedAdjunct p F c) ≫ (higherDirectImageIso p 1).inv.app F =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 1).hom.app U ≫
        (constantIntegerHomGlobalSectionsIso S).inv.app ((higherDirectImage p 1).obj F)
          (cohomologyToHigherSections p F 1 c) := by
  intro U
  let E := (constantIntegerHomGlobalSectionsIso S).app ((higherDirectImage p 1).obj F)
  let a := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (AbelianSheaf.{u, u + 1} S) 1).app U
  have hvalue := cohomologyOriginalDerivedAdjunct_h1_value p F c
  have hi := ConcreteCategory.congr_hom E.inv_hom_id (cohomologyToHigherSections p F 1 c)
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hi
  have he : a.inv ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
        (cohomologyOriginalDerivedAdjunct p F c) ≫ (higherDirectImageIso p 1).inv.app F =
      E.inv (cohomologyToHigherSections p F 1 c) := by
    apply (ConcreteCategory.bijective_of_isIso E.hom).injective
    exact hvalue.trans hi.symm
  apply (cancel_epi a.inv).mp
  change a.inv ≫
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
        (cohomologyOriginalDerivedAdjunct p F c) ≫ (higherDirectImageIso p 1).inv.app F =
    a.inv ≫ a.hom ≫ E.inv (cohomologyToHigherSections p F 1 c)
  simpa only [Iso.inv_hom_id_assoc] using he

end AlgebraicGeometry.Scheme.EtaleCohomology
