/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.NormalCoefficient
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.Cohomology
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# Original augmentation and the degree-zero unit normalization

Native cycle projections, the unchanged Hom class/localization comparison and
original coinduction identify the coefficient augmentation with the functional
A-to-R map that it already represents. The actual TwoLayer unit normalization
uses the same regular-source homology normalization after its native single
model comparison. Finite-normal projectivity is proved from the original finite
injective local map; no extra normalization or projectivity premise is assumed.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex Opposite

@[expose] public noncomputable section
universe u v

private theorem unitNormalization_map_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z W : C} {a : X ⟶ Y} {b : Y ⟶ W} {c : X ⟶ Z} {d : Z ⟶ W}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

private theorem unitNormalization_paste_squares
    {C : Type*} [Category* C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : A ⟶ F} {e : F ⟶ D} {k : F ⟶ G} {q : G ⟶ E}
    (h : a ≫ b = d ≫ e) (h' : e ≫ c = k ≫ q) :
    a ≫ (b ≫ c) = (d ≫ k) ≫ q := by
  rw [← Category.assoc, h, Category.assoc, h', Category.assoc]

private theorem unitNormalization_paste_three
    {C : Type*} [Category* C] {A B D E F G H I : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ F}
    {p : A ⟶ G} {q : G ⟶ D} {r : G ⟶ H} {s : H ⟶ E}
    {t : H ⟶ I} {u : I ⟶ F}
    (h₁ : a ≫ b = p ≫ q) (h₂ : q ≫ c = r ≫ s) (h₃ : s ≫ d = t ≫ u) :
    a ≫ (b ≫ c ≫ d) = (p ≫ r ≫ t) ≫ u := by
  have h := unitNormalization_paste_squares
    (unitNormalization_paste_squares h₁ h₂) h₃
  simpa only [Category.assoc] using h

private theorem unitNormalization_three_composition
    {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (e : D ⟶ F) (f : B ⟶ G) (g : G ⟶ F) (k : A ⟶ G)
    (hc : c ≫ d = e) (hb : b ≫ e = f ≫ g) (ha : a ≫ f = k) :
    (a ≫ b ≫ c) ≫ d = k ≫ g := by
  simp only [Category.assoc]
  rw [hc, hb, ← Category.assoc, ha]

private theorem unitNormalization_mk_zero
    {C : Type*} [Category* C] [HasShift C ℤ] {X Y : C} (f : X ⟶ Y) :
    ShiftedHom.mk₀ (0 : ℤ) rfl f =
      f ≫ (CategoryTheory.shiftFunctorZero C ℤ).inv.app Y := by
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']

private theorem unitNormalization_iso_linear_trans_apply
    {R : Type*} [CommRing R] {M N : ModuleCat.{u} R}
    {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≅ N) (D : N ≃ₗ[R] P) (x : M) :
    (e.toLinearEquiv.trans D) x = D (e.hom.hom x) := rfl

private theorem unitNormalization_linear_trans_eq
    {R M X Y Z : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module R M] [Module R X] [Module R Y] [Module R Z]
    (D : M ≃ₗ[R] X) (C : Y ≃ₗ[R] X) (E : Z ≃ₗ[R] Y)
    (x : M) (z : Z) (h : C.symm (D x) = E z) :
    (D.trans (C.symm.trans E.symm)) x = z := by
  change E.symm (C.symm (D x)) = z
  rw [h, E.symm_apply_apply]

private theorem unitNormalization_augmentation_cancel
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K L J : C} {M N : D} (s : M ≅ F.obj K) (t : N ≅ F.obj L)
    (a : K ⟶ L) (u : L ⟶ J) [IsIso (F.map u)] (g : M ⟶ N)
    (h : g ≫ t.hom = s.hom ≫ F.map a) :
    s.hom ≫ F.map (a ≫ u) ≫ (t ≪≫ asIso (F.map u)).inv = g := by
  change s.hom ≫ F.map (a ≫ u) ≫ inv (F.map u) ≫ t.inv = _
  rw [F.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, t.hom_inv_id, Category.comp_id]

private theorem unitNormalization_XIsoOfEq_inv
    {C : Type*} [Category* C] [Preadditive C]
    (K : CochainComplex C ℤ) {p q : ℤ} (h : p = q) :
    (K.XIsoOfEq h).inv = (K.XIsoOfEq h.symm).hom := by
  subst q
  rfl

namespace CategoryTheory.ShortComplex

/-- Exact functor comparison retains the original projection from cycles. -/
private theorem mapHomologyIso_projection
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (S : ShortComplex C) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  let a : (S.map F).cycles ⟶ F.obj h.K := (h.map F).cyclesIso.hom
  let b : (S.map F).homology ⟶ F.obj h.H := (h.map F).homologyIso.hom
  have hπ : (S.map F).homologyπ ≫ b = a ≫ F.map h.π :=
    (h.map F).homologyπ_comp_homologyIso_hom
  have hq : F.map h.π ≫ F.map h.homologyIso.inv =
      F.map h.cyclesIso.inv ≫ F.map S.homologyπ :=
    unitNormalization_map_square F h.π_comp_homologyIso_inv
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  change (S.map F).homologyπ ≫ (b ≫ F.map h.homologyIso.inv) =
    (a ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ
  exact unitNormalization_paste_squares hπ hq

/-- The inverse exact-functor comparison retains that same projection. -/
theorem mapHomologyIso_inv_projection
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (S : ShortComplex C) :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  apply (cancel_epi (S.mapCyclesIso F).hom).mp
  apply (cancel_mono (S.mapHomologyIso F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact (mapHomologyIso_projection F S).symm

end CategoryTheory.ShortComplex

namespace CochainComplex.HomComplex

variable {A : Type u} [CommRing A]

/-- The native module cycle comparison is the original forgetful comparison,
then the identity-on-cochains comparison, then the original cocycle kernel. -/
def originalModuleCyclesComparison
    (K J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj ((moduleComplex A K J).cycles n) ⟶
      AddCommGrpCat.of (Cocycle K J n) :=
  (((moduleComplex A K J).sc n).mapCyclesIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat)).inv ≫
    cyclesMap (moduleComplexForgetIso A K J).hom n ≫
    (leftHomologyData K J n).cyclesIso.hom

/-- Every original cycle is sent to the identical original Hom cochain. -/
theorem originalModuleCyclesComparison_cochain
    (K J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    originalModuleCyclesComparison K J n ≫ (leftHomologyData K J n).i =
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat).map ((moduleComplex A K J).iCycles n) := by
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let S := (moduleComplex A K J).sc n
  let T := HomComplex K J
  let E := moduleComplexForgetIso A K J
  let h := leftHomologyData K J n
  let a : U.obj S.cycles ⟶ (S.map U).cycles := (S.mapCyclesIso U).inv
  let b : (S.map U).cycles ⟶ T.cycles n := cyclesMap E.hom n
  let c : T.cycles n ⟶ h.K := h.cyclesIso.hom
  let d : h.K ⟶ T.X n := h.i
  let e : T.cycles n ⟶ T.X n := T.iCycles n
  let f : (S.map U).cycles ⟶ U.obj S.X₂ := (S.map U).iCycles
  let g : U.obj S.X₂ ⟶ T.X n := E.hom.f n
  let k : U.obj S.cycles ⟶ U.obj S.X₂ := U.map S.iCycles
  have hc : c ≫ d = e := h.cyclesIso_hom_comp_i
  have hb : b ≫ e = f ≫ g := cyclesMap_i E.hom n
  have ha : a ≫ f = k :=
    (congrArg (fun z => a ≫ z) (S.mapCyclesIso_hom_iCycles U).symm).trans
      ((S.mapCyclesIso U).inv_hom_id_assoc k)
  have hp := unitNormalization_three_composition a b c d e f g k hc hb ha
  change (a ≫ b ≫ c) ≫ d = k
  exact hp.trans (Category.comp_id k)

/-- The original projection to homology followed by the original class comparison
is precisely the quotient of that original cocycle. -/
theorem originalModuleCyclesComparison_class
    (K J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat).map ((moduleComplex A K J).homologyπ n) ≫
        (moduleHomologyClassesIso K J n).hom =
      originalModuleCyclesComparison K J n ≫ (leftHomologyData K J n).π := by
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let S := (moduleComplex A K J).sc n
  let T := HomComplex K J
  let E := moduleComplexForgetIso A K J
  let h := leftHomologyData K J n
  let a : U.obj S.homology ⟶ (S.map U).homology := (S.mapHomologyIso U).inv
  let b : (S.map U).homology ⟶ T.homology n := homologyMap E.hom n
  let c : T.homology n ⟶ h.H := h.homologyIso.hom
  let p : U.obj S.cycles ⟶ (S.map U).cycles := (S.mapCyclesIso U).inv
  let q : (S.map U).cycles ⟶ (S.map U).homology := (S.map U).homologyπ
  let r : (S.map U).cycles ⟶ T.cycles n := cyclesMap E.hom n
  let t : T.cycles n ⟶ h.K := h.cyclesIso.hom
  have h₁ : U.map S.homologyπ ≫ a = p ≫ q :=
    ShortComplex.mapHomologyIso_inv_projection U S
  have h₂ : q ≫ b = r ≫ T.homologyπ n := homologyπ_naturality E.hom n
  have h₃ : T.homologyπ n ≫ c = t ≫ h.π := h.homologyπ_comp_homologyIso_hom
  change U.map S.homologyπ ≫ (a ≫ b ≫ c) = (p ≫ r ≫ t) ≫ h.π
  exact unitNormalization_paste_three h₁ h₂ h₃

/-- A native cycle with the stated original cochain represents the supplied cocycle.
The premise is equality of the underlying cochains, not a cohomology/trace oracle. -/
theorem moduleCocycleClass_of_cycles
    (K J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (moduleComplex A K J).cycles n) (z : Cocycle K J n)
    (hz : (moduleComplex A K J).iCycles n x = (z : Cochain K J n)) :
    (moduleComplex A K J).homologyπ n x = moduleCocycleClass K J n z := by
  have hc : originalModuleCyclesComparison K J n x = z := by
    apply Cocycle.ext
    have h := ConcreteCategory.congr_hom (originalModuleCyclesComparison_cochain K J n) x
    exact h.trans hz
  apply (moduleHomologyClassesAddEquiv K J n).injective
  rw [moduleCocycleClass_comparison]
  have h := ConcreteCategory.congr_hom (originalModuleCyclesComparison_class K J n) x
  change (moduleHomologyClassesIso K J n).hom
      ((moduleComplex A K J).homologyπ n x) =
    CohomologyClass.mk (originalModuleCyclesComparison K J n x) at h
  exact h.trans (congrArg CohomologyClass.mk hc)

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

variable {A : Type u} [CommRing A]

/-- A chain map from an original single determines its homology class through
its literal degree-zero component. -/
theorem single_homologyMap_moduleCocycleClass
    (M : ModuleCat.{u} A) (K J : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : ((singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ moduleComplex A K J)
    (φ : M) (z : Cocycle K J 0)
    (hz : f.f 0 ((singleObjXSelf (.up ℤ) 0 M).inv φ) = (z : Cochain K J 0)) :
    homologyMap f 0 ((singleObjHomologySelfIso (.up ℤ) 0 M).inv φ) =
      moduleCocycleClass K J 0 z := by
  let B := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let L := moduleComplex A K J
  let ec := singleObjCyclesSelfIso (.up ℤ) 0 M
  let eh := singleObjHomologySelfIso (.up ℤ) 0 M
  let x := cyclesMap f 0 (ec.inv φ)
  have hx : L.iCycles 0 x = (z : Cochain K J 0) := by
    have h₁ := ConcreteCategory.congr_hom (cyclesMap_i f 0) (ec.inv φ)
    have h₂ := ConcreteCategory.congr_hom (singleObjCyclesSelfIso_inv_iCycles (.up ℤ) 0 M) φ
    change L.iCycles 0 x = f.f 0 (B.iCycles 0 (ec.inv φ)) at h₁
    change B.iCycles 0 (ec.inv φ) = (singleObjXSelf (.up ℤ) 0 M).inv φ at h₂
    exact h₁.trans ((congrArg (f.f 0) h₂).trans hz)
  have hm : ec.inv ≫ cyclesMap f 0 ≫ L.homologyπ 0 = eh.inv ≫ homologyMap f 0 := by
    rw [← homologyπ_naturality, ← Category.assoc,
      singleObjCyclesSelfIso_inv_homologyπ]
  have hv := ConcreteCategory.congr_hom hm φ
  change L.homologyπ 0 x = homologyMap f 0 (eh.inv φ) at hv
  exact hv.symm.trans (moduleCocycleClass_of_cycles K J 0 x z hx)

/-- The element of the original coefficient defines multiplication on the regular module. -/
def regularCoefficientMap (M : ModuleCat.{u} A) (φ : M) : ModuleCat.of A A ⟶ M :=
  ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf A A M).symm φ)

/-- The original regular-module coefficient morphism takes one to its supplied coefficient. -/
theorem regularCoefficientMap_one (M : ModuleCat.{u} A) (φ : M) :
    regularCoefficientMap M φ (1 : A) = φ :=
  (LinearMap.ringLmapEquivSelf A A M).apply_symm_apply φ

/-- The regular Hom augmentation represents the literal single map followed by
that same coefficient augmentation. -/
theorem regularHomAugmentation_class
    (M : ModuleCat.{u} A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (j : ((singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ J) (φ : M) :
    homologyMap (j ≫ (regularSingleComplexIso J).inv) 0
        ((singleObjHomologySelfIso (.up ℤ) 0 M).inv φ) =
      moduleCocycleClass ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J 0
        (Cocycle.ofHom ((singleFunctor (ModuleCat.{u} A) 0).map
          (regularCoefficientMap M φ) ≫ j)) := by
  let K := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let E := regularSingleComplexIso J
  let b := j ≫ E.inv
  let l := regularCoefficientMap M φ
  let f := (singleFunctor (ModuleCat.{u} A) 0).map l ≫ j
  let eA := singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)
  let eM := singleObjXSelf (.up ℤ) 0 M
  apply single_homologyMap_moduleCocycleClass M K J b φ (Cocycle.ofHom f)
  apply (regularSingleCochainEquiv J 0).injective
  have hb : b ≫ E.hom = j := by
    simp only [b, Category.assoc, E.inv_hom_id, Category.comp_id]
  have hb₀ := congrArg (fun k => k.f 0) hb
  have hy := ConcreteCategory.congr_hom hb₀ (eM.inv φ)
  change E.hom.f 0 (b.f 0 (eM.inv φ)) = j.f 0 (eM.inv φ) at hy
  have hf : eA.inv ≫ f.f 0 = l ≫ eM.inv ≫ j.f 0 := by
    change eA.inv ≫ (((singleFunctor (ModuleCat.{u} A) 0).map l).f 0 ≫ j.f 0) = _
    rw [single_map_f_self]
    change eA.inv ≫ (eA.hom ≫ l ≫ eM.inv) ≫ j.f 0 = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change E.hom.f 0 (b.f 0 (eM.inv φ)) =
    regularSingleCochainEquiv J 0 (Cochain.ofHom f)
  rw [hy, regularSingleCochainEquiv_apply]
  change j.f 0 (eM.inv φ) = (eA.inv ≫ f.f 0) (1 : A)
  rw [hf]
  change j.f 0 (eM.inv φ) = j.f 0 (eM.inv (l (1 : A)))
  rw [regularCoefficientMap_one]

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Scalar restriction and a specified original chain comparison retain the
class of the literal degree-n cochain. -/
theorem restricted_homology_class_of_cycles
    (σ : R →+* A) (L : CochainComplex (ModuleCat.{u} A) ℤ)
    (K J : CochainComplex (ModuleCat.{u} R) ℤ)
    (E : ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj L ≅
      moduleComplex R K J) (n : ℤ) (x : L.cycles n) (z : Cocycle K J n)
    (hz : E.hom.f n (L.iCycles n x) = (z : Cochain K J n)) :
    (((L.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n).mapIso E).hom
        (L.homologyπ n x) = moduleCocycleClass K J n z := by
  let U := ModuleCat.restrictScalars σ
  let S := L.sc n
  let T := moduleComplex R K J
  let a : U.obj S.cycles ⟶ (S.map U).cycles := (S.mapCyclesIso U).inv
  let c : (S.map U).cycles ⟶ T.cycles n := cyclesMap E.hom n
  let e : U.obj S.homology ⟶ (S.map U).homology := (S.mapHomologyIso U).inv
  let hmap : (S.map U).homology ⟶ T.homology n := homologyMap E.hom n
  let q : (S.map U).cycles ⟶ (S.map U).homology := (S.map U).homologyπ
  let y := c (a x)
  have hc : a ≫ (S.map U).iCycles = U.map S.iCycles := by
    rw [← S.mapCyclesIso_hom_iCycles U, Iso.inv_hom_id_assoc]
  have hy : T.iCycles n y = (z : Cochain K J n) := by
    have h₁ := ConcreteCategory.congr_hom (cyclesMap_i E.hom n) (a x)
    have h₂ := ConcreteCategory.congr_hom hc x
    change T.iCycles n y = E.hom.f n ((S.map U).iCycles (a x)) at h₁
    change (S.map U).iCycles (a x) = L.iCycles n x at h₂
    exact h₁.trans ((congrArg (E.hom.f n) h₂).trans hz)
  have h₁ : U.map S.homologyπ ≫ e = a ≫ q :=
    ShortComplex.mapHomologyIso_inv_projection U S
  have h₂ : q ≫ hmap = c ≫ T.homologyπ n := homologyπ_naturality E.hom n
  have hp : U.map S.homologyπ ≫ e ≫ hmap = a ≫ c ≫ T.homologyπ n :=
    (unitNormalization_paste_squares h₁ h₂).trans (Category.assoc a c (T.homologyπ n))
  have hv := ConcreteCategory.congr_hom hp x
  change hmap (e (L.homologyπ n x)) = T.homologyπ n y at hv
  exact hv.trans (moduleCocycleClass_of_cycles K J n y z hy)

/-- The actual scalar-restricted single augmentation can be evaluated before
passing through its original homology comparison. -/
theorem restricted_single_homologyMap_moduleCocycleClass
    (σ : R →+* A) (M : ModuleCat.{u} A) (L : CochainComplex (ModuleCat.{u} A) ℤ)
    (K J : CochainComplex (ModuleCat.{u} R) ℤ)
    (E : ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj L ≅
      moduleComplex R K J)
    (f : ((singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ L) (φ : M)
    (z : Cocycle K J 0)
    (hz : E.hom.f 0 (f.f 0 ((singleObjXSelf (.up ℤ) 0 M).inv φ)) =
      (z : Cochain K J 0)) :
    (((L.sc 0).mapHomologyIso (ModuleCat.restrictScalars σ)).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).mapIso E).hom
        (homologyMap f 0 ((singleObjHomologySelfIso (.up ℤ) 0 M).inv φ)) =
      moduleCocycleClass K J 0 z := by
  let B := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let ec := singleObjCyclesSelfIso (.up ℤ) 0 M
  let eh := singleObjHomologySelfIso (.up ℤ) 0 M
  let x := cyclesMap f 0 (ec.inv φ)
  have hc : L.iCycles 0 x = f.f 0 ((singleObjXSelf (.up ℤ) 0 M).inv φ) := by
    have h₁ := ConcreteCategory.congr_hom (cyclesMap_i f 0) (ec.inv φ)
    have h₂ := ConcreteCategory.congr_hom (singleObjCyclesSelfIso_inv_iCycles (.up ℤ) 0 M) φ
    change L.iCycles 0 x = f.f 0 (B.iCycles 0 (ec.inv φ)) at h₁
    change B.iCycles 0 (ec.inv φ) = (singleObjXSelf (.up ℤ) 0 M).inv φ at h₂
    exact h₁.trans (congrArg (f.f 0) h₂)
  have hm : ec.inv ≫ cyclesMap f 0 ≫ L.homologyπ 0 = eh.inv ≫ homologyMap f 0 := by
    rw [← homologyπ_naturality, ← Category.assoc,
      singleObjCyclesSelfIso_inv_homologyπ]
  have hv := ConcreteCategory.congr_hom hm φ
  change L.homologyπ 0 x = homologyMap f 0 (eh.inv φ) at hv
  rw [← hv]
  exact restricted_homology_class_of_cycles σ L K J E 0 x z
    ((congrArg (E.hom.f 0) hc).trans hz)

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  (σ : R →+* A) [IsLocalHom σ] (hfin : σ.Finite) (hinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)

/-- The passed finite-normal coefficient normalization sends the actual
augmentation cocycle to its original native coinduced coefficient. -/
theorem coinducedRegularHomologyZeroIso_cocycle
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u]
    (φ : coinducedCoefficient σ) :
    (coinducedRegularHomologyZeroIso σ hfin hinj hR hA I u).hom
      (moduleCocycleClass ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        (coinducedCoefficientComplex σ I) 0
        (Cocycle.ofHom ((singleFunctor (ModuleCat.{u} A) 0).map
          (regularCoefficientMap (coinducedCoefficient σ) φ) ≫
            coinducedCoefficientAugmentation σ I u))) = φ := by
  let M := coinducedCoefficient σ
  let J := coinducedCoefficientComplex σ I
  let j := coinducedCoefficientAugmentation σ I u
  let eh := singleObjHomologySelfIso (.up ℤ) 0 M
  let E := coinducedRegularHomologyZeroIso σ hfin hinj hR hA I u
  have hc := regularHomAugmentation_class M J j φ
  have ha := ConcreteCategory.congr_hom
    (coinducedRegularHomologyZeroIso_augmentation σ hfin hinj hR hA I u) (eh.inv φ)
  calc
    _ = E.hom (homologyMap (j ≫ (regularSingleComplexIso J).inv) 0 (eh.inv φ)) :=
      congrArg E.hom hc.symm
    _ = eh.hom (eh.inv φ) := ha
    _ = φ := ConcreteCategory.congr_hom eh.inv_hom_id φ

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

private theorem unitNormalization_single_map_component
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶ I) (f : M ⟶ N) :
    Cochain.fromSingleEquiv (zero_add (0 : ℤ))
      (Cochain.ofHom ((singleFunctor (ModuleCat.{u} R) 0).map f ≫ u)) =
        f ≫ (singleObjXSelf (.up ℤ) 0 N).inv ≫ u.f 0 := by
  let eM := singleObjXSelf (.up ℤ) 0 M
  let eN := singleObjXSelf (.up ℤ) 0 N
  change eM.inv ≫ (((singleFunctor (ModuleCat.{u} R) 0).map f).f 0 ≫ u.f 0) = _
  rw [single_map_f_self]
  change eM.inv ≫ ((eM.hom ≫ f ≫ eN.inv) ≫ u.f 0) = f ≫ eN.inv ≫ u.f 0
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The original native coinduced coefficient, regarded as its actual R-linear functional. -/
def originalCoinducedFunctional (φ : coinducedCoefficient σ) :
    (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) ⟶ ModuleCat.of R R :=
  (ModuleCat.homLinearEquiv (R := R) (S := R)
    (M := (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))
    (N := ModuleCat.of R R)).symm (coinducedCoefficientEquiv σ φ)

/-- The native restricted functional has the exact original coinduction value. -/
theorem originalCoinducedFunctional_apply (φ : coinducedCoefficient σ)
    (a : (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :
    originalCoinducedFunctional σ φ a = coinducedCoefficientEquiv σ φ a := rfl

/-- The degree-zero coinduction comparison evaluates the original regular Hom
augmentation at one, retaining both original single comparisons. -/
theorem coinducedRegularHomAugmentation_component
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I)
    (φ : coinducedCoefficient σ) :
    (coinducedSingleComplexIso σ (ModuleCat.of A A) I).hom.f 0
      ((coinducedRegularHomAugmentation σ I u).f 0
        ((singleObjXSelf (.up ℤ) 0 (coinducedCoefficient σ)).inv φ)) =
      (Cochain.ofHom ((singleFunctor (ModuleCat.{u} R) 0).map
        (originalCoinducedFunctional σ φ) ≫ u)) := by
  apply (Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
  rw [unitNormalization_single_map_component]
  apply ConcreteCategory.hom_ext
  intro a
  change _ = u.f 0 ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv
    (originalCoinducedFunctional σ φ a))
  rw [originalCoinducedFunctional_apply]
  change u.f 0 ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv
      (coinducedCoefficientEquiv σ φ ((1 : A) * (show A from a)))) =
    u.f 0 ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv
      (coinducedCoefficientEquiv σ φ (show A from a)))
  rw [one_mul]

/-- The same native scalar-restricted homology comparison sends the original
coefficient class to the original functional followed by the supplied augmentation. -/
theorem coinducedSingleHomologyIso_regular_augmentation
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I)
    (φ : coinducedCoefficient σ) :
    (coinducedSingleHomologyIso σ (ModuleCat.of A A) I 0).hom
      (homologyMap (coinducedRegularHomAugmentation σ I u) 0
        ((singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)).inv φ)) =
      moduleCocycleClass
        ((singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))) I 0
        (Cocycle.ofHom ((singleFunctor (ModuleCat.{u} R) 0).map
          (originalCoinducedFunctional σ φ) ≫ u)) :=
  restricted_single_homologyMap_moduleCocycleClass σ (coinducedCoefficient σ)
    (moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
      (coinducedCoefficientComplex σ I))
    ((singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))) I
    (coinducedSingleComplexIso σ (ModuleCat.of A A) I)
    (coinducedRegularHomAugmentation σ I u) φ
    (Cocycle.ofHom ((singleFunctor (ModuleCat.{u} R) 0).map
      (originalCoinducedFunctional σ φ) ≫ u))
    (coinducedRegularHomAugmentation_component σ I u φ)

end CochainComplex.HomComplex

private theorem zero_target_comparison
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K J : C} {U V : D}
    (s : U ⟶ F.obj K) (e : V ≅ F.obj J) (f : K ⟶ J) :
    s ≫ F.map (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
      (((shiftFunctor D (0 : ℤ)).mapIso e) ≪≫
        ((F.commShiftIso (0 : ℤ)).app J).symm).inv =
      ShiftedHom.mk₀ (0 : ℤ) rfl (s ≫ F.map f ≫ e.inv) := by
  let Z := shiftFunctorZero D ℤ
  have hm : F.map (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
      (F.commShiftIso (0 : ℤ)).hom.app J = F.map f ≫ Z.inv.app (F.obj J) := by
    simpa only [ShiftedHom.map, unitNormalization_mk_zero] using
      ShiftedHom.map_mk₀ (0 : ℤ) rfl f F
  have he := Z.inv.naturality e.inv
  change e.inv ≫ Z.inv.app V = Z.inv.app (F.obj J) ≫ e.inv⟦(0 : ℤ)⟧' at he
  rw [unitNormalization_mk_zero (s ≫ F.map f ≫ e.inv)]
  change s ≫ F.map (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
      (F.commShiftIso (0 : ℤ)).hom.app J ≫ e.inv⟦(0 : ℤ)⟧' =
    (s ≫ F.map f ≫ e.inv) ≫ Z.inv.app V
  rw [← Category.assoc (F.map (ShiftedHom.mk₀ (0 : ℤ) rfl f))
    ((F.commShiftIso (0 : ℤ)).hom.app J) (e.inv⟦(0 : ℤ)⟧'), hm]
  calc
    _ = s ≫ F.map f ≫ (Z.inv.app (F.obj J) ≫ e.inv⟦(0 : ℤ)⟧') := by
      simp only [Category.assoc]
    _ = s ≫ F.map f ≫ (e.inv ≫ Z.inv.app V) :=
      congrArg (fun k => s ≫ F.map f ≫ k) he.symm
    _ = _ := by simp only [Category.assoc]

namespace CochainComplex.HomComplex

/-- The original zero cocycle uses precisely the native zero-shift inverse. -/
theorem equivHomShift_symm_ofHom_zero
    {C : Type*} [Category* C] [Preadditive C]
    {K J : CochainComplex C ℤ} (f : K ⟶ J) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ (0 : ℤ) rfl f := by
  rw [unitNormalization_mk_zero]
  apply HomologicalComplex.hom_ext
  intro p
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctorZero_inv_app_f]
  change ((Cochain.ofHom f).rightShift 0 0 (zero_add (0 : ℤ))).v p p (add_zero p) = _
  rw [Cochain.rightShift_v (Cochain.ofHom f) 0 0 (zero_add (0 : ℤ))
    p p (add_zero p) p (add_zero p), Cochain.ofHom_v]
  exact congrArg (fun t => f.f p ≫ t) (unitNormalization_XIsoOfEq_inv J (add_zero p))

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)] [HasExt.{u} (ModuleCat.{u} R)]

/-- The passed original Hom-complex comparison retains the actual degree-zero
coefficient map, after cancellation of the same supplied augmentation. -/
theorem singleHomologyExtLinearEquiv_original_mk₀
    (M N : ModuleCat.{u} R) (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶ J) [QuasiIso u] (f : M ⟶ N) :
    singleHomologyExtLinearEquiv M N J u 0
      (moduleCocycleClass ((singleFunctor (ModuleCat.{u} R) 0).obj M) J 0
        (Cocycle.ofHom ((singleFunctor (ModuleCat.{u} R) 0).map f ≫ u))) =
      Ext.mk₀ f := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let K := (singleFunctor (ModuleCat.{u} R) 0).obj M
  let P : ModuleCat.{u} R := (moduleComplex R K J).homology 0
  let s := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M
  let t := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N
  let e := t ≪≫ asIso (Q.map u)
  let a := (singleFunctor (ModuleCat.{u} R) 0).map f
  let c := a ≫ u
  let z : Cocycle K J (0 : ℤ) := Cocycle.ofHom c
  let x : P := moduleCocycleClass K J 0 z
  let T := coefficientShiftIso N J u (0 : ℤ)
  let D : P ≃ₗ[R] (Q.obj K ⟶ Q.obj (J⟦(0 : ℤ)⟧)) :=
    moduleHomologyDerivedLinearEquiv K J 0
  let C : (S.obj M ⟶ (S.obj N)⟦(0 : ℤ)⟧) ≃ₗ[R]
      (Q.obj K ⟶ Q.obj (J⟦(0 : ℤ)⟧)) := Linear.homCongr R s T
  let E : Ext.{u} M N 0 ≃ₗ[R] (S.obj M ⟶ (S.obj N)⟦(0 : ℤ)⟧) :=
    Ext.homLinearEquiv (R := R)
  have hnat : S.map f ≫ t.hom = s.hom ≫ Q.map a :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.naturality f
  have hc : s.hom ≫ Q.map c ≫ e.inv = S.map f :=
    unitNormalization_augmentation_cancel Q s t a u (S.map f) hnat
  have hD : D x = Q.map (Cocycle.equivHomShift.symm z) :=
    moduleHomologyDerivedLinearEquiv_cocycle K J 0 z
  have hz : Cocycle.equivHomShift.symm z = ShiftedHom.mk₀ (0 : ℤ) rfl c :=
    equivHomShift_symm_ofHom_zero c
  have hC : C.symm (D x) = E (Ext.mk₀ f) :=
    (congrArg C.symm hD).trans
      ((Linear.homCongr_symm_apply R s T (Q.map (Cocycle.equivHomShift.symm z))).trans
        ((congrArg (fun w => s.hom ≫ Q.map w ≫ T.inv) hz).trans
          ((zero_target_comparison Q s.hom e c).trans
            ((congrArg (ShiftedHom.mk₀ (0 : ℤ) rfl) hc).trans (Ext.mk₀_hom f).symm))))
  exact unitNormalization_linear_trans_eq D C E x (Ext.mk₀ f) hC

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)] [HasExt.{u} (ModuleCat.{u} R)]
  (σ : R →+* A)

/-- The original coinduction Hom comparison cancels the supplied augmentation
and returns exactly the original native functional in Ext zero. -/
theorem coinducedSingleHomologyExt_regular_augmentation
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u]
    (φ : coinducedCoefficient σ) :
    coinducedSingleHomologyExtLinearEquiv.{u, u, u, v, u}
        σ (ModuleCat.of A A) (ModuleCat.of R R) I u 0
        (homologyMap (coinducedRegularHomAugmentation σ I u) 0
          ((singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)).inv φ)) =
      Ext.mk₀ (originalCoinducedFunctional σ φ) := by
  let M : ModuleCat.{u} R := (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)
  let K := (singleFunctor (ModuleCat.{u} R) 0).obj M
  let L : ModuleCat.{u} R := (ModuleCat.restrictScalars σ).obj
    ((moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
      (coinducedCoefficientComplex σ I)).homology 0)
  let N : ModuleCat.{u} R := (moduleComplex R K I).homology 0
  let e : L ≅ N := coinducedSingleHomologyIso σ (ModuleCat.of A A) I 0
  let D : N ≃ₗ[R] Ext.{u} M (ModuleCat.of R R) 0 :=
    singleHomologyExtLinearEquiv M (ModuleCat.of R R) I u 0
  let x : L := homologyMap (coinducedRegularHomAugmentation σ I u) 0
    ((singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)).inv φ)
  let z : Cocycle K I 0 := Cocycle.ofHom
    ((singleFunctor (ModuleCat.{u} R) 0).map (originalCoinducedFunctional σ φ) ≫ u)
  have hx : e.hom.hom x = moduleCocycleClass K I 0 z :=
    coinducedSingleHomologyIso_regular_augmentation σ I u φ
  have he : coinducedSingleHomologyExtLinearEquiv.{u, u, u, v, u}
      σ (ModuleCat.of A A) (ModuleCat.of R R) I u 0 x = D (e.hom.hom x) :=
    unitNormalization_iso_linear_trans_apply e D x
  exact he.trans ((congrArg D hx).trans
    (singleHomologyExtLinearEquiv_original_mk₀ M (ModuleCat.of R R) I u
      (originalCoinducedFunctional σ φ)))

variable [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  [IsLocalHom σ] (hfin : σ.Finite) (hinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)

/-- The two actual degree-zero normalizations agree on every class. This is
the native functional normalization needed by the original unit row. -/
theorem coinducedRegularHomologyZeroIso_ext_zero
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u]
    (x : (moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
      (coinducedCoefficientComplex σ I)).homology 0) :
    Ext.addEquiv₀ (coinducedSingleHomologyExtLinearEquiv.{u, u, u, v, u}
      σ (ModuleCat.of A A) (ModuleCat.of R R) I u 0 x) =
      originalCoinducedFunctional σ
        ((coinducedRegularHomologyZeroIso σ hfin hinj hR hA I u).hom x) := by
  let E := coinducedRegularHomologyZeroIso σ hfin hinj hR hA I u
  let eh := singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)
  let b := coinducedRegularHomAugmentation σ I u
  let φ := E.hom x
  let F := coinducedSingleHomologyExtLinearEquiv.{u, u, u, v, u}
    σ (ModuleCat.of A A) (ModuleCat.of R R) I u 0
  have hx : homologyMap b 0 (eh.inv φ) = x := by
    apply E.toLinearEquiv.injective
    have ha := ConcreteCategory.congr_hom
      (coinducedRegularHomologyZeroIso_augmentation σ hfin hinj hR hA I u) (eh.inv φ)
    exact ha.trans (ConcreteCategory.congr_hom eh.inv_hom_id φ)
  have hf : F x = Ext.mk₀ (originalCoinducedFunctional σ φ) :=
    (congrArg F hx.symm).trans (coinducedSingleHomologyExt_regular_augmentation σ I u φ)
  exact (congrArg Ext.addEquiv₀ hf).trans (Ext.addEquiv₀.apply_symm_apply _)

end CochainComplex.HomComplex


open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex

/-- Cancelling the same original augmentation identifies both normalization factors. -/
private theorem original_augmentation_normalization
    {C : Type*} [Category* C] {S U V W N : C}
    (s : S ≅ V) (b : U ≅ V) (r : V ≅ W) (j : U ≅ W) (t : U ≅ N)
    (h : b.hom ≫ r.hom = j.hom) :
    (s ≪≫ r ≪≫ j.symm) ≪≫ t = s ≪≫ b.symm ≪≫ t := by
  have hr : r.hom ≫ j.inv = b.inv := by
    apply (cancel_epi b.hom).mp
    rw [← Category.assoc, h, j.hom_inv_id, b.hom_inv_id]
  apply Iso.ext
  change (s.hom ≫ r.hom ≫ j.inv) ≫ t.hom = s.hom ≫ b.inv ≫ t.hom
  rw [hr, Category.assoc]

namespace CochainComplex.HomComplex.TwoLayerDual

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  [HasDerivedCategory.{v} (ModuleCat.{u} A)]
  (σ : R →+* A) [IsLocalHom σ] (hfin : σ.Finite) (hinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
  (I : InjectiveResolution (ModuleCat.of R R))

/-- The original TwoLayer unit coordinate uses exactly the finite-normal
regular-source normalization, after its unchanged native single-model comparison. -/
theorem unitNormalization_eq_regularHomologyZeroIso :
    letI : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
      restrictedProjective_of_finite_normal_dimension_two σ hfin hinj hR hA
    unitNormalization σ I =
      singleHomologyIso (resolutionCoefficient σ I) (ModuleCat.of A A) 0 ≪≫
        coinducedRegularHomologyZeroIso σ hfin hinj hR hA I.cochainComplex I.ι' := by
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hfin hinj hR hA
  let J := resolutionCoefficient σ I
  let b := coinducedRegularHomAugmentation σ I.cochainComplex I.ι'
  let j := coinducedCoefficientAugmentation σ I.cochainComplex I.ι'
  let : QuasiIso b :=
    coinducedRegularHomAugmentation_quasiIso σ hfin hinj hR hA I.cochainComplex I.ι'
  let : QuasiIso j := coefficientAugmentation_quasiIso σ I
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) 0
  let s := singleHomologyIso J (ModuleCat.of A A) 0
  let eB := isoOfQuasiIsoAt b 0
  let eR := H.mapIso (regularSingleComplexIso J)
  let eJ := isoOfQuasiIsoAt j 0
  let t := singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)
  have h : eB.hom ≫ eR.hom = eJ.hom := by
    change H.map b ≫ H.map (regularSingleComplexIso J).hom = H.map j
    exact (H.map_comp b (regularSingleComplexIso J).hom).symm.trans
      (congrArg H.map
        (coinducedRegularHomAugmentation_evaluation σ I.cochainComplex I.ι'))
  change (s ≪≫ eR ≪≫ eJ.symm) ≪≫ t = s ≪≫ eB.symm ≪≫ t
  exact original_augmentation_normalization s eB eR eJ t h

end CochainComplex.HomComplex.TwoLayerDual


universe w

namespace CochainComplex.HomComplex.TwoLayerDual

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  [HasDerivedCategory.{v} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasExt.{u} (ModuleCat.{u} R)]
  (σ : R →+* A) [IsLocalHom σ] (hfin : σ.Finite) (hinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
  (I : InjectiveResolution (ModuleCat.of R R))

/-- The actual TwoLayer unit coordinate gives the original native functional under
Ext zero after the unchanged single-model and coinduction comparisons. -/
theorem unitNormalization_ext_zero :
    letI : I.cochainComplex.IsKInjective :=
      CochainComplex.isKInjective_of_injective I.cochainComplex 0
    letI : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
      restrictedProjective_of_finite_normal_dimension_two σ hfin hinj hR hA
    ∀ z : homology (resolutionCoefficient σ I) 0 (regularSource A),
      Ext.addEquiv₀ (coinducedSingleHomologyExtLinearEquiv.{u, u, u, w, u}
        σ (ModuleCat.of A A) (ModuleCat.of R R) I.cochainComplex I.ι' 0
        ((singleHomologyIso (resolutionCoefficient σ I) (ModuleCat.of A A) 0).hom z)) =
      originalCoinducedFunctional σ ((unitNormalization σ I).hom z) := by
  let : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hfin hinj hR hA
  intro z
  let s := singleHomologyIso (resolutionCoefficient σ I) (ModuleCat.of A A) 0
  let E := coinducedRegularHomologyZeroIso σ hfin hinj hR hA I.cochainComplex I.ι'
  have hr := coinducedRegularHomologyZeroIso_ext_zero σ hfin hinj hR hA
    I.cochainComplex I.ι' (s.hom z)
  have hz := ConcreteCategory.congr_hom
    (congrArg (fun e => e.hom)
      (unitNormalization_eq_regularHomologyZeroIso σ hfin hinj hR hA I)) z
  change (unitNormalization σ I).hom z = E.hom (s.hom z) at hz
  exact hr.trans (congrArg (originalCoinducedFunctional σ) hz.symm)

end CochainComplex.HomComplex.TwoLayerDual
