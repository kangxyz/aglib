/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Derived

/-!
# Native single and affine transports for curve Serre duality
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- Native homology shift maps preserve the original shifted composition.
This retains the shift-addition comparison and hence the native signs. -/
theorem CategoryTheory.Functor.shiftMap_shiftedComp
    {A B : Type*} [Category* A] [HasShift A ℤ] [Category* B]
    (H : A ⥤ B) [H.ShiftSequence ℤ] {X Y Z : A}
    {a b c i l m : ℤ} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (hab : b + a = c) (hil : a + i = l) (hlm : b + l = m) :
    H.shiftMap (f.comp g hab) i m (by omega) =
      H.shiftMap f i l hil ≫ H.shiftMap g l m hlm := by
  have h := H.shiftIso_hom_app_comp_shiftMap g a c hab i l m hil hlm
  simpa only [Functor.shiftMap, ShiftedHom.comp, Functor.map_comp, Category.assoc] using
    congrArg (fun z => (H.shift i).map f ≫ z) h.symm


namespace CategoryTheory.Functor

/-- Fully faithful transport of original shifted morphisms, with the
installed shift comparison as the forward map. -/
def cmCurveShiftedHomEquiv {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] (F : A ⥤ B) [F.Full] [F.Faithful] [F.CommShift ℤ]
    (X Y : A) (s : ℤ) : ShiftedHom X Y s ≃ ShiftedHom (F.obj X) (F.obj Y) s :=
  (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
    (Iso.homCongr (Iso.refl _) ((F.commShiftIso s).app Y))

/-- The forward transport is the native shifted functor map. -/
theorem cmCurveShiftedHomEquiv_apply {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] (F : A ⥤ B) [F.Full] [F.Faithful] [F.CommShift ℤ]
    {X Y : A} {s : ℤ} (f : ShiftedHom X Y s) :
    F.cmCurveShiftedHomEquiv X Y s f = f.map F := by
  change 𝟙 _ ≫ F.map f ≫ (F.commShiftIso s).hom.app Y = _
  exact Category.id_comp _

/-- The inverse is the original fully faithful preimage and native shift inverse. -/
theorem cmCurveShiftedHomEquiv_symm_apply {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] (F : A ⥤ B) [F.Full] [F.Faithful] [F.CommShift ℤ]
    {X Y : A} {s : ℤ} (f : ShiftedHom (F.obj X) (F.obj Y) s) :
    (F.cmCurveShiftedHomEquiv X Y s).symm f =
      F.preimage (f ≫ (F.commShiftIso s).inv.app Y) := by
  change F.preimage (𝟙 _ ≫ f ≫ (F.commShiftIso s).inv.app Y) = _
  rw [Category.id_comp]

/-- Original shifted preimages retain native composition, including its signs. -/
theorem cmCurveShiftedHomEquiv_symm_comp
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) [F.Full] [F.Faithful] [F.CommShift ℤ]
    {X Y Z : A} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom (F.obj Y) (F.obj Z) b) (h : b + a = c) :
    (F.cmCurveShiftedHomEquiv X Z c).symm ((f.map F).comp g h) =
      f.comp ((F.cmCurveShiftedHomEquiv Y Z b).symm g) h := by
  apply (F.cmCurveShiftedHomEquiv X Z c).injective
  rw [Equiv.apply_symm_apply, F.cmCurveShiftedHomEquiv_apply]
  exact ((ShiftedHom.map_comp f _ h F).trans
    (congrArg (fun z => (f.map F).comp z h)
      ((F.cmCurveShiftedHomEquiv_apply _).symm.trans
        ((F.cmCurveShiftedHomEquiv Y Z b).apply_symm_apply g)))).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Cohomology

open RelativeCanonicalReindex

/-- Both original single normalizations are the same coefficient placement. -/
theorem cmCurveCoefficientShift_single {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (N : A) (n q i : ℤ) (hi : q + i = n) :
    ((DerivedCategory.singleFunctors A).shiftIso q i n hi).hom.app N ≫
        ((DerivedCategory.singleFunctors A).shiftIso (q - n) i 0 (by omega)).inv.app N =
      (relativeOpenCoefficientShiftIso N n q).hom := by
  have h : i = n - q := by omega
  subst i
  rfl

end AlgebraicGeometry.Scheme.Cohomology

private theorem cmCurveEqToIsoMiddle
    {A : Type*} [Category* A] {X Y Z W : A}
    (p : Y = X) (q : Y = Z) (r : Z = W) (s : X = W) :
    ((eqToIso p).inv ≫ eqToHom q) ≫ (eqToIso r).hom = (eqToIso s).hom := by
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_trans]


namespace CochainComplex

open HomologicalComplex

/-- On a single complex, the original shift map identifies its unique
homology group by the identity of the coefficient object. The middle
component carries no differential sign. -/
theorem cmCurveSingleShift_homology {A : Type*} [Category* A] [Abelian A]
    (N : A) (s i : ℤ) (h : s + i = 0) :
    (HomologicalComplex.homologyFunctor A (.up ℤ) 0).shiftMap
        (((CochainComplex.singleFunctors A).shiftIso s i 0 h).inv.app N)
        i 0 h ≫ (singleObjHomologySelfIso (.up ℤ) 0 N).hom =
      (singleObjHomologySelfIso (.up ℤ) i N).hom := by
  let K := (CochainComplex.singleFunctor A i).obj N
  let L := (CochainComplex.singleFunctor A 0).obj N
  let b : ShiftedHom K L s :=
    ((CochainComplex.singleFunctors A).shiftIso s i 0 h).inv.app N
  let φ : K.sc i ⟶ L.sc 0 :=
    (HomologicalComplex.shortComplexFunctor A (.up ℤ) i).map b ≫
      (CochainComplex.shiftShortComplexFunctorIso A s i 0 h).hom.app L
  have hmap : (HomologicalComplex.homologyFunctor A (.up ℤ) 0).shiftMap b i 0 h =
      ShortComplex.homologyMap φ := by
    change HomologicalComplex.homologyMap b i ≫
      (CochainComplex.ShiftSequence.shiftIso A s i 0 h).hom.app L = _
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    exact (ShortComplex.homologyMap_comp _ _).symm
  have hmid : φ.τ₂ ≫ (singleObjXSelf (.up ℤ) 0 N).hom =
      (singleObjXSelf (.up ℤ) i N).hom := by
    simp only [φ, ShortComplex.comp_τ₂,
      HomologicalComplex.shortComplexFunctor_map_τ₂,
      CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂]
    have hs : s = -i := by omega
    subst s
    simp only [b, CochainComplex.singleFunctors, HomologicalComplex.Hom.isoOfComponents,
      singleObjXSelf, singleObjXIsoOfEq, HomologicalComplex.XIsoOfEq,
      HomologicalComplex.single]
    exact cmCurveEqToIsoMiddle
      (by
        change (L⟦(-i)⟧).X i = K.X i
        simp [K, L, CochainComplex.shiftFunctor_obj_X',
          CochainComplex.singleFunctor])
      (by
        change (L⟦(-i)⟧).X i = L.X 0
        simp [L, CochainComplex.shiftFunctor_obj_X']) _ _
  let eK : (K.sc i).homology ⟶ N := (singleObjHomologySelfIso (.up ℤ) i N).hom
  let eL : (L.sc 0).homology ⟶ N := (singleObjHomologySelfIso (.up ℤ) 0 N).hom
  let cK : (K.sc i).cycles ⟶ N := (singleObjCyclesSelfIso (.up ℤ) i N).hom
  let cL : (L.sc 0).cycles ⟶ N := (singleObjCyclesSelfIso (.up ℤ) 0 N).hom
  have hπK : (K.sc i).homologyπ ≫ eK = cK :=
    homologyπ_singleObjHomologySelfIso_hom (.up ℤ) i N
  have hπL : (L.sc 0).homologyπ ≫ eL = cL :=
    homologyπ_singleObjHomologySelfIso_hom (.up ℤ) 0 N
  have hc : ShortComplex.cyclesMap φ ≫ cL = cK := by
    change ShortComplex.cyclesMap φ ≫
      ((L.sc 0).iCycles ≫ (singleObjXSelf (.up ℤ) 0 N).hom) =
      (K.sc i).iCycles ≫ (singleObjXSelf (.up ℤ) i N).hom
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ (singleObjXSelf (.up ℤ) 0 N).hom)
        (ShortComplex.cyclesMap_i φ))).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (K.sc i).iCycles ≫ z) hmid))
  have hcoefficient : ShortComplex.homologyMap φ ≫ eL = eK := by
    apply (cancel_epi (K.sc i).homologyπ).mp
    calc
      _ = ShortComplex.cyclesMap φ ≫ (L.sc 0).homologyπ ≫ eL :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ eL) (ShortComplex.homologyπ_naturality φ))).trans
            (Category.assoc _ _ _)
      _ = ShortComplex.cyclesMap φ ≫ cL :=
        congrArg (fun z => ShortComplex.cyclesMap φ ≫ z) hπL
      _ = cK := hc
      _ = (K.sc i).homologyπ ≫ eK := hπK.symm
  exact (congrArg (fun z => z ≫ eL) hmap).trans hcoefficient

end CochainComplex

private theorem cmCurveIsoMiddleCancel
    {A : Type*} [Category* A] {P Q R T N : A}
    (c : P ⟶ Q) (f : Q ⟶ R) (E : T ≅ R) (g : R ⟶ N) :
    (c ≫ f ≫ E.inv) ≫ (E.hom ≫ g) = c ≫ f ≫ g := by
  simp only [Category.assoc, E.inv_hom_id_assoc]

private theorem cmCurveMapTriple
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {P Q R T : A} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c :=
  (F.map_comp a (b ≫ c)).trans
    (congrArg (fun t => F.map a ≫ t) (F.map_comp b c))

namespace DerivedCategory

/-- The native single/homology comparison is the original complex
single-homology map after the localization factorization. -/
theorem cmCurveSingleHomology_comparison {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (i : ℤ) (N : A) :
    (singleFunctorCompHomologyFunctorIso A i).hom.app N =
      (homologyFunctorFactors A i).hom.app ((CochainComplex.singleFunctor A i).obj N) ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) i N).hom := by
  dsimp [singleFunctorCompHomologyFunctorIso, singleFunctorsPostcompQIso]
  rw [HomologicalComplex.homologyFunctorSingleIso_hom_app]
  let K := (CochainComplex.singleFunctor A i).obj N
  let X := ((singleFunctors A).functor i).obj N
  let H := homologyFunctor A i
  let a : H.obj X ⟶ K.homology i := (homologyFunctorFactors A i).hom.app K
  let b : K.homology i ⟶ N :=
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) i N).hom
  change H.map (𝟙 X) ≫ 𝟙 _ ≫ a ≫ b = a ≫ b
  exact (congrArg (fun t => t ≫ 𝟙 _ ≫ a ≫ b) (H.map_id X)).trans
    ((Category.id_comp _).trans (Category.id_comp _))

/-- Homology of the installed single shift retains the coefficient identity.
This is the precise native sign normalization used by the curve pairing. -/
theorem cmCurveSingleShift_homology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (N : A) (s i : ℤ) (h : s + i = 0) :
    (homologyFunctor A 0).shiftMap
        (((singleFunctors A).shiftIso s i 0 h).inv.app N) i 0 h ≫
        (singleFunctorCompHomologyFunctorIso A 0).hom.app N =
      (singleFunctorCompHomologyFunctorIso A i).hom.app N := by
  let b : ShiftedHom ((CochainComplex.singleFunctor A i).obj N)
      ((CochainComplex.singleFunctor A 0).obj N) s :=
    ((CochainComplex.singleFunctors A).shiftIso s i 0 h).inv.app N
  have hb : ((singleFunctors A).shiftIso s i 0 h).inv.app N = ShiftedHom.map b Q := by
    simpa only [DerivedCategory.singleFunctors, ShiftedHom.map] using
      (SingleFunctors.postcomp_shiftIso_inv_app
        (CochainComplex.singleFunctors A) Q s i 0 h N)
  let K := (CochainComplex.singleFunctor A i).obj N
  let L := (CochainComplex.singleFunctor A 0).obj N
  let E₀ := (homologyFunctorFactors A 0).app L
  let c : (homologyFunctor A i).obj (Q.obj K) ⟶ K.homology i :=
    (homologyFunctorFactors A i).hom.app K
  let f : K.homology i ⟶ L.homology 0 :=
    (HomologicalComplex.homologyFunctor A (.up ℤ) 0).shiftMap b i 0 h
  let z : L.homology 0 ⟶ N :=
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 N).hom
  let σ : (homologyFunctor A 0).obj (Q.obj L) ⟶ N :=
    (singleFunctorCompHomologyFunctorIso A 0).hom.app N
  have hQ : (homologyFunctor A 0).shiftMap (ShiftedHom.map b Q) i 0 h =
      c ≫ f ≫ E₀.inv := shiftMap_homologyFunctor_map_Q b i 0 h
  have hσ : σ = E₀.hom ≫ z := cmCurveSingleHomology_comparison 0 N
  have hf : f ≫ z =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) i N).hom :=
    CochainComplex.cmCurveSingleShift_homology N s i h
  let P := (homologyFunctor A i).obj (Q.obj K)
  let a₀ : P ⟶ N := (homologyFunctor A 0).shiftMap
    (((singleFunctors A).shiftIso s i 0 h).inv.app N) i 0 h ≫ σ
  let a₁ : P ⟶ N := (homologyFunctor A 0).shiftMap (ShiftedHom.map b Q) i 0 h ≫ σ
  let a₂ : P ⟶ N := (c ≫ f ≫ E₀.inv) ≫ σ
  let a₃ : P ⟶ N := (c ≫ f ≫ E₀.inv) ≫ (E₀.hom ≫ z)
  let a₄ : P ⟶ N := c ≫ f ≫ z
  let a₅ : P ⟶ N := c ≫
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) i N).hom
  have h₀ : a₀ = a₁ :=
    congrArg (fun t => (homologyFunctor A 0).shiftMap t i 0 h ≫ σ) hb
  have h₁ : a₁ = a₂ := congrArg (fun t => t ≫ σ) hQ
  have h₂ : a₂ = a₃ := congrArg (fun t => (c ≫ f ≫ E₀.inv) ≫ t) hσ
  have h₃ : a₃ = a₄ := cmCurveIsoMiddleCancel c f E₀ z
  have h₄ : a₄ = a₅ := congrArg (fun t => c ≫ t) hf
  have h₅ : a₅ = (singleFunctorCompHomologyFunctorIso A i).hom.app N :=
    (cmCurveSingleHomology_comparison i N).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))

end DerivedCategory


namespace CategoryTheory.ShiftedHom

/-- A commuting source comparison transports the original shifted
composition, including the installed addition isomorphism. -/
theorem cmCurveSourceIso_comp {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] (F G : A ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] (e : F ≅ G) [e.hom.CommShift ℤ]
    {X Y : A} {Z : B} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom (G.obj Y) Z b) (h : b + a = c) :
    (mk₀ (0 : ℤ) rfl (e.hom.app X)).comp ((f.map G).comp g h) (add_zero c) =
      (f.map F).comp ((mk₀ (0 : ℤ) rfl (e.hom.app Y)).comp g (add_zero b)) h := by
  calc
    _ = ((mk₀ (0 : ℤ) rfl (e.hom.app X)).comp (f.map G) (add_zero a)).comp g h :=
      (comp_assoc _ _ _ (add_zero a) h (by omega)).symm
    _ = ((f.map F).comp (mk₀ (0 : ℤ) rfl (e.hom.app Y)) (zero_add a)).comp g h :=
      congrArg (fun z => z.comp g h) (map_naturality f e.hom).symm
    _ = _ := comp_assoc _ _ _ (zero_add a) (add_zero b) (by omega)

end CategoryTheory.ShiftedHom


namespace DerivedCategory

/-- Extracting homology after the installed single shift is the native
shift map followed by the degree-zero coefficient identification. -/
theorem cmCurveHomToShiftSingle_homology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {X : DerivedCategory A} (N : A) (s i : ℤ)
    (h : s + i = 0)
    (f : X ⟶ ((singleFunctor A 0).obj N)⟦s⟧) :
    (homologyFunctor A i).map
        (f ≫ ((singleFunctors A).shiftIso s i 0 h).hom.app N) ≫
        (singleFunctorCompHomologyFunctorIso A i).hom.app N =
      (homologyFunctor A 0).shiftMap f i 0 h ≫
        (singleFunctorCompHomologyFunctorIso A 0).hom.app N := by
  let H := (homologyFunctor A 0).shift i
  let J := ((singleFunctors A).shiftIso s i 0 h).app N
  let σ := ((homologyFunctor A 0).shiftIso s i 0 h).hom.app
    ((singleFunctor A 0).obj N)
  have hsingle : H.map J.inv ≫ σ ≫
      (singleFunctorCompHomologyFunctorIso A 0).hom.app N =
      (singleFunctorCompHomologyFunctorIso A i).hom.app N := by
    exact (Category.assoc _ _ _).symm.trans (cmCurveSingleShift_homology N s i h)
  have htarget : H.map J.hom ≫ (singleFunctorCompHomologyFunctorIso A i).hom.app N =
      σ ≫ (singleFunctorCompHomologyFunctorIso A 0).hom.app N := by
    calc
      _ = H.map J.hom ≫ (H.map J.inv ≫ σ ≫
          (singleFunctorCompHomologyFunctorIso A 0).hom.app N) :=
        congrArg (fun z => H.map J.hom ≫ z) hsingle.symm
      _ = _ := by
        rw [← Category.assoc, ← H.map_comp, J.hom_inv_id, H.map_id, Category.id_comp]
  have hresult : H.map (f ≫ J.hom) ≫
        (singleFunctorCompHomologyFunctorIso A i).hom.app N =
      (homologyFunctor A 0).shiftMap f i 0 h ≫
        (singleFunctorCompHomologyFunctorIso A 0).hom.app N := by
    exact (congrArg (fun z => z ≫ (singleFunctorCompHomologyFunctorIso A i).hom.app N)
      (H.map_comp f J.hom)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => H.map f ≫ z) htarget).trans (Category.assoc _ _ _).symm))
  simpa only [H, J, Iso.app_hom, DerivedCategory.shift_homologyFunctor] using hresult

end DerivedCategory


namespace DerivedCategory.Plus

/-- The installed homology shift sequence on bounded-below objects is the
original full-derived shift sequence after the native inclusion. -/
theorem cmCurveHomology_shiftMap_full
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K L : Plus A} {s a b : ℤ} (t : ShiftedHom K L s) (h : s + a = b) :
    (homologyFunctor A 0).shiftMap t a b h =
      (DerivedCategory.homologyFunctor A 0).shiftMap
        (t.map DerivedCategory.Plus.ι) a b h := by
  let H := DerivedCategory.homologyFunctor A 0
  let ι : Plus A ⥤ DerivedCategory A := DerivedCategory.Plus.ι
  let c : (L⟦s⟧).obj ⟶ L.obj⟦s⟧ := (ι.commShiftIso s).hom.app L
  let e : (H.shift a).obj (L.obj⟦s⟧) ≅ (H.shift b).obj L.obj :=
    (H.shiftIso s a b h).app L.obj
  change (H.shift a).map t.hom ≫ (𝟙 _ ≫ (H.shift a).map c ≫ 𝟙 _ ≫ e.hom) =
    (H.shift a).map (t.hom ≫ c) ≫ e.hom
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]


/-- The native bounded-below shift sequence uses the original homology
functor in its displayed degree. -/
theorem cmCurve_shift_homologyFunctor
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] (i : ℤ) :
    (homologyFunctor A 0).shift i = homologyFunctor A i := by
  change DerivedCategory.Plus.ι ⋙ (DerivedCategory.homologyFunctor A 0).shift i =
    DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor A i
  exact congrArg (fun H => DerivedCategory.Plus.ι ⋙ H)
    (DerivedCategory.shift_homologyFunctor A i)

/-- Ordinary native homology maps retain the actual bounded-below inclusion. -/
theorem cmCurve_homology_map_full
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K L : Plus A} (f : K ⟶ L) (i : ℤ) :
    (homologyFunctor A i).map f =
      (DerivedCategory.homologyFunctor A i).map (DerivedCategory.Plus.ι.map f) := rfl

end DerivedCategory.Plus


namespace CategoryTheory.Functor

/-- Degree-zero native shift maps are ordinary functor maps. -/
theorem cmCurveShiftMap_mk₀ {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] (H : A ⥤ B) [H.ShiftSequence ℤ]
    {X Y : A} (f : X ⟶ Y) (i : ℤ) :
    H.shiftMap (ShiftedHom.mk₀ (0 : ℤ) rfl f) i i (zero_add i) = (H.shift i).map f := by
  simp [Functor.shiftMap, ShiftedHom.mk₀, shiftFunctorZero', H.shiftIso_zero_hom_app]


/-- The original degree-zero shifted embedding cancels the native zero shift. -/
theorem cmCurveMk₀_postZero
    {A : Type*} [Category* A] [HasShift A ℤ] {X Y : A} (f : X ⟶ Y) :
    ShiftedHom.mk₀ (0 : ℤ) rfl f ≫ (shiftFunctorZero A ℤ).hom.app Y = f := by
  have h : ShiftedHom.mk₀ (0 : ℤ) rfl f ≫
      (shiftFunctorZero' A (0 : ℤ) rfl).hom.app Y = f :=
    (ShiftedHom.homEquiv (M := ℤ) (0 : ℤ) rfl).left_inv f
  simpa only [shiftFunctorZero', eqToIso_refl, Iso.refl_trans] using h

/-- Original zero-shift normalization determines the original shifted map. -/
theorem cmCurveEqMk₀_of_postZero
    {A : Type*} [Category* A] [HasShift A ℤ] {X Y : A}
    (f : ShiftedHom X Y (0 : ℤ)) (g : X ⟶ Y)
    (h : f ≫ (shiftFunctorZero A ℤ).hom.app Y = g) :
    f = ShiftedHom.mk₀ (0 : ℤ) rfl g := by
  apply (cancel_mono ((shiftFunctorZero A ℤ).hom.app Y)).mp
  exact h.trans (cmCurveMk₀_postZero g).symm

/-- The original output iso can be cancelled through its actual inverse. -/
theorem cmCurveOutputIsoInverse
    {A : Type*} [Category* A] {X Y Z : A} (E : Y ≅ Z)
    (f : X ⟶ Y) (g : X ⟶ Z) (h : f ≫ E.hom = g) : f = g ≫ E.inv := by
  apply (cancel_mono E.hom).mp
  have hR : (g ≫ E.inv) ≫ E.hom = g :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => g ≫ z) E.inv_hom_id).trans (Category.comp_id _))
  exact h.trans hR.symm

end CategoryTheory.Functor

namespace DerivedCategory

/-- Degree-zero shifted homology on the full model is its original map. -/
theorem cmCurve_homology_shiftMap_mk₀
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K L : DerivedCategory A} (f : K ⟶ L) :
    (homologyFunctor A 0).shiftMap (ShiftedHom.mk₀ (0 : ℤ) rfl f) 0 0 (by omega) =
      (homologyFunctor A 0).map f := by
  have h := Functor.cmCurveShiftMap_mk₀ (homologyFunctor A 0) f 0
  simpa only [DerivedCategory.shift_homologyFunctor] using h

end DerivedCategory

namespace DerivedCategory.Plus

/-- Degree-zero shifted homology on the native bounded-below model is its original map. -/
theorem cmCurve_homology_shiftMap_mk₀
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K L : Plus A} (f : K ⟶ L) :
    (homologyFunctor A 0).shiftMap (ShiftedHom.mk₀ (0 : ℤ) rfl f) 0 0 (by omega) =
      (homologyFunctor A 0).map f := by
  let I := DerivedCategory.Plus.ι (C := A)
  have hm : (ShiftedHom.mk₀ (0 : ℤ) rfl f).map I =
      ShiftedHom.mk₀ (0 : ℤ) rfl (I.map f) :=
    ShiftedHom.map_mk₀ (0 : ℤ) rfl f I
  let P := (homologyFunctor A 0).obj K
  let Q := (homologyFunctor A 0).obj L
  let a₀ : P ⟶ Q := (homologyFunctor A 0).shiftMap
    (ShiftedHom.mk₀ (0 : ℤ) rfl f) 0 0 (by omega)
  let a₁ : P ⟶ Q := (DerivedCategory.homologyFunctor A 0).shiftMap
    ((ShiftedHom.mk₀ (0 : ℤ) rfl f).map I) 0 0 (by omega)
  let a₂ : P ⟶ Q := (DerivedCategory.homologyFunctor A 0).shiftMap
    (ShiftedHom.mk₀ (0 : ℤ) rfl (I.map f)) 0 0 (by omega)
  let a₃ : P ⟶ Q := (homologyFunctor A 0).map f
  have h₀ : a₀ = a₁ := cmCurveHomology_shiftMap_full _ (by omega)
  have h₁ : a₁ = a₂ :=
    congrArg (fun t => (DerivedCategory.homologyFunctor A 0).shiftMap t 0 0
      (show (0 : ℤ) + 0 = 0 by omega)) hm
  have h₂ : a₂ = a₃ := DerivedCategory.cmCurve_homology_shiftMap_mk₀ (I.map f)
  exact h₀.trans (h₁.trans h₂)

end DerivedCategory.Plus



namespace DerivedCategory

/-- The fully faithful single preimage is its original normalized
homology map. -/
theorem cmCurveSinglePreimage_homology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {M N : A} (i : ℤ)
    (f : (singleFunctor A i).obj M ⟶ (singleFunctor A i).obj N) :
    (singleFunctorCompHomologyFunctorIso A i).inv.app M ≫
      (homologyFunctor A i).map f ≫
      (singleFunctorCompHomologyFunctorIso A i).hom.app N =
      (singleFunctor A i).preimage f := by
  let g := (singleFunctor A i).preimage f
  have h := (singleFunctorCompHomologyFunctorIso A i).hom.naturality g
  change (homologyFunctor A i).map ((singleFunctor A i).map g) ≫
      (singleFunctorCompHomologyFunctorIso A i).hom.app N =
    (singleFunctorCompHomologyFunctorIso A i).hom.app M ≫ g at h
  rw [(singleFunctor A i).map_preimage] at h
  exact (congrArg (fun z => (singleFunctorCompHomologyFunctorIso A i).inv.app M ≫ z) h).trans
    (Iso.inv_hom_id_app_assoc (singleFunctorCompHomologyFunctorIso A i) M g)

end DerivedCategory


namespace AlgebraicGeometry.Scheme.Cohomology

open RelativeCanonicalReindex

/-- The original reindexing is the same native coefficient placement
for every complementary integer degree. -/
theorem cmCurveReindexCoefficient {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (N : A) (n q s i : ℤ)
    (hqn : q - s = n) (hsi : s + i = 0) :
    (singleReindexIso N n q s hqn).inv =
      ((DerivedCategory.singleFunctors A).shiftIso q i n (by omega)).hom.app N ≫
        ((DerivedCategory.singleFunctors A).shiftIso s i 0 hsi).inv.app N := by
  have hi : i = -s := by omega
  subst i
  unfold singleReindexIso
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv]

/-- The zero output shift is the original trace target normalization. -/
theorem cmCurveSingleReindexTrace {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (N : A) (m : ℤ) :
    (singleReindexIso N m m 0 (by omega)).inv ≫
        (shiftFunctorZero (DerivedCategory A) ℤ).hom.app
          ((DerivedCategory.singleFunctor A 0).obj N) =
      ((DerivedCategory.singleFunctors A).shiftIso m 0 m (by omega)).hom.app N := by
  let Z := (shiftFunctorZero (DerivedCategory A) ℤ).app
    ((DerivedCategory.singleFunctor A 0).obj N)
  have h := cmCurveReindexCoefficient N m m 0 0 (by omega) (by omega)
  have hJ : ((DerivedCategory.singleFunctors A).shiftIso 0 0 0 (by omega)).inv.app N ≫
      Z.hom = 𝟙 _ :=
    (congrArg (fun f => f ≫ Z.hom)
      ((DerivedCategory.singleFunctors A).shiftIso_zero_inv_app 0 N)).trans Z.inv_hom_id
  exact (congrArg (fun f => f ≫ Z.hom) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f =>
        ((DerivedCategory.singleFunctors A).shiftIso m 0 m (by omega)).hom.app N ≫ f) hJ).trans
          (Category.comp_id _)))

/-- The affine zero-coefficient shift is literally the inverse of the
original reindexing at its displayed integer degree. -/
theorem cmCurveCoefficientShift_reindex {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (N : A) (n q : ℤ) :
    (relativeOpenCoefficientShiftIso N n q).hom =
      (singleReindexIso N n q (q - n) (by omega)).inv := by
  unfold relativeOpenCoefficientShiftIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  exact (cmCurveReindexCoefficient N n q (q - n) (n - q) (by omega) (by omega)).symm

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveModelModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

/-- Right whiskering followed by the native associator is the
comparison for the actual parenthesized composite functor. -/
def cmCurveWhiskerRightAssoc
    {S A B M : Type*} [Category* S] [Category* A] [Category* B] [Category* M]
    {F : S ⥤ B} {D : S ⥤ A} {G : A ⥤ B} (E : F ≅ D ⋙ G) (I : B ⥤ M) :
    F ⋙ I ≅ D ⋙ (G ⋙ I) :=
  Functor.isoWhiskerRight E I ≪≫ Functor.associator D G I

/-- The original source component is unchanged by the native associator. -/
theorem cmCurveWhiskerRightAssoc_hom_app
    {S A B M : Type*} [Category* S] [Category* A] [Category* B] [Category* M]
    {F : S ⥤ B} {D : S ⥤ A} {G : A ⥤ B} (E : F ≅ D ⋙ G) (I : B ⥤ M) (X : S) :
    (cmCurveWhiskerRightAssoc E I).hom.app X = I.map (E.hom.app X) := by
  simp only [cmCurveWhiskerRightAssoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]

/-- The same parenthesized comparison retains the native shift structure. -/
instance cmCurveWhiskerRightAssoc_commShift
    {S A B M : Type*} [Category* S] [Category* A] [Category* B] [Category* M]
    [HasShift S ℤ] [HasShift A ℤ] [HasShift B ℤ] [HasShift M ℤ]
    {F : S ⥤ B} {D : S ⥤ A} {G : A ⥤ B}
    [F.CommShift ℤ] [D.CommShift ℤ] [G.CommShift ℤ]
    (E : F ≅ D ⋙ G) [E.hom.CommShift ℤ] (I : B ⥤ M) [I.CommShift ℤ] :
    (cmCurveWhiskerRightAssoc E I).hom.CommShift ℤ := by
  dsimp only [cmCurveWhiskerRightAssoc, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The same shifted original arrow, transported through a native fully
faithful inclusion, a native shifted functor, and its actual endpoint maps. -/
def cmCurveModuleHomOfIso
    {A B M : Type*} [Category* A] [Category* B] [Category* M]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift M ℤ]
    (I : A ⥤ B) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (F : A ⥤ M) [F.CommShift ℤ] {K N : A} {L T : M}
    (c : L ⟶ F.obj K) (t : F.obj N ⟶ T) (s : ℤ)
    (φ : ShiftedHom (I.obj K) (I.obj N) s) : ShiftedHom L T s :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl c).comp
    ((((I.cmCurveShiftedHomEquiv K N s).symm φ).map F).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl t) (zero_add s)) (add_zero s)

/-- The shared constructor is the original preimage and shifted functor map. -/
theorem cmCurveModuleHomOfIso_apply
    {A B M : Type*} [Category* A] [Category* B] [Category* M]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift M ℤ]
    (I : A ⥤ B) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (F : A ⥤ M) [F.CommShift ℤ] {K N : A} {L T : M}
    (c : L ⟶ F.obj K) (t : F.obj N ⟶ T) (s : ℤ)
    (φ : ShiftedHom (I.obj K) (I.obj N) s) :
    cmCurveModuleHomOfIso I F c t s φ =
      c ≫ (ShiftedHom.map (I.preimage (φ ≫ (I.commShiftIso s).inv.app N)) F) ≫ t⟦s⟧' := by
  unfold cmCurveModuleHomOfIso
  rw [Functor.cmCurveShiftedHomEquiv_symm_apply, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

/-- The shared original-map constructor retains all native source shifts. -/
theorem cmCurveModuleHomOfIso_comp
    {S A B M : Type*} [Category* S] [Category* A] [Category* B] [Category* M]
    [HasShift S ℤ] [HasShift A ℤ] [HasShift B ℤ] [HasShift M ℤ]
    (D : S ⥤ A) [D.CommShift ℤ] (H : S ⥤ M) [H.CommShift ℤ]
    (I : A ⥤ B) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (F : A ⥤ M) [F.CommShift ℤ] (E : H ≅ D ⋙ F) [E.hom.CommShift ℤ]
    {X Y : S} {N : A} {T : M} (t : F.obj N ⟶ T) {a b c : ℤ}
    (f : ShiftedHom X Y a) (φ : ShiftedHom (I.obj (D.obj Y)) (I.obj N) b)
    (hab : b + a = c) :
    cmCurveModuleHomOfIso I F (E.hom.app X) t c ((f.map (D ⋙ I)).comp φ hab) =
      (f.map H).comp (cmCurveModuleHomOfIso I F (E.hom.app Y) t b φ) hab := by
  have hv : (I.cmCurveShiftedHomEquiv (D.obj X) N c).symm
      ((f.map (D ⋙ I)).comp φ hab) =
      (f.map D).comp ((I.cmCurveShiftedHomEquiv (D.obj Y) N b).symm φ) hab := by
    simpa only [ShiftedHom.comp_map] using
      I.cmCurveShiftedHomEquiv_symm_comp (Z := N) (f.map D) φ hab
  unfold cmCurveModuleHomOfIso
  rw [hv, ShiftedHom.map_comp, ← ShiftedHom.comp_map]
  rw [ShiftedHom.comp_assoc _ _ _ hab (zero_add b) (by omega)]
  exact ShiftedHom.cmCurveSourceIso_comp H (D ⋙ F) E f
    ((((I.cmCurveShiftedHomEquiv (D.obj Y) N b).symm φ).map F).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl t) (zero_add b)) hab

/-- Degree-zero values of the same constructor use the original mapped
arrow and original endpoint maps. -/
theorem cmCurveModuleHomOfIso_mk₀
    {A B M : Type*} [Category* A] [Category* B] [Category* M]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift M ℤ]
    (I : A ⥤ B) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (F : A ⥤ M) [F.CommShift ℤ] {K N : A} {L T : M}
    (c : L ⟶ F.obj K) (t : F.obj N ⟶ T) (f : K ⟶ N) :
    cmCurveModuleHomOfIso I F c t 0 (ShiftedHom.mk₀ (0 : ℤ) rfl (I.map f)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (c ≫ F.map f ≫ t) := by
  have hv : (I.cmCurveShiftedHomEquiv K N (0 : ℤ)).symm
      (ShiftedHom.mk₀ (0 : ℤ) rfl (I.map f)) = ShiftedHom.mk₀ (0 : ℤ) rfl f := by
    apply (I.cmCurveShiftedHomEquiv K N (0 : ℤ)).injective
    rw [Equiv.apply_symm_apply, I.cmCurveShiftedHomEquiv_apply, ShiftedHom.map_mk₀]
  unfold cmCurveModuleHomOfIso
  rw [hv, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]

/-- The module-valued original arrow is obtained by the actual global
sections comparison, native derived sections, and original affine unit
coefficient isomorphism. -/
def cmCurveSerreModuleHom (F : C.Modules) (s : ℤ)
    (φ : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦s⟧) :
    cmCurveSerreDerivedSections k ι j F ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))⟦s⟧ := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let c := IM.map ((moduleDerivedGlobalSectionsPushforwardCompIso p
    (Scheme.ΓSpecIso (.of k)).inv.hom).hom.app
      ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F))
  let t := IM.map (affineDerivedStructureTargetIso (.of k)).hom
  exact cmCurveModuleHomOfIso IY RF c t s φ

omit [IsClosedImmersion j] in
/-- The module-valued specialization has the same original preimage,
composition comparison, and native coefficient map. -/
theorem cmCurveSerreModuleHom_apply (F : C.Modules) (s : ℤ)
    (φ : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦s⟧) :
    let p := j ≫ toSpec k ι
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
    let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
    let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let v : ShiftedHom
        ((derivedPushforwardPlus p).obj ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F))
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) s :=
      IY.preimage (φ ≫ (IY.commShiftIso s).inv.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O))
    cmCurveSerreModuleHom k ι j F s φ =
      IM.map ((moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of
        k)).inv.hom).hom.app
          ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)) ≫
        v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map (affineDerivedStructureTargetIso (.of
          k)).hom)⟦s⟧' := by
  dsimp only
  unfold cmCurveSerreModuleHom
  exact cmCurveModuleHomOfIso_apply _ _ _ _ _ _

omit [IsClosedImmersion j] in
/-- The actual module-valued arrow retains all native source Ext actions. -/
theorem cmCurveSerreModuleHom_comp {F F' : C.Modules} {a : ℕ} {b c : ℤ}
    (η : Ext.{u + 1} (C := C.Modules) F F' a)
    (φ : cmCurveSerreDirectImage k ι j F' ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦b⟧)
    (hab : b + (a : ℤ) = c) :
    cmCurveSerreModuleHom k ι j F c
        ((η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
          DerivedCategory.Plus.ι)).comp φ hab) =
      (η.homPlus.map ((moduleGlobalSectionsFunctorOfHom C
        (cmCurveSerreScalar k ι j)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι)).comp
        (cmCurveSerreModuleHom k ι j F' b φ) hab := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let S := DerivedCategory.Plus.singleFunctor C.Modules 0
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let D := derivedPushforwardPlus p
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let H := (moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)).rightDerivedFunctorPlus
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let Cmp : H ≅ D ⋙ G.rightDerivedFunctorPlus :=
    moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Cmp.hom.CommShift ℤ :=
    moduleDerivedGlobalSectionsPushforwardCompIso_commShift p
      (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := cmCurveWhiskerRightAssoc Cmp IM
  let t := IM.map (affineDerivedStructureTargetIso (.of k)).hom
  let θ := (η.homPlus.map (D ⋙ IY)).comp φ hab
  have hL := congrArg
    (fun c' => cmCurveModuleHomOfIso IY RF c' t c θ)
    (cmCurveWhiskerRightAssoc_hom_app Cmp IM (S.obj F)).symm
  have hG := cmCurveModuleHomOfIso_comp D (H ⋙ IM) IY RF E t η.homPlus φ hab
  have hR := congrArg
    (fun c' => (η.homPlus.map (H ⋙ IM)).comp
      (cmCurveModuleHomOfIso IY RF c' t b φ) hab)
    (cmCurveWhiskerRightAssoc_hom_app Cmp IM (S.obj F'))
  exact hL.trans (hG.trans hR)

omit [IsClosedImmersion j] in
/-- In degree zero, no new derived arrow is chosen: the model is the
original composition comparison and original affine coefficient map. -/
theorem cmCurveSerreModuleHom_mk₀ (F : C.Modules)
    (f : (derivedPushforwardPlus (j ≫ toSpec k ι)).obj
        ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F) ⟶
      (DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj
        (cmCurveSerreUnit (Spec (.of k)))) :
    cmCurveSerreModuleHom k ι j F 0
      (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map f)) =
    ShiftedHom.mk₀ (0 : ℤ) rfl
      (DerivedCategory.Plus.ι.map
        ((moduleDerivedGlobalSectionsPushforwardCompIso (j ≫ toSpec k ι)
          (Scheme.ΓSpecIso (.of k)).inv.hom).hom.app
            ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F) ≫
          (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
            (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctorPlus.map f ≫
          (affineDerivedStructureTargetIso (.of k)).hom)) := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let c := (moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of
    k)).inv.hom).hom.app
    ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)
  let t := (affineDerivedStructureTargetIso (.of k)).hom
  have h := cmCurveModuleHomOfIso_mk₀ IY RF (IM.map c) (IM.map t) f
  exact h.trans (congrArg (ShiftedHom.mk₀ (0 : ℤ) rfl)
    ((congrArg (fun z => IM.map c ≫ z)
      (IM.map_comp (G.rightDerivedFunctorPlus.map f) t).symm).trans
        (IM.map_comp c (G.rightDerivedFunctorPlus.map f ≫ t)).symm))

/-- Original affine coefficient sections retain the original spectrum
normalization of the structural field action. -/
theorem cmCurveSerreAffineSections_coefficient :
    (moduleAffineGlobalSectionsIso (.of k)).inv.app
        (cmCurveSerreUnit (Spec (.of k))) ≫
      (cmCurveSerreSpecUnitSectionsIso k).hom =
      (moduleAffineStructureSectionsIso (.of k)).hom := by
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := moduleAffineStructureSectionsIso (.of k)
  let R := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := ConcreteCategory.congr_hom E.hom_inv_id x
  change R.symm (E.hom x) = (show Γ(Spec (.of k), ⊤) from x) at hx
  have hE : E.hom x = R (show Γ(Spec (.of k), ⊤) from x) :=
    (R.apply_symm_apply (E.hom x)).symm.trans (congrArg R hx)
  exact (cmCurveSerreSpecUnitSectionsIso_apply k _).trans hE.symm

end AlgebraicGeometry.Scheme.Cohomology

namespace CategoryTheory.Functor

/-- The original derived transformation between isomorphic additive
functors retains the native single unit. -/
theorem cmCurveRightDerivedPlusIso_singleUnit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B] (F G : A ⥤ B) [F.Additive] [G.Additive]
    (e : F ≅ G) (M : A) :
    F.rightDerivedSingleUnit M ≫ (F.rightDerivedFunctorPlusIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (DerivedCategory.Plus.singleFunctor B 0).map (e.hom.app M) ≫
        G.rightDerivedSingleUnit M := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  let S := CochainComplex.singleFunctorPlus B 0
  let Q : CochainComplex.Plus B ⥤ DerivedCategory.Plus B := DerivedCategory.Plus.Q
  let τF : S.obj (F.obj M) ⟶ F.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let τG : S.obj (G.obj M) ⟶ G.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M)
  have hτ : τF ≫ (NatIso.mapCochainComplexPlus e).hom.app K =
      S.map (e.hom.app M) ≫ τG := by
    apply ObjectProperty.hom_ext
    change (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
        (e.hom.mapHomologicalComplex (.up ℤ)).app
          ((CochainComplex.singleFunctor A 0).obj M) =
      (CochainComplex.singleFunctor B 0).map (e.hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M
    rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
    simp only [Iso.inv_hom_id_app_assoc]
  change (Q.map τF ≫ F.rightDerivedFunctorPlusUnit.app K) ≫
      (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) =
    Q.map (S.map (e.hom.app M)) ≫ (Q.map τG ≫ G.rightDerivedFunctorPlusUnit.app K)
  rw [Category.assoc, F.rightDerivedFunctorPlusIso_hom_app e K]
  rw [← Category.assoc, ← Q.map_comp, hτ, Q.map_comp, Category.assoc]

/-- The original derived-functor isomorphism commutes with shifts by
its native unit factorization, without changing either derived functor. -/
theorem cmCurveRightDerivedPlusIso_commShift
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B] (F G : A ⥤ B) [F.Additive] [G.Additive]
    (e : F ≅ G) : (F.rightDerivedFunctorPlusIso e).hom.CommShift ℤ := by
  let Q : CochainComplex.Plus A ⥤ DerivedCategory.Plus A := DerivedCategory.Plus.Q
  let β := Functor.whiskerRight (NatTrans.mapCochainComplexPlus e.hom) DerivedCategory.Plus.Q ≫
    G.rightDerivedFunctorPlusUnit
  let : β.CommShift ℤ := by
    dsimp only [β]
    infer_instance
  apply Functor.commShift_of_rightDerived_factorization Q (CochainComplex.Plus.quasiIso A)
    F.rightDerivedFunctorPlusUnit β (F.rightDerivedFunctorPlusIso e).hom
  apply NatTrans.ext
  funext K
  exact F.rightDerivedFunctorPlusIso_hom_app e K

/-- A mapped original isomorphism cancels its actual unit comparison. -/
theorem cmCurveMappedIsoUnit {A B : Type*} [Category* A] [Category* B]
    (Q : A ⥤ B) {X Y : A} (E : X ≅ Y) {Z : B}
    (u : Q.obj X ⟶ Z) (t : Z ⟶ Q.obj Y) (h : u ≫ t = Q.map E.hom) :
    (Q.map E.inv ≫ u) ≫ t = 𝟙 (Q.obj Y) := by
  rw [Category.assoc, h, ← Q.map_comp, E.inv_hom_id, Q.map_id]

/-- Acyclic-single normalization cancels the very same original derived
unit, without choosing a new comparison. -/
theorem cmCurveRightDerivedSingleUnit_acyclic
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (M : A)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    F.rightDerivedSingleUnit M ≫ (F.rightDerivedFunctorPlusSingleIsoOfAcyclic M hM).hom =
      𝟙 _ := by
  let E : F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M) ≅
      (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) :=
    (CochainComplex.plus B).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)
  exact cmCurveMappedIsoUnit DerivedCategory.Plus.Q E
    (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M))
    (F.rightDerivedFunctorPlusSingleIsoOfAcyclic M hM).hom
    (F.rightDerivedFunctorPlusSingleIsoOfAcyclic_unit M hM)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveModelCoefficientDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k]

/-- Native coefficient normalization follows from the same original
single units and the original section coefficient equation. -/
theorem cmCurveCoefficientThroughUnit {A : Type*} [Category* A]
    {P Q U V K : A} (u : P ⟶ Q) [Epi u] (v : U ⟶ V)
    (r : Q ⟶ V) (e : V ⟶ U) (ρ : P ⟶ U) (c : U ⟶ K) (t : Q ⟶ K)
    (h₁ : u ≫ r = ρ ≫ v) (h₂ : v ≫ e = 𝟙 U) (h₃ : ρ ≫ c = u ≫ t) :
    r ≫ e ≫ c = t := by
  apply (cancel_epi u).mp
  calc
    _ = (u ≫ r) ≫ e ≫ c := (Category.assoc _ _ _).symm
    _ = (ρ ≫ v) ≫ e ≫ c := congrArg (fun z => z ≫ e ≫ c) h₁
    _ = ρ ≫ c :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => ρ ≫ z)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ c) h₂).trans (Category.id_comp _)))))
    _ = _ := h₃

/-- The coefficient normalization in the affine Hom equivalence is the
original affine structural normalization, after its original section map. -/
theorem cmCurveSerreAffineDerived_coefficient :
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let U := moduleSpecΓFunctor (R := .of k)
    let : U.Additive := moduleSpecΓFunctor_additive (.of k)
    let : PreservesFiniteLimits U :=
      preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
    let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
      (AffineDerived.isZero_rightDerived_globalSections_succ O)
    (G.rightDerivedFunctorPlusIso (moduleAffineGlobalSectionsIso (.of k)).symm).hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) ≫
      E.hom ≫ (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveSerreSpecUnitSectionsIso k).hom =
      (affineDerivedStructureTargetIso (.of k)).hom := by
  dsimp only
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let ρ := (moduleAffineGlobalSectionsIso (.of k)).symm
  let R := G.rightDerivedFunctorPlusIso ρ
  let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
    (AffineDerived.isZero_rightDerived_globalSections_succ O)
  let η := G.rightDerivedSingleUnit O
  let : IsIso η := affineStructureUnit_isIso (.of k)
  let c := (moduleAffineStructureSectionsIso (.of k)).hom
  let t := (affineDerivedStructureTargetIso (.of k)).hom
  have h₁ : η ≫ R.hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) =
      S.map (ρ.hom.app O) ≫ U.rightDerivedSingleUnit O :=
    G.cmCurveRightDerivedPlusIso_singleUnit U ρ O
  have h₂ : U.rightDerivedSingleUnit O ≫ E.hom = 𝟙 _ :=
    U.cmCurveRightDerivedSingleUnit_acyclic O
      (AffineDerived.isZero_rightDerived_globalSections_succ O)
  have hc : S.map (ρ.hom.app O) ≫ S.map (cmCurveSerreSpecUnitSectionsIso k).hom =
      S.map c := (S.map_comp _ _).symm.trans
        (congrArg S.map (cmCurveSerreAffineSections_coefficient k))
  have ht : η ≫ t = S.map c := IsIso.hom_inv_id_assoc η (S.map c)
  exact cmCurveCoefficientThroughUnit η (U.rightDerivedSingleUnit O)
    (R.hom.app ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O)) E.hom
    (S.map (ρ.hom.app O)) (S.map (cmCurveSerreSpecUnitSectionsIso k).hom) t h₁ h₂
    (hc.trans ht.symm)

end AlgebraicGeometry.Scheme.Cohomology


namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveModelComparisonDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- A fixed native source square and coefficient square transport the
same affine Hom arrow after cancellation of its original target iso. -/
theorem cmCurveAffineArrowTransport {A : Type*} [Category* A]
    {P Q V W T N X K : A} (c : P ⟶ Q) (r : Q ⟶ V)
    (vU : V ⟶ T) (vG : Q ⟶ W) (rN : W ⟶ T) (e : T ⟶ N)
    (d : X ≅ N) (eN : N ⟶ K) (t : W ⟶ K)
    (hn : r ≫ vU = vG ≫ rN) (hc : rN ≫ e ≫ eN = t) :
    (c ≫ r ≫ vU ≫ e ≫ d.inv) ≫ d.hom ≫ eN = c ≫ vG ≫ t := by
  simp only [Category.assoc, d.inv_hom_id_assoc]
  rw [← Category.assoc r vU, hn]
  simpa only [Category.assoc] using congrArg (fun z => c ≫ vG ≫ z) hc

/-- The original affine Hom equivalence and the module-valued original
arrow agree after their displayed native coefficient shifts and the
original spectrum coefficient map. No comparison equation is a premise. -/
theorem cmCurveSerreAffineHom_moduleHom (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q : ℕ)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(q : ℤ)⟧) :
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F
        (cmCurveSerreUnit (Spec (.of k))) n q a ≫
      (relativeOpenCoefficientShiftIso
        ((moduleSpecΓFunctor (R := .of k)).obj
          (cmCurveSerreUnit (Spec (.of k)))) (n : ℤ) (q : ℤ)).hom ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveSerreSpecUnitSectionsIso k).hom)⟦(q : ℤ) - n⟧' =
      cmCurveSerreModuleHom k ι j F ((q : ℤ) - n)
        (a ≫ (relativeOpenCoefficientShiftIso
          (cmCurveSerreUnit (Spec (.of k))) (n : ℤ) (q : ℤ)).hom) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let S := DerivedCategory.Plus.singleFunctor C.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0
  let SM := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let D := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let ρ : G ≅ U := NatIso.ofComponents
    (fun L => (moduleTopSectionsIso (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom L).symm)
    (by intro L L' f; ext x; rfl)
  have hρ : ρ = (moduleAffineGlobalSectionsIso (.of k)).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext L
    rfl
  let R := G.rightDerivedFunctorPlusIso ρ
  let : R.hom.CommShift ℤ := G.cmCurveRightDerivedPlusIso_commShift U ρ
  let Rfull := Functor.isoWhiskerRight R IM
  let : Rfull.hom.CommShift ℤ := by
    dsimp only [Rfull, Functor.isoWhiskerRight_hom]
    infer_instance
  let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
    (AffineDerived.isZero_rightDerived_globalSections_succ O)
  let Cmp := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of k)).inv.hom
  let cY := relativeOpenCoefficientShiftIso O (n : ℤ) (q : ℤ)
  let cM := relativeOpenCoefficientShiftIso (U.obj O) (n : ℤ) (q : ℤ)
  let s : ℤ := (q : ℤ) - n
  let v : ShiftedHom (D.obj (S.obj F)) (SY.obj O) s :=
    IY.preimage ((a ≫ cY.hom) ≫ (IY.commShiftIso s).inv.app (SY.obj O))
  have hnat : IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) =
      v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
        (IM.map (R.hom.app (SY.obj O)))⟦s⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
      Rfull, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using
      (ShiftedHom.map_naturality v Rfull.hom).symm
  have hcoef₀ : IM.map (R.hom.app (SY.obj O)) ≫ IM.map E.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveSerreSpecUnitSectionsIso k).hom =
      IM.map (affineDerivedStructureTargetIso (.of k)).hom := by
    have h₀ := cmCurveSerreAffineDerived_coefficient k
    dsimp only at h₀
    rw [← hρ] at h₀
    have h := congrArg IM.map h₀
    have hm : IM.map (R.hom.app (SY.obj O) ≫ E.hom ≫
        SM.map (cmCurveSerreSpecUnitSectionsIso k).hom) =
        IM.map (R.hom.app (SY.obj O)) ≫ IM.map E.hom ≫
          IM.map (SM.map (cmCurveSerreSpecUnitSectionsIso k).hom) :=
      (IM.map_comp _ _).trans
        (congrArg (fun z => IM.map (R.hom.app (SY.obj O)) ≫ z) (IM.map_comp _ _))
    exact hm.symm.trans h
  let J := shiftFunctor (DerivedCategory (ModuleCat.{u} k)) s
  have hcoef : J.map (IM.map (R.hom.app (SY.obj O))) ≫
        J.map (IM.map E.hom) ≫
          J.map ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
            (cmCurveSerreSpecUnitSectionsIso k).hom) =
      J.map (IM.map (affineDerivedStructureTargetIso (.of k)).hom) :=
    (cmCurveMapTriple J _ _ _).symm.trans (J.congr_map hcoef₀)
  have hA' : moduleSpecDerivedPushforwardHomAddEquiv p F O n q a =
      IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map E.hom)⟦s⟧' ≫ cM.inv := by
    have hA := moduleSpecDerivedPushforwardHomAddEquiv_apply p F O n q a
    dsimp only at hA
    convert hA using 1
    simp only [Cmp, ρ, G, U, R, E, cY, cM, s, v, S, SY, D, IM, IY,
      relativeOpenCoefficientShiftIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc]
    rfl
  let P := cmCurveSerreDerivedSections k ι j F
  let T := ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
    (ModuleCat.of k k))⟦s⟧
  let a₀ : P ⟶ T := moduleSpecDerivedPushforwardHomAddEquiv p F O n q a ≫
    cM.hom ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
      (cmCurveSerreSpecUnitSectionsIso k).hom)⟦s⟧'
  let a₁ : P ⟶ T :=
    (IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) ≫
      v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map E.hom)⟦s⟧' ≫ cM.inv) ≫
        cM.hom ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
          (cmCurveSerreSpecUnitSectionsIso k).hom)⟦s⟧'
  let a₂ : P ⟶ T := IM.map (Cmp.hom.app (S.obj F)) ≫
    v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
      (IM.map (affineDerivedStructureTargetIso (.of k)).hom)⟦s⟧'
  have h₀ : a₀ = a₁ := congrArg (fun z => z ≫ cM.hom ≫
    ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
      (cmCurveSerreSpecUnitSectionsIso k).hom)⟦s⟧') hA'
  have h₁ : a₁ = a₂ := cmCurveAffineArrowTransport _ _ _ _ _ _ cM _ _ hnat hcoef
  have h₂ : a₂ = cmCurveSerreModuleHom k ι j F s (a ≫ cY.hom) :=
    (cmCurveSerreModuleHom_apply k ι j F s (a ≫ cY.hom)).symm
  exact h₀.trans (h₁.trans h₂)


/-- The same original affine Hom comparison uses any actual integer
reindex, proved from its original coefficient normalization. -/
theorem cmCurveSerreAffineHom_moduleHom_reindex (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q : ℕ) (s : ℤ)
    (hqn : (q : ℤ) - s = n)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(q : ℤ)⟧) :
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a ≫
        (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
          (cmCurveSerreSpecUnitSectionsIso k).hom)⟦s⟧' =
      cmCurveSerreModuleHom k ι j F s
        (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  have hs : s = (q : ℤ) - n := by omega
  subst s
  dsimp only
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
  let u := ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
    (cmCurveSerreSpecUnitSectionsIso k).hom)⟦(q : ℤ) - n⟧'
  have hM := congrArg (fun z => B ≫ z ≫ u)
    (cmCurveCoefficientShift_reindex N (n : ℤ) (q : ℤ)).symm
  have hY := congrArg
    (fun z => cmCurveSerreModuleHom k ι j F ((q : ℤ) - n) (a ≫ z))
    (cmCurveCoefficientShift_reindex O (n : ℤ) (q : ℤ))
  exact hM.trans ((cmCurveSerreAffineHom_moduleHom k ι j n e F hF q a).trans hY)

end AlgebraicGeometry.Scheme.Cohomology


namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveModelHomologyDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The actual inverse components transport an original unit homology square. -/
theorem cmCurveUnitHomologyInverse {A : Type*} [Category* A]
    {P N X Y : A} (e₀ : P ≅ N) (E : X ≅ Y) (u : P ⟶ X) (c : N ⟶ Y)
    (h : e₀.inv ≫ u ≫ E.hom = c) : e₀.inv ≫ u = c ≫ E.inv := by
  apply (cancel_mono E.hom).mp
  have hR : (c ≫ E.inv) ≫ E.hom = c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => c ≫ z) E.inv_hom_id).trans (Category.comp_id _))
  exact (Category.assoc _ _ _).trans (h.trans hR.symm)

/-- The native target single comparisons paste through their original
coefficient square, with their actual inverse components. -/
theorem cmCurveTargetSinglePasting {A : Type*} [Category* A]
    {U X Y Z W V : A} (B : U ⟶ X) (T : X ⟶ Y) (R : X ⟶ Z)
    (J : Z ≅ Y) (c : Z ⟶ W) (K : W ≅ V) (h : Y ⟶ V) (ψ : U ⟶ W)
    (hR : R = T ≫ J.inv) (hc : c ≫ K.hom = J.hom ≫ h)
    (hψ : B ≫ R ≫ c = ψ) : B ≫ T ≫ h = ψ ≫ K.hom := by
  symm
  calc
    _ = (B ≫ R ≫ c) ≫ K.hom := congrArg (fun z => z ≫ K.hom) hψ.symm
    _ = B ≫ (T ≫ J.inv) ≫ (J.hom ≫ h) := by
      rw [hR, Category.assoc, Category.assoc, hc]
    _ = B ≫ T ≫ h := by simp only [Category.assoc, J.inv_hom_id_assoc]

/-- The actual affine comparison, original homology extraction, and
original resolution-section comparison evaluate the module-valued native
shift map. This is a proved original-map identity, not an extra premise. -/
theorem cmCurveSerreAffineHom_homology_of_reindex (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q i : ℕ) (s : ℤ)
    (hqn : (q : ℤ) - s = n) (hsi : s + (i : ℤ) = 0)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(q : ℤ)⟧)
    (x : cmCurveSerreCohomology k ι j F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) (i : ℤ) (n : ℤ) (by omega)).app N
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    cmCurveSerreHomologyDualAddEquiv k ι j F i N
        (cmCurveSerreSpecUnitSectionsIso k)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).map (B ≫ T.hom) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k)
            (i : ℤ)).hom.app N) x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F s
          (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv))
        (i : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) (i : ℤ) (n : ℤ) (by omega)).app N
  let JN := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    s (i : ℤ) 0 (by omega)).app N
  let Jk := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    s (i : ℤ) 0 (by omega)).app (ModuleCat.of k k)
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let eN := cmCurveSerreSpecUnitSectionsIso k
  let ψ := cmCurveSerreModuleHom k ι j F s
    (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)
  have hbridge := cmCurveSerreAffineHom_moduleHom_reindex k ι j n e F hF q s hqn a
  have hshift : (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv = T.hom ≫ JN.inv :=
    cmCurveReindexCoefficient N (n : ℤ) (q : ℤ) s (i : ℤ) hqn hsi
  have hnat : ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map eN.hom)⟦s⟧' ≫
      Jk.hom = JN.hom ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom :=
    (((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso s (i : ℤ) 0
      (by omega)).hom.naturality eN.hom)
  have hArrow : B ≫ T.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom =
      ψ ≫ Jk.hom :=
    cmCurveTargetSinglePasting B T.hom
      (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv JN
      (((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map eN.hom)⟦s⟧')
      Jk ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ψ
      hshift hnat hbridge
  let eI := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
    ℤ)).hom.app N
  let eK := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
    ℤ)).hom.app
    (ModuleCat.of k k)
  have hcoef : H.map ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ≫ eK =
      eI ≫ eN.hom := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
        ℤ)).hom.naturality eN.hom
  have hform : H.map (B ≫ T.hom) ≫ eI ≫ eN.hom =
      H.map ((B ≫ T.hom) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ≫ eK := by
    exact (congrArg (fun z => H.map (B ≫ T.hom) ≫ z) hcoef.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ eK)
          (H.map_comp (B ≫ T.hom)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom)).symm))
  have hnormalize : H.map (B ≫ T.hom) ≫ eI ≫ eN.hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap ψ (i : ℤ) 0 (by omega) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
          (ModuleCat.of k k) :=
    hform.trans ((congrArg (fun z => H.map z ≫ eK)
      ((Category.assoc _ _ _).trans hArrow)).trans
      (DerivedCategory.cmCurveHomToShiftSingle_homology (ModuleCat.of k k) s (i : ℤ) (by omega)
        ψ))
  change (H.map (B ≫ T.hom) ≫ eI ≫ eN.hom) (E.symm x) = _
  exact congrArg (fun f => f (E.symm x)) hnormalize


/-- The actual affine comparison, original homology extraction, and
original resolution-section comparison evaluate the module-valued native
shift map. This is a proved original-map identity, not an extra premise. -/
theorem cmCurveSerreAffineHom_homology (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q i : ℕ) (hi : (q : ℤ) + i = n)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(q : ℤ)⟧)
    (x : cmCurveSerreCohomology k ι j F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) (i : ℤ) (n : ℤ) hi).app N
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    cmCurveSerreHomologyDualAddEquiv k ι j F i N
        (cmCurveSerreSpecUnitSectionsIso k)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).map (B ≫ T.hom) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k)
            (i : ℤ)).hom.app N) x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F ((q : ℤ) - n)
          (a ≫ (relativeOpenCoefficientShiftIso O (n : ℤ) (q : ℤ)).hom))
        (i : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  dsimp only
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let s : ℤ := (q : ℤ) - n
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)
  have h := cmCurveSerreAffineHom_homology_of_reindex k ι j n e F hF q i s
    (by dsimp [s]; omega) (by dsimp [s]; omega) a x
  have hmap := congrArg (fun z => cmCurveSerreModuleHom k ι j F s (a ≫ z))
    (cmCurveCoefficientShift_reindex O (n : ℤ) (q : ℤ)).symm
  exact h.trans (congrArg
    (fun φ => (H.shiftMap φ (i : ℤ) 0 (by dsimp [s]; omega) ≫ e₀) (E.symm x)) hmap)

end AlgebraicGeometry.Scheme.Cohomology
