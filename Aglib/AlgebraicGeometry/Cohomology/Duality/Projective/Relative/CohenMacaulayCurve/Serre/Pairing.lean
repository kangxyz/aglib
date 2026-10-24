/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Derived

/-!
# The original positive curve Yoneda pairing
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Native Yoneda transport between two specified original linear
Ext/cohomology comparisons, checked before concrete specialization. -/
def cmCurveYonedaActionOfEquivs
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O F G : A} {a i l : ℕ}
    {H₁ H₂ : Type*} [AddCommGroup H₁] [AddCommGroup H₂] [Module k H₁] [Module k H₂]
    (E₁ : Ext.{w} O F i ≃ₗ[k] H₁) (E₂ : Ext.{w} O G l ≃ₗ[k] H₂)
    (η : Ext.{w} F G a) (h : i + a = l) : H₁ →ₗ[k] H₂ :=
  E₂.toLinearMap.comp ((η.postcompOfLinear k O h).comp E₁.symm.toLinearMap)

/-- The abstract transport retains the original class and native Yoneda product. -/
theorem cmCurveYonedaActionOfEquivs_apply
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O F G : A} {a i l : ℕ}
    {H₁ H₂ : Type*} [AddCommGroup H₁] [AddCommGroup H₂] [Module k H₁] [Module k H₂]
    (E₁ : Ext.{w} O F i ≃ₗ[k] H₁) (E₂ : Ext.{w} O G l ≃ₗ[k] H₂)
    (η : Ext.{w} F G a) (h : i + a = l) (x : H₁) :
    cmCurveYonedaActionOfEquivs E₁ E₂ η h x = E₂ ((E₁.symm x).comp η h) := rfl

/-- The original Ext/trace pairing is linear on abstract native carriers. -/
def cmCurveYonedaPairingOfEquiv
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O F W : A} {i r m : ℕ}
    {H : Type*} [AddCommGroup H] [Module k H]
    (E : Ext.{w} O F i ≃ₗ[k] H) (t : Ext.{w} O W m →ₗ[k] k)
    (h : i + r = m) : Ext.{w} F W r →ₗ[k] Module.Dual k H where
  toFun β := t.comp ((β.postcompOfLinear k O h).comp E.symm.toLinearMap)
  map_add' β γ := by
    ext x
    exact (congrArg t (Ext.comp_add (E.symm x) β γ h)).trans (t.map_add _ _)
  map_smul' a β := by
    ext x
    exact (congrArg t (Ext.comp_smul (E.symm x) β h a)).trans (t.map_smul a _)

/-- The abstract linear constructor retains the original positive Yoneda value. -/
theorem cmCurveYonedaPairingOfEquiv_apply
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O F W : A} {i r m : ℕ}
    {H : Type*} [AddCommGroup H] [Module k H]
    (E : Ext.{w} O F i ≃ₗ[k] H) (t : Ext.{w} O W m →ₗ[k] k)
    (h : i + r = m) (β : Ext.{w} F W r) (x : H) :
    cmCurveYonedaPairingOfEquiv E t h β x = t ((E.symm x).comp β h) := rfl

/-- Native associativity proves the original pairing naturality before
specializing the Ext/cohomology carriers. -/
theorem cmCurveYonedaPairingOfEquiv_comp
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O F G W : A}
    {i a b l r m : ℕ} {HF HG : Type*}
    [AddCommGroup HF] [AddCommGroup HG] [Module k HF] [Module k HG]
    (EF : Ext.{w} O F i ≃ₗ[k] HF) (EG : Ext.{w} O G l ≃ₗ[k] HG)
    (t : Ext.{w} O W m →ₗ[k] k) (η : Ext.{w} F G a) (β : Ext.{w} G W b)
    (hab : a + b = r) (hil : i + a = l) (hir : i + r = m) (hlb : l + b = m)
    (x : HF) :
    cmCurveYonedaPairingOfEquiv EF t hir (η.comp β hab) x =
      cmCurveYonedaPairingOfEquiv EG t hlb β
        (cmCurveYonedaActionOfEquivs EF EG η hil x) := by
  change t ((EF.symm x).comp (η.comp β hab) hir) =
    t ((EG.symm (EG ((EF.symm x).comp η hil))).comp β hlb)
  rw [EG.symm_apply_apply]
  exact congrArg t (Ext.comp_assoc (EF.symm x) η β hil hab (by omega)).symm

/-- The original identity class acts as the unit of the positive pairing. -/
theorem cmCurveYonedaPairingOfEquiv_unit
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {k : Type*} [CommRing k] [Linear k A] {O W : A} {r : ℕ}
    {H : Type*} [AddCommGroup H] [Module k H]
    (E : Ext.{w} O O 0 ≃ₗ[k] H) (t : Ext.{w} O W r →ₗ[k] k)
    (β : Ext.{w} O W r) :
    cmCurveYonedaPairingOfEquiv E t (Nat.zero_add r) β (E (Ext.mk₀ (𝟙 O))) = t β := by
  change t ((E.symm (E (Ext.mk₀ (𝟙 O)))).comp β (Nat.zero_add r)) = t β
  rw [E.symm_apply_apply, Ext.mk₀_id_comp]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveClosureModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

/-- The genuine positive Yoneda action on the original cohomology, with
the original Ext/cohomology normalization on both ends. -/
def cmCurveSerreYonedaAction {F G : C.Modules} {a : ℕ}
    (η : Ext.{u + 1} (C := C.Modules) F G a) (i l : ℕ) (hil : i + a = l) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    cmCurveSerreCohomology k ι j F i →ₗ[k] cmCurveSerreCohomology k ι j G l := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) G l
  let O : C.Modules := cmCurveSerreUnit C
  let E₁ : Ext.{u + 1} (C := C.Modules) O F i ≃ₗ[k]
      cmCurveSerreCohomology k ι j F i :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F i
  let E₂ : Ext.{u + 1} (C := C.Modules) O G l ≃ₗ[k]
      cmCurveSerreCohomology k ι j G l :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) G l
  exact cmCurveYonedaActionOfEquivs E₁ E₂ η hil

omit [IsClosedImmersion j] in
/-- The native cohomology action retains its original Ext class value. -/
theorem cmCurveSerreYonedaAction_apply {F G : C.Modules} {a : ℕ}
    (η : Ext.{u + 1} (C := C.Modules) F G a) (i l : ℕ) (hil : i + a = l)
    (x : cmCurveSerreCohomology k ι j F i) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) G l
    let O : C.Modules := cmCurveSerreUnit C
    let E₁ : Ext.{u + 1} (C := C.Modules) O F i ≃ₗ[k]
        cmCurveSerreCohomology k ι j F i :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F i
    let E₂ : Ext.{u + 1} (C := C.Modules) O G l ≃ₗ[k]
        cmCurveSerreCohomology k ι j G l :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) G l
    cmCurveSerreYonedaAction k ι j η i l hil x = E₂ ((E₁.symm x).comp η hil) := rfl

omit [IsClosedImmersion j] in
/-- Degree-zero positive Yoneda action is the original cohomology coefficient map. -/
theorem cmCurveSerreYonedaAction_mk₀ {F G : C.Modules} (f : F ⟶ G) (i : ℕ)
    (x : cmCurveSerreCohomology k ι j F i) :
    cmCurveSerreYonedaAction k ι j (Ext.mk₀ f) i i (Nat.add_zero i) x =
      (moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) i).map f x := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) G i
  let O : C.Modules := cmCurveSerreUnit C
  let E : Ext.{u + 1} (C := C.Modules) O F i ≃ₗ[k]
      cmCurveSerreCohomology k ι j F i :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F i
  have h := cmCurveSerreYonedaAction_apply k ι j (Ext.mk₀ f) i i (Nat.add_zero i) x
  have hn := moduleExtCohomologyMap_naturality C f i (E.symm x)
  have hG := moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
    G i ((E.symm x).comp (Ext.mk₀ f) (Nat.add_zero i))
  have hF : moduleExtCohomologyMap C F i (E.symm x) = x :=
    (moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
      F i (E.symm x)).symm.trans (E.apply_symm_apply x)
  exact h.trans (hG.trans (hn.trans
    (congrArg ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) i).map f) hF)))

variable (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- The positive Yoneda/trace pairing, using the same existing geometric
trace and the original Ext/cohomology maps. No perfect-pairing premise occurs. -/
def cmCurveSerreYonedaPairing (F : C.Modules) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r →ₗ[k]
      Module.Dual k (cmCurveSerreCohomology k ι j F (1 - r)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let Eω : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let t : Ext.{u + 1} (C := C.Modules) O W 1 →ₗ[k] k :=
    (cmCurveSerreTrace k ι j n e hCM hn).comp Eω.toLinearMap
  exact cmCurveYonedaPairingOfEquiv E t (show (1 - r) + r = 1 by omega)

/-- The same staged pairing evaluates by the original Ext/cohomology
maps and the already installed trace. -/
theorem cmCurveSerreYonedaPairing_apply (F : C.Modules) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let O : C.Modules := cmCurveSerreUnit C
    let E : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
        cmCurveSerreCohomology k ι j F (1 - r) :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
    cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn β x =
      cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1
          ((E.symm x).comp β (by omega))) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let Eω : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let t : Ext.{u + 1} (C := C.Modules) O W 1 →ₗ[k] k :=
    (cmCurveSerreTrace k ι j n e hCM hn).comp Eω.toLinearMap
  exact (cmCurveYonedaPairingOfEquiv_apply E t (by omega) β x).trans
    (congrArg (cmCurveSerreTrace k ι j n e hCM hn)
      (moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
        W 1 ((E.symm x).comp β (by omega))))

/-- All complementary degrees use original Yoneda associativity. In
particular, the degree-one action has the native positive boundary sign. -/
theorem cmCurveSerreYonedaPairing_comp {F G : C.Modules} {a b r : ℕ}
    (η : Ext.{u + 1} (C := C.Modules) F G a)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCanonicalModule k ι j n) b)
    (hab : a + b = r) (hr : r ≤ 1) (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn (η.comp β hab) x =
      cmCurveSerreYonedaPairing k ι j n e hCM G b (by omega) hn β
        (cmCurveSerreYonedaAction k ι j η (1 - r) (1 - b) (by omega) x) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) G (1 - b)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let EF : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let EG : Ext.{u + 1} (C := C.Modules) O G (1 - b) ≃ₗ[k]
      cmCurveSerreCohomology k ι j G (1 - b) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) G (1 - b)
  let Eω : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let t : Ext.{u + 1} (C := C.Modules) O W 1 →ₗ[k] k :=
    (cmCurveSerreTrace k ι j n e hCM hn).comp Eω.toLinearMap
  exact cmCurveYonedaPairingOfEquiv_comp EF EG t η β hab (by omega) (by omega) (by omega) x

/-- Ordinary source naturality is the degree-zero specialization, on the
original sheaf-cohomology coefficient map. -/
theorem cmCurveSerreYonedaPairing_precomp {F G : C.Modules}
    (f : F ⟶ G) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCanonicalModule k ι j n) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn
        ((Ext.mk₀ f).comp β (Nat.zero_add r)) x =
      cmCurveSerreYonedaPairing k ι j n e hCM G r hr hn β
        ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) (1 - r)).map f x) := by
  exact (cmCurveSerreYonedaPairing_comp k ι j n e hCM
    (Ext.mk₀ f) β (Nat.zero_add r) hr hn x).trans
      (congrArg (cmCurveSerreYonedaPairing k ι j n e hCM G r hr hn β)
        (cmCurveSerreYonedaAction_mk₀ k ι j f (1 - r) x))

/-- The actual structural section one, expressed through the original
unit-source Ext/cohomology map. -/
def cmCurveSerreStructuralOne :
    cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0 :=
  moduleExtCohomologyMap C (cmCurveSerreUnit C) 0 (Ext.mk₀ (𝟙 _))

omit [IsClosedImmersion j] in
/-- Its original global section is literally `1`; no orientation is chosen. -/
theorem cmCurveSerreStructuralOne_sections :
    Sheaf.H.equiv₀ (moduleAddSheaf C (cmCurveSerreUnit C)) isTerminalTop
      (cmCurveSerreStructuralOne k ι j) = (1 : Γ(C, ⊤)) := by
  exact moduleExtCohomologyMap_mk₀_sections C (cmCurveSerreUnit C) (𝟙 _)

/-- The genuine structural map on `H⁰(O_C)`, linearly generated by the
actual structural section one. Its section formula identifies the original ring map. -/
def cmCurveSerreStructuralH0Map : k →ₗ[k]
    cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0 :=
  (LinearMap.id : k →ₗ[k] k).smulRight (cmCurveSerreStructuralOne k ι j)

omit [IsClosedImmersion j] in
/-- Under the original degree-zero section equivalence this is the literal
structural ring map on every scalar, not merely an isomorphism of lines. -/
theorem cmCurveSerreStructuralH0Map_sections (a : k) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveSerreUnit C) 0
    let : Module k Γ(C, ⊤) := Module.compHom _ (cmCurveSerreScalar k ι j)
    moduleH0EquivOfHom C (cmCurveSerreScalar k ι j) (cmCurveSerreUnit C)
      (cmCurveSerreStructuralH0Map k ι j a) = cmCurveSerreScalar k ι j a := by
  let O : C.Modules := cmCurveSerreUnit C
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) O 0
  let : Module k Γ(C, ⊤) := Module.compHom _ (cmCurveSerreScalar k ι j)
  let E := moduleH0EquivOfHom C (cmCurveSerreScalar k ι j) O
  have hE : E (cmCurveSerreStructuralOne k ι j) = (1 : Γ(C, ⊤)) :=
    cmCurveSerreStructuralOne_sections k ι j
  change E (a • cmCurveSerreStructuralOne k ι j) = cmCurveSerreScalar k ι j a
  exact (E.map_smul a _).trans
    ((congrArg (fun z : Γ(C, ⊤) => a • z) hE).trans
      (show (cmCurveSerreScalar k ι j a) * 1 = cmCurveSerreScalar k ι j a from mul_one _))

/-- An honest isomorphism of the original structural map makes evaluation
at its original section one a linear equivalence of duals. -/
def cmCurveSerreStructuralEvaluationEquiv
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    Module.Dual k
      (cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (cmCurveSerreStructuralH0Map k ι j) hc).dualMap.trans
    (LinearMap.ringLmapEquivSelf k k k)

omit [IsClosedImmersion j] in
/-- This equivalence is evaluation on the original structural one. -/
theorem cmCurveSerreStructuralEvaluationEquiv_apply
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (l : Module.Dual k
      (cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0)) :
    cmCurveSerreStructuralEvaluationEquiv k ι j hc l = l (cmCurveSerreStructuralOne k ι j) := by
  change l ((cmCurveSerreStructuralH0Map k ι j) 1) = _
  exact congrArg l (one_smul k (cmCurveSerreStructuralOne k ι j))

/-- At the structural section one, positive Yoneda composition reduces
to the same trace applied to the original degree-one cohomology class. -/
theorem cmCurveSerreYonedaPairing_one (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j (cmCurveCanonicalModule k ι j n) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let O : C.Modules := cmCurveSerreUnit C
    let W : C.Modules := cmCurveCanonicalModule k ι j n
    let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
        cmCurveSerreCohomology k ι j W 1 :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
    cmCurveSerreYonedaPairing k ι j n e hCM (cmCurveSerreUnit C) 1
        (by omega) hn (E.symm x) (cmCurveSerreStructuralOne k ι j) =
      cmCurveSerreTrace k ι j n e hCM hn x := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) O 0
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E₀ : Ext.{u + 1} (C := C.Modules) O O 0 ≃ₗ[k]
      cmCurveSerreCohomology k ι j O 0 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) O 0
  let E₁ : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let t : Ext.{u + 1} (C := C.Modules) O W 1 →ₗ[k] k :=
    (cmCurveSerreTrace k ι j n e hCM hn).comp E₁.toLinearMap
  have hOne : cmCurveSerreStructuralOne k ι j = E₀ (Ext.mk₀ (𝟙 O)) :=
    (moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
      O 0 (Ext.mk₀ (𝟙 O))).symm
  exact (congrArg
    (cmCurveSerreYonedaPairing k ι j n e hCM O 1 (by omega) hn (E₁.symm x)) hOne).trans
    ((cmCurveYonedaPairingOfEquiv_unit E₀ t (E₁.symm x)).trans
      (congrArg (cmCurveSerreTrace k ι j n e hCM hn) (E₁.apply_symm_apply x)))

end AlgebraicGeometry.Scheme.Cohomology
