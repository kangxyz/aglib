/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient

/-!
# Unit-coefficient Cohen--Macaulay curve Serre duality

The public endpoint preserves the original additive forward map, original
positive Yoneda action, and the same installed trace. Its native intermediate
providers live under `Serre/`.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveEndpointModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- A proved equality with a linear map equips the same additive
bijection with linearity while retaining its original forward map. -/
def cmCurveLinearEquivOfOriginalPairing {k : Type*} [CommRing k]
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    (E : X ≃+ Y) (P : X →ₗ[k] Y) (h : ∀ x, E x = P x) : X ≃ₗ[k] Y where
  toAddEquiv := E
  map_smul' a x := (h (a • x)).trans
    ((P.map_smul a x).trans (congrArg (fun y => a • y) (h x).symm))

/-- Unit-coefficient Serre duality for a coherent module on the actual
chosen-embedding Cohen--Macaulay curve. The forward map is exactly the
original additive comparison, now proved linear by its same positive
Yoneda/trace pairing. -/
def cmCurveSerreDuality (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r ≃ₗ[k]
      Module.Dual k (cmCurveSerreCohomology k ι j F (1 - r)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  exact cmCurveLinearEquivOfOriginalPairing
    (cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn)
    (cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn)
    (cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing k ι j n e hCM F hF r hr hn)

/-- Linear packaging leaves the original comparison forward map unchanged. -/
theorem cmCurveSerreDuality_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r) :
    cmCurveSerreDuality k ι j n e hCM F hF r hr hn β =
      cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β := rfl

/-- The original linear comparison retains full source/Yoneda naturality
in complementary curve degrees, with the original unsigned Ext product. -/
theorem cmCurveSerreDuality_comp {F G : C.Modules}
    (hF : affineLocallyFiniteType C F) (hG : affineLocallyFiniteType C G)
    {a b r : ℕ} (η : Ext.{u + 1} (C := C.Modules) F G a)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCanonicalModule k ι j n) b)
    (hab : a + b = r) (hr : r ≤ 1) (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveSerreDuality k ι j n e hCM F hF r hr hn (η.comp β hab) x =
      cmCurveSerreDuality k ι j n e hCM G hG b (by omega) hn β
        (cmCurveSerreYonedaAction k ι j η (1 - r) (1 - b) (by omega) x) := by
  rw [cmCurveSerreDuality_apply, cmCurveSerreDuality_apply,
    cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing,
    cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing]
  exact cmCurveSerreYonedaPairing_comp k ι j n e hCM η β hab hr hn x

/-- Ordinary source naturality uses the original sheaf-cohomology map. -/
theorem cmCurveSerreDuality_precomp {F G : C.Modules}
    (hF : affineLocallyFiniteType C F) (hG : affineLocallyFiniteType C G)
    (f : F ⟶ G) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCanonicalModule k ι j n) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveSerreDuality k ι j n e hCM F hF r hr hn
        ((Ext.mk₀ f).comp β (Nat.zero_add r)) x =
      cmCurveSerreDuality k ι j n e hCM G hG r hr hn β
        ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) (1 - r)).map f x) := by
  rw [cmCurveSerreDuality_apply, cmCurveSerreDuality_apply,
    cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing,
    cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing]
  exact cmCurveSerreYonedaPairing_precomp k ι j n e hCM f r hr hn β x

/-- The same degree-one Serre functional, evaluated at the original
structural one, is the already installed original trace. -/
theorem cmCurveSerreDuality_one (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j (cmCurveCanonicalModule k ι j n) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let O : C.Modules := cmCurveSerreUnit C
    let W : C.Modules := cmCurveCanonicalModule k ι j n
    let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
        cmCurveSerreCohomology k ι j W 1 :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
    cmCurveSerreDuality k ι j n e hCM (cmCurveSerreUnit C)
        (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C)
        1 (by omega) hn (E.symm x) (cmCurveSerreStructuralOne k ι j) =
      cmCurveSerreTrace k ι j n e hCM hn x := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) O 0
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  have h₀ := cmCurveSerreDuality_apply k ι j n e hCM O
    (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C)
    1 (by omega) hn (E.symm x)
  have h₁ := cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing k ι j n e hCM O
    (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C)
    1 (by omega) hn (E.symm x)
  have hpoint := congrArg (fun l => l (cmCurveSerreStructuralOne k ι j)) (h₀.trans h₁)
  exact hpoint.trans (cmCurveSerreYonedaPairing_one k ι j n e hCM hn x)

/-- Bijectivity of the genuine structural `k → H⁰(O_C)` map makes the
same existing trace bijective. No orientation of another coefficient
line and no perfect-pairing premise are introduced. -/
theorem cmCurveSerreTrace_bijective (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    Function.Bijective (cmCurveSerreTrace k ι j n e hCM hn) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let P := cmCurveSerreDuality k ι j n e hCM O
    (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C) 1 (by omega) hn
  let T := E.symm.trans (P.trans (cmCurveSerreStructuralEvaluationEquiv k ι j hc))
  have hT : (T : Sheaf.H.{u + 1} (moduleAddSheaf C W) 1 → k) =
      cmCurveSerreTrace k ι j n e hCM hn := by
    funext x
    change cmCurveSerreStructuralEvaluationEquiv k ι j hc (P (E.symm x)) = _
    rw [cmCurveSerreStructuralEvaluationEquiv_apply]
    exact cmCurveSerreDuality_one k ι j n e hCM hn x
  rw [← hT]
  exact T.bijective

/-- The original trace as a linear equivalence under the honest
structural `H⁰` isomorphism. Its forward map remains the installed trace. -/
def cmCurveSerreTraceEquiv (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    Sheaf.H.{u + 1} (moduleAddSheaf C (cmCurveCanonicalModule k ι j n)) 1 ≃ₗ[k] k := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  exact LinearEquiv.ofBijective (cmCurveSerreTrace k ι j n e hCM hn)
    (cmCurveSerreTrace_bijective k ι j n e hCM hn hc)

/-- Packaging the proved trace bijection does not change its forward map. -/
theorem cmCurveSerreTraceEquiv_apply (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (x : cmCurveSerreCohomology k ι j (cmCurveCanonicalModule k ι j n) 1) :
    cmCurveSerreTraceEquiv k ι j n e hCM hn hc x =
      cmCurveSerreTrace k ι j n e hCM hn x := rfl

end AlgebraicGeometry.Scheme.Cohomology
