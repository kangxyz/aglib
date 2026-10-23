/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.System.Data
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.QuotientComparison

/-! # Native coherent adic systems from actual compatible line bundles -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
  (S : CompatibleLineBundleSystem f I)

section CoefficientReduction

variable (K : X.IdealSheafData) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (hK : K = i.ker) (M : X.Modules) (N : Z.Modules)
  (e : (pullback i).obj M ≅ N)

/-- The original quotient comparison followed by the actual coefficient map. -/
def coefficientReductionMap :
    (idealSheafQuotientFunctor X K).obj M ⟶ (pushforward i).obj N :=
  (closedImmersionQuotientIso K.subschemeι i (by
    simpa only [IdealSheafData.ker_subschemeι] using hK) M).hom ≫
    (pushforward i).map e.hom

instance coefficientReductionMap_isIso :
    IsIso (coefficientReductionMap K i hK M N e) := by
  dsimp only [coefficientReductionMap]
  infer_instance

/-- The variable coefficient boundary keeps the concrete thickening maps folded. -/
def coefficientReductionIso :
    (idealSheafQuotientFunctor X K).obj M ≅ (pushforward i).obj N :=
  asIso (coefficientReductionMap K i hK M N e)

@[reassoc]
theorem unit_coefficientReductionIso_hom :
    (idealSheafQuotientUnit X K).app M ≫
      (coefficientReductionIso K i hK M N e).hom =
        adjointCoefficientMap i M N e.hom := by
  change (idealSheafQuotientUnit X K).app M ≫
    ((closedImmersionQuotientIso K.subschemeι i
      (by simpa only [IdealSheafData.ker_subschemeι] using hK) M).hom ≫
        (pushforward i).map e.hom) = _
  rw [adjointCoefficientMap_eq_unit]
  exact closedImmersionUnit_quotientIso_hom_assoc K.subschemeι i
    (by simpa only [IdealSheafData.ker_subschemeι] using hK) M
    ((pushforward i).map e.hom)

end CoefficientReduction

/-- Actual positive terms are finite-type quasicoherent, by finite presentation
of line bundles and finite direct image along the original closed immersion. -/
theorem positiveTerm_coherent (n : ℕ) : affineLocallyFiniteType X (S.positiveTerm n) := by
  let := lineBundle_isFinitePresentation _ (S.bundle n)
  exact FiniteMorphism.affineLocallyFiniteType_pushforward
    (idealThickeningι f (I ^ (n + 1)))
    (affineLocallyFiniteType_of_finitePresentation (S.bundle n).val)

/-- An original pushed line bundle is annihilated by the matching native ideal power. -/
theorem positiveTerm_killed (n : ℕ) :
    killedByIdealSheaf (idealThickeningIdealSheaf f I ^ (n + 1)) (S.positiveTerm n) := by
  simpa only [idealThickeningι_ker, idealThickeningIdealSheaf_pow] using
    killedByIdealSheaf_pushforward_ker (idealThickeningι f (I ^ (n + 1)))
      (S.bundle n).val

/-- The native ideal-power quotient is canonically the original geometric
thickening quotient, with precisely the same original unit. -/
def nativeQuotientIso (n : ℕ) (M : X.Modules) :
    (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj M ≅
      (pushforward (idealThickeningι f (I ^ n))).obj
        ((pullback (idealThickeningι f (I ^ n))).obj M) :=
  closedImmersionQuotientIso (idealThickeningIdealSheaf f I ^ n).subschemeι
    (idealThickeningι f (I ^ n)) (by
      simp only [IdealSheafData.ker_subschemeι, idealThickeningι_ker,
        idealThickeningIdealSheaf_pow]) M

@[reassoc (attr := simp)]
theorem unit_nativeQuotientIso_hom (n : ℕ) (M : X.Modules) :
    (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M ≫
      (nativeQuotientIso (f := f) (I := I) n M).hom =
        (pullbackPushforwardAdjunction (idealThickeningι f (I ^ n))).unit.app M :=
  closedImmersionUnit_quotientIso_hom _ _ _ M

/-- The actual positive successor compatibility supplies the native reduction iso. -/
def positiveReductionIso (n : ℕ) :
    (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ (n + 1))).obj
      (S.positiveTerm (n + 1)) ≅ S.positiveTerm n :=
  coefficientReductionIso (idealThickeningIdealSheaf f I ^ (n + 1))
    (idealThickeningι f (I ^ (n + 1)))
    (by rw [idealThickeningι_ker, idealThickeningIdealSheaf_pow])
    (S.positiveTerm (n + 1)) (S.bundle n).val (S.successorCoefficientIso n)

@[reassoc (attr := simp)]
theorem unit_positiveReductionIso_hom (n : ℕ) :
    (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ (n + 1))).app
        (S.positiveTerm (n + 1)) ≫ (S.positiveReductionIso n).hom =
      S.positiveTransition n := by
  exact unit_coefficientReductionIso_hom _ _ _ _ _ _

variable [IsLocallyNoetherian X]

/-- Every native term is coherent, including the actual zero term. -/
theorem term_coherent : ∀ n : ℕ, affineLocallyFiniteType X (S.term n)
  | 0 => (affineLocallyFiniteType X).prop_zero
  | n + 1 => S.positiveTerm_coherent n

/-- The degree-zero quotient is the actual zero module sheaf. -/
def zeroReductionIso :
    (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ 0)).obj
      (S.positiveTerm 0) ≅ (0 : X.Modules) :=
  (((completionFunctor X (idealThickeningIdealSheaf f I)).obj
    ⟨S.positiveTerm 0, S.positiveTerm_coherent 0⟩).zero_isZero).isoZero

/-- Every native term is annihilated by its matching ideal power. -/
theorem term_killed : ∀ n : ℕ,
    killedByIdealSheaf (idealThickeningIdealSheaf f I ^ n) (S.term n)
  | 0 => killedByIdealSheaf_of_iso _ S.zeroReductionIso
      (idealSheafQuotient_killed X _ (S.positiveTerm 0))
  | n + 1 => S.positiveTerm_killed n

/-- Actual geometric successor isomorphisms imply all native adic conditions. -/
theorem diagram_isAdicSystem :
    IsAdicSystem X (idealThickeningIdealSheaf f I) S.diagram where
  coherent n := S.term_coherent n
  annihilated n := S.term_killed n
  reduction n := by
    cases n with
    | zero =>
        refine ⟨S.zeroReductionIso, ?_⟩
        exact (isZero_zero X.Modules).eq_of_tgt _ _
    | succ n =>
        refine ⟨S.positiveReductionIso n, ?_⟩
        rw [S.diagram_map_succ]
        exact S.unit_positiveReductionIso_hom n

/-- The original native coherent formal system produced from compatible
actual line bundles. No completeness, properness or effectivity is required. -/
def toAdicSystem : AdicSystem X (idealThickeningIdealSheaf f I) :=
  ⟨S.diagram, S.diagram_isAdicSystem⟩

@[simp]
theorem toAdicSystem_obj_zero : S.toAdicSystem.obj.obj (op 0) = 0 := rfl

@[simp]
theorem toAdicSystem_obj_succ (n : ℕ) :
    S.toAdicSystem.obj.obj (op (n + 1)) = S.positiveTerm n := rfl

/-- The native system retains the original positive geometric transition. -/
@[simp]
theorem toAdicSystem_transition_succ (n : ℕ) :
    S.toAdicSystem.transition (n + 1) = S.positiveTransition n :=
  S.diagram_map_succ (n + 1)

end AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem
