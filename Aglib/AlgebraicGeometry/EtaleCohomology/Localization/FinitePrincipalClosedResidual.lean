/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleInjectiveRefinementDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientOpenZeroTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalClosedSupport

/-! # The actual smaller-rank residual class after finite coefficient replacement

Starting with the original H1 class and its produced composite open-zero,
choose a genuine injective on the finite coefficient model, transform the
class by the actual adjunct, and construct the closed-branch injective and
its literal residual class. The quotient rank drops. Vanishing of this
specific smaller-rank class detects the unchanged original class through the
actual two-branch detector and finite coefficient retract.

This constructs the induction obligation and its return map, not its solution:
no smaller-rank vanishing or target-refinement conclusion is assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
open scoped nonZeroDivisors
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u eY eY' eV eW dY' dV dA
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- The actual finite coefficient image class, retaining the original
pullback and coefficient arrow. No finite comparison dictionary is replaced. -/
def moduleFiniteImageClass
    {T T' Y Y' : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
    (f : T' ⟶ T) (f' : Y' ⟶ Y) (b : Y ⟶ T) (b' : Y' ⟶ T')
    (h : f' ≫ b = b' ≫ f) (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf T Λ) (J : ModuleSheaf T' Λ)
    (a : (moduleInverseImage f Λ).obj I ⟶ J) (q : ℕ)
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q) :
    Sheaf.H.{eY'} ((inverseImage b').obj
      ((SheafOfModules.toSheaf (constantRing T' Λ)).obj J)) q :=
  Sheaf.H.map (moduleClosedPullbackCoefficientMap f f' b b' h Λ I J a) q
    (cohomologyPullback f' _ q c)

/-- Produce the actual lower-rank closed class and its original-class detector.
The only vanishing input is the already produced original composite open-zero. -/
theorem exists_finite_principalClosed_residual
    (R L : Type u) [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] [Module.Finite R L] [Surjective (Spec.algebraMap R L)]
    (s : L) (hs : s ≠ 0) (d : ℕ) (hd : ringKrullDim R ≤ (d + 1 : ℕ))
    {Y Y' V W : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
    [HasDerivedCategory.{dY'} (AbelianSheaf.{u, u + 1} Y')]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (f' : Y' ⟶ Y) (b : Y ⟶ Spec (.of R)) (b' : Y' ⟶ Spec (.of L))
    (h : IsPullback b' f' (Spec.algebraMap R L) b) [Smooth b']
    (j' : V ⟶ Y') (bU : V ⟶ (principalSupportOpen L s).toScheme)
    (hj : IsPullback bU j' (principalSupportOpen L s).ι b')
    (i' : W ⟶ Y') (bZ : W ⟶ Spec (.of (L ⧸ Ideal.span {s})))
    (hi : IsPullback bZ i' (principalSupportClosedMap L s) b')
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf (Spec (.of R)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of R))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (hopen : cohomologyPullback.{u, eY, eV} (j' ≫ f') _ 1 c = 0) :
    ∃ J : ModuleSheaf (Spec (.of L)) (ULift.{u + 1} (ZMod n)), Injective J ∧
      ∃ a : (moduleInverseImage (Spec.algebraMap R L) (ULift.{u + 1} (ZMod n))).obj I ⟶ J,
      ∃ K : ModuleSheaf (Spec (.of (L ⧸ Ideal.span {s})))
          (ULift.{u + 1} (ZMod n)), Injective K ∧
      ∃ aZ : (moduleInverseImage (principalSupportClosedMap L s)
          (ULift.{u + 1} (ZMod n))).obj J ⟶ K, Mono aZ ∧
      let cL := moduleFiniteImageClass (Spec.algebraMap R L) f' b b' h.w.symm
        (ULift.{u + 1} (ZMod n)) I J a 1 c
      let cZ := Sheaf.H.map
        (moduleClosedPullbackCoefficientMap (principalSupportClosedMap L s)
          i' b' bZ hi.w.symm (ULift.{u + 1} (ZMod n)) J K aZ) 1
        (cohomologyPullback i' _ 1 cL)
      ringKrullDim (L ⧸ Ideal.span {s}) ≤ (d : ℕ) ∧ (cZ = 0 → c = 0) := by
  let : IsFinite (Spec.algebraMap R L) :=
    (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite R L))
  obtain ⟨J, hJ, a, hfinite⟩ :=
    Finite.exists_moduleInjective_finite_refinement_detector.{u, eY, eY'}
      (Spec.algebraMap R L) (ULift.{u + 1} (ZMod n)) I
  let : Injective J := hJ
  obtain ⟨K, hK, aZ, haZ, hclosed⟩ :=
    exists_principalClosed_H1_detector (Y := Y') (V := V) (W := W) L s n hn J
  refine ⟨J, hJ, a, K, hK, aZ, haZ, ?_, ?_⟩
  · exact (RingHom.IsIntegral.closedSupport_le_predecessor
      (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R L))
      (Ideal.span {s}) (mem_nonZeroDivisors_iff_ne_zero.mpr hs)
      (Ideal.subset_span (by simp)) d hd)
  · intro hz
    apply hfinite f' b b' h 1 c
    apply hclosed b' j' bU hj inferInstance i' bZ hi
      (moduleFiniteImageClass (Spec.algebraMap R L) f' b b' h.w.symm
        (ULift.{u + 1} (ZMod n)) I J a 1 c)
    · exact coefficient_restriction_zero_of_composite_zero f' j' _ _
        (moduleClosedPullbackCoefficientMap (Spec.algebraMap R L) f' b b' h.w.symm
          (ULift.{u + 1} (ZMod n)) I J a) 1 c hopen
    · exact hz

end AlgebraicGeometry.Scheme.EtaleCohomology
