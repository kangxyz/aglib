/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantOpenFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Value
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackCoefficientIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.ConstantRestriction

/-! # Original open-curve comparison with native finite constant values

The existing small-value theorem is transported through one actual additive
iso. The final coefficient and original pullback remain unchanged. For a
specified constant trivialization, annihilation is reflected through the
original constant functor using a point of the nonempty source scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteValueOpenFieldExtension

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
  (X : FScheme k) (hX : Curve.Properties X)
  {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]

include hX in
/-- Original H1 pullback for an arbitrary finite value in the native sheaf
universe, retaining its actual positive invertible annihilator. -/
theorem h1Pullback_bijective_finiteValue (A : AddCommGrpCat.{u + 1}) [Finite A]
    (N : ℕ) (hpos : 0 < N) (hA : ∀ a : A, N • a = 0)
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    Function.Bijective (h1Pullback.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K))
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) := by
  obtain ⟨B, _, _, ⟨e⟩⟩ := ConstantFinite.exists_small_finiteValueIso A
  let f := pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)
  let eF := (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e
  have hB (b : B) : N • b = 0 := by
    have h := hA (e.hom (ULift.up b))
    have h' : e.hom (N • ULift.up b) = e.hom 0 := by simpa using h
    have he := (Iso.addCommGroupIsoToAddEquiv e).injective h'
    exact congrArg ULift.down he
  have hb := ConstantOpenFieldExtension.constantRestriction_bijective
    k K X hX j B N hpos hB hk
  have hcomp : ⇑(constantRestriction B f 1) =
      (Sheaf.H.map ((inverseImageConstantIso f).app (ConstantFinite.value B)).hom 1) ∘
        h1Pullback f (ConstantFinite.coefficient B U) := by
    funext a
    rw [constantRestriction_apply, cohomologyPullback_one]
    rfl
  rw [hcomp] at hb
  have hb' : Function.Bijective (h1Pullback f (ConstantFinite.coefficient B U)) :=
    Function.Bijective.of_comp_left hb
      (cohomologyMapIso_bijective ((inverseImageConstantIso f).app
        (ConstantFinite.value B)) 1).injective
  exact ⟨cohomologyPullback_injective_of_iso f eF 1 hb'.injective,
    cohomologyPullback_surjective_of_iso f eF 1 hb'.surjective⟩

include hX in
/-- An actual constant trivialization gives original H1 comparison, with its
annihilator reflected from the original sheaf rather than separately assumed
on the chosen value. -/
theorem h1Pullback_bijective_of_constantIso
    (F : AbelianSheaf.{u, u + 1} U) (A : AddCommGrpCat.{u + 1}) [Finite A]
    (e : F ≅ (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (N : ℕ) (hpos : 0 < N) (hF : KilledBy N F)
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    Function.Bijective (h1Pullback.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) F) := by
  have hc : KilledBy N
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) := by
    apply (cancel_epi e.hom).mp
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    have h := congrArg (fun a : F ⟶ F => a ≫ e.hom) hF
    simpa [KilledBy] using h
  have hv : N • 𝟙 A = 0 := by
    apply Constructible.FiniteColimits.constant_map_injective_at_point U A A
      (Classical.choice (inferInstance : Nonempty U))
    simpa [KilledBy] using hc
  have hA (a : A) : N • a = 0 := by
    exact ConcreteCategory.congr_hom hv a
  have hb := h1Pullback_bijective_finiteValue k K X hX j A N hpos hA hk
  let f := pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)
  exact ⟨cohomologyPullback_injective_of_iso f e.symm 1 hb.injective,
    cohomologyPullback_surjective_of_iso f e.symm 1 hb.surjective⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteValueOpenFieldExtension
