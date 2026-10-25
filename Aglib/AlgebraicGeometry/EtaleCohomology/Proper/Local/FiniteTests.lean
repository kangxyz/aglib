/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange

/-! # Original cohomology tests on finite direct images

The original finite cohomology equivalences and finite exchange transport
surjectivity and injectivity of the original pullback to finite direct-image
coefficients. These implications retain the actual original square, coefficient
and all four independent Ext universes. They impose no torsion condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS eX' eS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsFinite f]
  (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)

include f' h

/-- Surjectivity of the actual source pullback gives surjectivity on the
actual finite direct-image coefficient, through the original exchange square. -/
theorem cohomologyPullback_finiteDirectImage_surjective
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Surjective (cohomologyPullback.{u, eX, eX'} g' F q)) :
    Function.Surjective (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  have : IsIso ((baseChangeMap f f' g g' h.w.symm).app F) :=
    Finite.finiteBaseChange_app_isIso f f' g g' h F
  let e := Finite.finiteCohomologyDirectImageAddEquiv f F q
  let e' := Finite.finiteCohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
  intro y
  obtain ⟨x, hx⟩ := hF (e' (Sheaf.H.map
    ((baseChangeMap f f' g g' h.w.symm).app F) q y))
  refine ⟨e.symm x, ?_⟩
  apply (cohomologyMapIso_bijective
    (asIso ((baseChangeMap f f' g g' h.w.symm).app F)) q).injective
  apply e'.injective
  calc
    _ = cohomologyPullback g' F q (e (e.symm x)) :=
      Finite.finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h F q (e.symm x)
    _ = _ := by simpa only [AddEquiv.apply_symm_apply, asIso_hom] using hx

/-- Injectivity likewise transports to the same finite direct-image coefficient.
Only the source comparison's injectivity is an additional premise. -/
theorem cohomologyPullback_finiteDirectImage_injective
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Injective (cohomologyPullback.{u, eX, eX'} g' F q)) :
    Function.Injective (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let e := Finite.finiteCohomologyDirectImageAddEquiv f F q
  intro a b hab
  apply e.injective
  apply hF
  rw [← Finite.finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h,
    ← Finite.finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h, hab]

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
