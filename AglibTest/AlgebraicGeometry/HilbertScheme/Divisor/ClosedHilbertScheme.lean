/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.ClosedHilbertScheme

/-! Focused consumer of `Div^θ_X` for a closed subscheme `X ⊆ P^n_A` (Kleiman,
arXiv:math/0504020v1, Thm 3.7, statement p. 23, proof p. 24): for the representation of the
Hilbert functor of `X` by the closed Hilbert scheme of `C = i.ker`, the open subscheme
representing `Div^θ_X` with its H-quasi-projectivity, Noetherianity and universal divisor, and the
representability of `Div^θ_X` by an H-quasi-projective Noetherian scheme, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i]
  (θ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n θ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)

/-- For `X` flat over `A`, `Div^θ_X` is represented by the open subscheme `divisorSchemeOver E` of
the closed Hilbert scheme, which is H-quasi-projective and Noetherian, with an open immersion into
the closed Hilbert scheme and a universal relative effective Cartier divisor. -/
example [Flat (i ≫ toSpec A ι)] :
    haveI : Finite ι := Finite.of_equiv _ e.symm
    let E := locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i
      rfl θ r hr φ hC
    Nonempty ((locallyNoetherianRelativeDivisorFunctor i rfl θ).RepresentableBy
        (divisorSchemeOver E)) ∧
      IsHQuasiProjective (divisorSchemeOver E).obj.hom ∧
      IsNoetherian (divisorScheme E) ∧
      IsOpenImmersion (divisorSchemeι E :
        divisorScheme E ⟶ (closedHilbertSchemeOver ι n e A θ r hr φ).obj.left) ∧
      Scheme.Hom.IsRelativeEffectiveCartier (universalDivisor E).subschemeι
        (pullback.snd _ (divisorSchemeOver E).obj.hom) :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  ⟨⟨locallyNoetherianRelativeDivisorFunctorRepresentableBy _⟩, inferInstance, inferInstance,
    inferInstance, isRelativeEffectiveCartier_universalDivisor _⟩

include e in
/-- **Kleiman, Thm 3.7, existence form**: for `X` flat over `A`, `Div^θ_X` is represented on
locally Noetherian test schemes by an H-quasi-projective Noetherian scheme over `Spec A`. -/
example [Flat (i ≫ toSpec A ι)] :
    ∃ D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective D.obj.hom ∧ IsNoetherian D.obj.left ∧
        Nonempty ((locallyNoetherianRelativeDivisorFunctor i rfl θ).RepresentableBy D) :=
  exists_locallyNoetherianRelativeDivisorFunctor_representableBy ι n e A i rfl θ

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_locallyNoetherianRelativeDivisorFunctor_representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.exists_locallyNoetherianRelativeDivisorFunctor_representableBy
