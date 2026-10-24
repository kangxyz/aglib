/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.ClosedImmersion

/-! Focused consumer of the Hilbert functor of a closed subscheme `X ⊆ P^n_A`, X-first (Nitsure,
arXiv:math/0504590v1, Thm 6.1, p. 28, for a closed `X`): its identification with the Hilbert
subfunctor of `C = i.ker` on locally Noetherian test schemes, by the identity on values, its
representation by the closed Hilbert scheme of `C` with the universal family and the image in
`P^n`, H-quasi-projectivity, and the existence statement, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- The Hilbert functor of a closed `X` is the Hilbert subfunctor of `C = i.ker` on locally
Noetherian test schemes; the isomorphism sends a family `W` contained in `X` to `W.comap i_T`. -/
example {A : Type u} [CommRing A] {ι : Type u} [Finite ι] {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] (Φ : ℚ[X])
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (W : (locallyNoetherianClosedHilbertSubfunctor ι A Φ i.ker).toFunctor.obj T) :
    ((locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion i rfl Φ).inv.app T W).1 =
      W.1.1.comap (immersionBaseChange i rfl T.unop.obj.hom) :=
  rfl

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i]
  (θ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n θ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)

/-- The closed Hilbert scheme of `C = i.ker` represents the Hilbert functor of `X` (X-first) and is
H-quasi-projective; a point is the pullback to `X ×_{Spec A} T` of the corresponding point of
`Hilb^θ_C`, whose image in `P^n` it is, and the universal family is the pullback of the universal
family of the Hilbert scheme of `P^n_A`. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ closedHilbertSchemeOver ι n e A θ r hr φ) :
    IsHQuasiProjective (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom ∧
      ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i rfl θ
          r hr φ hC).homEquiv a).1 =
        ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).homEquiv
          a).1.1.comap (immersionBaseChange i rfl T.obj.hom) ∧
      ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i rfl θ
          r hr φ hC).homEquiv a).1.map (immersionBaseChange i rfl T.obj.hom) =
        ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).homEquiv
          a).1.1 ∧
      ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i rfl θ
          r hr φ hC).homEquiv (𝟙 _)).1 =
        ((universalHilbertFamily ι n e A θ r).comap
          (baseChangeMap ι (hilbertSchemeOver ι n e A θ r).obj.hom
            (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom
            (closedHilbertSchemeι ι n e A θ r hr φ) rfl)).comap
          (immersionBaseChange i rfl (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom) :=
  ⟨inferInstance,
    locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe hC a,
    locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe_map hC
      a,
    locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_id_coe hC⟩

include e in
/-- The Hilbert functor of a closed `X ⊆ P^n_A` is represented on locally Noetherian test schemes
by an H-quasi-projective scheme over `Spec A`. -/
example :
    ∃ H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective H.obj.hom ∧
        Nonempty ((locallyNoetherianImmersedHilbertFunctor i rfl θ).RepresentableBy H) :=
  exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion ι n e A i rfl
    θ

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctorIsoClosedHilbertSubfunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctorIsoClosedHilbertSubfunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_closedHilbertSchemeOver_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_closedHilbertSchemeOver_hom

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion
