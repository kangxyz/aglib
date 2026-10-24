/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Representability

/-! Focused consumer of the openness of `Div^θ_X` in `Hilb^θ_X` (Kleiman, arXiv:math/0504020v1,
Thm 3.7, statement p. 23, proof p. 24): the divisor locus of a family and its factorization
criterion, the open-subfunctor statement, and, for any representation of `Hilb^θ_X`, the open
subscheme representing `Div^θ_X` with its universal divisor, H-quasi-projectivity and
Noetherianity, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Scheme.LocalRepresentability
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι] {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (θ : ℚ[X])

/-- A morphism `g : Z ⟶ T` of locally Noetherian test schemes factors through the divisor locus of
a family `ξ ∈ Hilb^θ_X(T)` if and only if `ξ` pulls back to a relative effective Cartier divisor;
hence `Div^θ_X` is an open subfunctor of `Hilb^θ_X`. -/
example {T Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (ξ : (locallyNoetherianImmersedHilbertFunctor i rfl θ).obj (op T)) (g : Z ⟶ T) :
    (g.hom.left ⁻¹ᵁ divisorLocus ξ = ⊤ ↔
        Scheme.Hom.IsRelativeEffectiveCartier
          ((locallyNoetherianImmersedHilbertFunctor i rfl θ).map g.op ξ).1.subschemeι
          (pullback.snd _ Z.obj.hom)) ∧
      IsOpenSubfunctor (locallyNoetherianRelativeDivisorSubfunctor i rfl θ) :=
  ⟨preimage_divisorLocus_eq_top_iff ξ g,
    isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor⟩

/-- A point of `T` lies in the divisor locus of `ξ` if and only if the fibre of `ξ` over it is an
effective Cartier divisor of the fibre of `X ×_{Spec A} T`. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (ξ : (locallyNoetherianImmersedHilbertFunctor i rfl θ).obj (op T)) (t : T.obj.left) :
    t ∈ divisorLocus ξ ↔
      Scheme.Hom.FiberIsEffectiveCartier ξ.1.subschemeι (pullback.snd _ T.obj.hom) t :=
  mem_divisorLocus ξ t

variable {H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianImmersedHilbertFunctor i rfl θ).RepresentableBy H)

/-- `Div^θ_X` is represented by the open subscheme `divisorSchemeOver E` of the representing
scheme `H` of `Hilb^θ_X`, compatibly with `Hilb^θ_X`. -/
example {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : Z ⟶ divisorSchemeOver E) :
    Nonempty ((locallyNoetherianRelativeDivisorFunctor i rfl θ).RepresentableBy
        (divisorSchemeOver E)) ∧
      ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv a).1 =
        (E.homEquiv (a ≫ divisorSchemeToHilbertScheme E)).1 ∧
      IsOpenImmersion (divisorSchemeι E) ∧
      (divisorSchemeToHilbertScheme E).hom.left = divisorSchemeι E :=
  ⟨⟨locallyNoetherianRelativeDivisorFunctorRepresentableBy E⟩,
    locallyNoetherianRelativeDivisorFunctorRepresentableBy_homEquiv_coe E a, inferInstance,
    divisorSchemeToHilbertScheme_hom_left E⟩

/-- A morphism `a : Z ⟶ H` factors through the scheme of `Div^θ_X` if and only if the point of
`Hilb^θ_X(Z)` it classifies is a relative effective Cartier divisor. -/
example {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : Z ⟶ H) :
    a.hom.left ⁻¹ᵁ divisorLocus (E.homEquiv (𝟙 H)) = ⊤ ↔
      Scheme.Hom.IsRelativeEffectiveCartier (E.homEquiv a).1.subschemeι
        (pullback.snd _ Z.obj.hom) :=
  preimage_divisorLocus_homEquiv_id_eq_top_iff E a

/-- The universal divisor is a relative effective Cartier divisor and a point of `Div^θ_X`, and it
is the restriction of the universal family of `Hilb^θ_X`; every point is a pullback of it. -/
example {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : Z ⟶ divisorSchemeOver E) :
    Scheme.Hom.IsRelativeEffectiveCartier (universalDivisor E).subschemeι
        (pullback.snd _ (divisorSchemeOver E).obj.hom) ∧
      IsRelativeDivisorFamily i rfl θ (divisorSchemeOver E).obj.hom (universalDivisor E) ∧
      universalDivisor E = (E.homEquiv (𝟙 H)).1.comap (pullback.map _
        (divisorSchemeOver E).obj.hom _ H.obj.hom (𝟙 X) (divisorSchemeι E) (𝟙 _) (by simp)
        (by rw [Category.comp_id, divisorSchemeOver_hom])) ∧
      ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv a).1 =
        (universalDivisor E).comap (pullback.map _ Z.obj.hom _ (divisorSchemeOver E).obj.hom
          (𝟙 X) a.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w a.hom])) :=
  ⟨isRelativeEffectiveCartier_universalDivisor E, isRelativeDivisorFamily_universalDivisor E,
    universalDivisor_eq E,
    locallyNoetherianRelativeDivisorFunctorRepresentableBy_homEquiv_coe_eq_comap E a⟩

/-- Over a Noetherian ring, `Div^θ_X` is H-quasi-projective and Noetherian when `H` is
H-quasi-projective. -/
example [IsNoetherianRing A] [IsHQuasiProjective H.obj.hom] :
    IsHQuasiProjective (divisorSchemeOver E).obj.hom ∧ IsNoetherian (divisorSchemeOver E).obj.left :=
  ⟨inferInstance, IsHQuasiProjective.isNoetherian (divisorSchemeOver E).obj.hom⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.preimage_divisorLocus_eq_top_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.preimage_divisorLocus_eq_top_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianRelativeDivisorFunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianRelativeDivisorFunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isRelativeEffectiveCartier_universalDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isRelativeEffectiveCartier_universalDivisor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalDivisor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.universalDivisor_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_divisorSchemeOver_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_divisorSchemeOver_hom
