/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.ClosedSubscheme.Representability

/-! Focused consumer of the Hilbert scheme of a closed subscheme `C ⊆ P^n_A` (Nitsure,
arXiv:math/0504590v1, Theorem 5.3, p. 24, for `E = 𝒪_C`, through the closed embedding of
Lemma 5.4 (ii), p. 25): the subfunctor, the containment criterion, the generating sections, the
representability with the closed immersion into `hilbertScheme`, Noetherianity, the universal
family, the existence statement and the bridges to the monomial and polynomial forms, with axiom
guards. -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- The points of `Hilb^Φ_C` are the points `V` of `Hilb^Φ` with `C_T ≤ V`. -/
example {A : Type u} [CommRing A] (ι : Type u) (Φ : ℚ[X])
    (C : (ProjectiveSpace A ι).IdealSheafData) (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (Z : (hilbertFunctor ι Φ).obj T) :
    Z ∈ (closedHilbertSubfunctor ι Φ C).obj T ↔
      C.comap (pullback.fst (toSpec A ι) T.unop.hom) ≤ Z.1 :=
  mem_closedHilbertSubfunctor_obj ι Φ C Z

/-- `Hilb^Φ_C` is a subfunctor of `Hilb^Φ`: its inclusion is a monomorphism. -/
example {A : Type u} [CommRing A] (ι : Type u) (Φ : ℚ[X])
    (C : (ProjectiveSpace A ι).IdealSheafData) :
    Mono (closedHilbertSubfunctor ι Φ C).ι :=
  inferInstance

/-- **Containment criterion**: `C_T ≤ V` iff the sections of `φ` vanish in `π_* 𝒪_V(r)`. -/
example {A : Type u} [CommRing A] (ι : Type u) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (r : ℕ) {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    (V : (pullback (toSpec A ι) g).IdealSheafData) :
    C.comap (pullback.fst (toSpec A ι) g) ≤ V ↔ directImageSectionMap ι g r φ V = 0 :=
  comap_le_iff_directImageSectionMap_eq_zero ι g r φ hC V

/-- For the monomial map, the section map is F13's evaluation map. -/
example {A : Type u} [CommRing A] (ι : Type u) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (r : ℕ) (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    directImageSectionMap ι g r (monomialMap ι A r) Z = directImageQuotientMap ι g Z r :=
  directImageSectionMap_monomialMap ι g r Z

/-- For homogeneous polynomials, the section pairing is `homogeneousEvaluationPairing`. -/
example {A : Type u} [CommRing A] (ι : Type u) (r : ℕ) {I : Type u}
    (s : I → MvPolynomial.homogeneousSubmodule ι A r) :
    sectionPairing ι r (homogeneousEvaluation ι r s) = homogeneousEvaluationPairing ι r s :=
  sectionPairing_homogeneousEvaluation ι r s

/-- **Generating sections**: for a Noetherian ring, `C` is cut out by sections of `𝒪(r)` for all
large `r`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (C : (ProjectiveSpace A ι).IdealSheafData) :
    ∃ m : ℤ, ∀ r : ℕ, m ≤ r → ∃ (J : Type u)
      (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
        twistingSheaf A ι (r : ℤ)),
      Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C :=
  exists_sectionPairing_imageIdealData_eq ι n e C

/-- **Representability with the closed immersion into the Hilbert scheme of `P^n_A`**, and the
representing scheme is Noetherian. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    Nonempty ((locallyNoetherianClosedHilbertSubfunctor ι A Φ C).toFunctor.RepresentableBy
        (closedHilbertSchemeOver ι n e A Φ r hr φ)) ∧
      IsClosedImmersion (closedHilbertSchemeι ι n e A Φ r hr φ) ∧
        IsNoetherian (closedHilbertScheme ι n e A Φ r hr φ) :=
  ⟨⟨locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC⟩, inferInstance,
    inferInstance⟩

/-- A morphism to the Hilbert scheme of `C` gives the pullback of the universal family along its
composite with the closed immersion. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ closedHilbertSchemeOver ι n e A Φ r hr φ) :
    ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC).homEquiv a :
        (locallyNoetherianHilbertFunctor ι A Φ).obj (op T)) =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ).op
        (universalHilbertPoint ι n e A Φ r) :=
  locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_coe ι n e A Φ r hr φ hC a

/-- **The universal family** in comap form: the pullback of the universal family of `Hilb^Φ`
along the closed immersion. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC).homEquiv (𝟙 _) :
        (locallyNoetherianHilbertFunctor ι A Φ).obj
          (op (closedHilbertSchemeOver ι n e A Φ r hr φ))).1 =
      (universalHilbertFamily ι n e A Φ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
          (closedHilbertSchemeOver ι n e A Φ r hr φ).obj.hom (closedHilbertSchemeι ι n e A Φ r hr φ)
          rfl) :=
  locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe ι n e A Φ r hr φ hC

/-- **The closed condition** on morphisms to the Hilbert scheme of `P^n_A`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (∃ a' : T.obj.left ⟶ closedHilbertScheme ι n e A Φ r hr φ,
        a' ≫ closedHilbertSchemeι ι n e A Φ r hr φ = a.hom.left) ↔
      C.comap (pullback.fst (toSpec A ι) T.obj.hom) ≤
        ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a).1 :=
  exists_lift_closedHilbertSchemeι_iff hr hC a

/-- **The universal point** of the Hilbert scheme of `C`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    (universalClosedHilbertPoint ι n e A Φ r hr φ hC).1 =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ).op
        (universalHilbertPoint ι n e A Φ r) :=
  universalClosedHilbertPoint_coe ι n e A Φ r hr φ hC

/-- **Existence**: for all large `r` the Hilbert subfunctor of `C` is represented by a closed
subscheme of the Hilbert scheme of `P^n_A`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (C : (ProjectiveSpace A ι).IdealSheafData) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ (hr : hilbertRegularityBound n Φ ≤ r) (J : Type u)
      (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
        twistingSheaf A ι (r : ℤ)),
      Nonempty ((locallyNoetherianClosedHilbertSubfunctor ι A Φ C).toFunctor.RepresentableBy
        (closedHilbertSchemeOver ι n e A Φ r hr φ)) :=
  exists_closedHilbertScheme_representableBy ι n e A Φ C

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianClosedHilbertSubfunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianClosedHilbertSubfunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isNoetherian_closedHilbertScheme' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isNoetherian_closedHilbertScheme

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_closedHilbertScheme_representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_closedHilbertScheme_representableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_closedHilbertSchemeι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_closedHilbertSchemeι_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.comap_le_iff_directImageSectionMap_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.comap_le_iff_directImageSectionMap_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_sectionPairing_imageIdealData_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_sectionPairing_imageIdealData_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalClosedHilbertPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.universalClosedHilbertPoint
