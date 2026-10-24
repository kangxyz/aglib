/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Representability

/-! Focused consumer of the Hilbert scheme of a locally closed subscheme `Y ⊆ P^n_A` (Nitsure,
arXiv:math/0504590v1, Thm 6.1, p. 28, for `E = 𝒪_Y` and trivial bundles): the representability of
the Nitsure-form Hilbert functor of `Y` and of the subfunctor of families contained in `Y`, the
immersion into the Hilbert scheme of `P^n_A`, the universal family, the lifting criterion and the
existence for large `r`, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
  (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The Hilbert scheme of `Y` represents the Hilbert functor of `Y`** on locally Noetherian
test schemes, and it is a Noetherian, locally closed subscheme of the Hilbert scheme of `P^n_A`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    Nonempty ((locallyNoetherianImmersedHilbertFunctor i rfl Φ).RepresentableBy
        (immersedHilbertSchemeOver ι n e A Φ r hr φ i)) ∧
      IsImmersion (immersedHilbertSchemeι ι n e A Φ r hr φ i) ∧
        IsNoetherian (immersedHilbertScheme ι n e A Φ r hr φ i) :=
  ⟨⟨locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i rfl hC⟩,
    inferInstance, inferInstance⟩

/-- The families of `Hilb^Φ` contained in `Y` are represented by the same scheme; a morphism
corresponds to the pullback of the universal family of the Hilbert scheme of `P^n_A`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i) :
    ((locallyNoetherianImmersedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ i rfl hC).homEquiv
        a : (locallyNoetherianHilbertFunctor ι A Φ).obj (op T)) =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).op
        (universalHilbertPoint ι n e A Φ r) :=
  locallyNoetherianImmersedHilbertSubfunctorRepresentableBy_homEquiv_coe ι n e A Φ r hr φ i rfl hC a

/-- **The lifting criterion**: a morphism to the Hilbert scheme of `P^n_A` factors through the
Hilbert scheme of `Y` exactly when its family is contained in `Y`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (∃ c : T.obj.left ⟶ immersedHilbertScheme ι n e A Φ r hr φ i,
        c ≫ immersedHilbertSchemeι ι n e A Φ r hr φ i = a.hom.left) ↔
      (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a ∈
        (immersedHilbertSubfunctor i rfl Φ).obj (op T.obj) :=
  exists_lift_immersedHilbertSchemeι_iff rfl hC a

/-- **The universal family** `D^Φ ⊆ Y ×_{Spec A} H^Φ_Y` corresponds to the identity, and its image
in `P^n_A ×_{Spec A} H^Φ_Y` is the restriction of the universal family of the Hilbert scheme of
`P^n_A`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (universalImmersedHilbertPoint ι n e A Φ r hr φ i rfl hC).1 =
        universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl ∧
      (universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl).map
          (immersionBaseChange i rfl (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom) =
        (universalHilbertFamily ι n e A Φ r).comap
          (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
            (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
            (immersedHilbertSchemeι ι n e A Φ r hr φ i)
            (Over.w (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom)) :=
  ⟨universalImmersedHilbertPoint_coe ι n e A Φ r hr φ i rfl hC,
    map_universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl hC⟩

/-- The universal point is a closed subscheme of `Y ×_{Spec A} H^Φ_Y`, proper and flat over
`H^Φ_Y`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    IsProper ((universalImmersedHilbertPoint ι n e A Φ r hr φ i rfl hC).1.subschemeι ≫
        pullback.snd _ _) ∧
      Flat ((universalImmersedHilbertPoint ι n e A Φ r hr φ i rfl hC).1.subschemeι ≫
        pullback.snd _ _) :=
  ⟨(universalImmersedHilbertPoint ι n e A Φ r hr φ i rfl hC).2.isProper,
    (universalImmersedHilbertPoint ι n e A Φ r hr φ i rfl hC).2.flat⟩

/-- **The point given by `a : T ⟶ H^Φ_Y` is the pullback of the universal family**, which is
itself a point of the Hilbert functor of `Y`. -/
example (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i rfl hC).homEquiv
        a).1 =
        (universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl).comap
          (pullback.map (i ≫ toSpec A ι) T.obj.hom (i ≫ toSpec A ι)
            (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom (𝟙 Y) a.hom.left (𝟙 _)
            (by simp) (by rw [Category.comp_id, Over.w a.hom])) ∧
      IsImmersedHilbertFamily i rfl Φ (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
        (universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl) :=
  ⟨locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_eq_comap ι n e A Φ r hr φ i rfl
      hC a,
    isImmersedHilbertFamily_universalImmersedHilbertFamily ι n e A Φ r hr φ i rfl hC⟩

/-- **Existence**: for every large `r` there are sections `φ` for which the Hilbert scheme of `Y`
represents its Hilbert functor. -/
example : ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ (hr : hilbertRegularityBound n Φ ≤ r) (J : Type u)
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ)),
    Nonempty ((locallyNoetherianImmersedHilbertFunctor i rfl Φ).RepresentableBy
      (immersedHilbertSchemeOver ι n e A Φ r hr φ i)) :=
  exists_immersedHilbertScheme_representableBy ι n e A Φ i rfl

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertSubfunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertSubfunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_immersedHilbertSchemeι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_immersedHilbertSchemeι_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_universalImmersedHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_universalImmersedHilbertFamily

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_immersedHilbertScheme_representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_immersedHilbertScheme_representableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.universalImmersedHilbertPoint_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.universalImmersedHilbertPoint_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_eq_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_eq_comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamily_universalImmersedHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamily_universalImmersedHilbertFamily
