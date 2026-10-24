/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.OpenSubscheme

/-! Focused consumer of the Hilbert scheme of an open subscheme `U ⊆ P^n_A` (Nitsure,
arXiv:math/0504590v1, §6, p. 28, Exercise A): the open-locus universal property for closed
subschemes of `P^n_T`, openness of the subfunctor `Hilb^Φ_U`, and its representability by an open
subscheme of the Hilbert scheme, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- **The Hilbert scheme of an open `U ⊆ P^n_A` represents `Hilb^Φ_U`** on locally Noetherian
test schemes, and it is an open subscheme of the Hilbert scheme. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    (U : (ProjectiveSpace A ι).Opens) :
    Nonempty ((locallyNoetherianOpenHilbertSubfunctor ι A Φ U).toFunctor.RepresentableBy
        (openHilbertSchemeOver ι n e A Φ r U)) ∧
      IsOpenImmersion (openHilbertSchemeι ι n e A Φ r U) :=
  ⟨⟨locallyNoetherianOpenHilbertSubfunctorRepresentableBy ι n e A Φ r U hr⟩, inferInstance⟩

/-- The Hilbert scheme of `U` is Noetherian. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (U : (ProjectiveSpace A ι).Opens) :
    IsNoetherian (openHilbertScheme ι n e A Φ r U) :=
  inferInstance

/-- A point of the Hilbert scheme lies in the Hilbert scheme of `U` exactly when the universal
family over it lies in `U`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (U : (ProjectiveSpace A ι).Opens)
    (x : hilbertScheme ι n e A Φ r) :
    x ∈ Set.range (openHilbertSchemeι ι n e A Φ r U) ↔
      ∀ w ∈ (universalHilbertFamily ι n e A Φ r).support,
        pullback.snd (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w = x →
          pullback.fst (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w ∈ U := by
  rw [range_openHilbertSchemeι]
  exact mem_openHilbertSchemeOpens ι n e A Φ r U x

/-- The universal family of `Hilb^Φ_U` is the restriction of the universal family. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    (U : (ProjectiveSpace A ι).Opens) :
    ((locallyNoetherianOpenHilbertSubfunctorRepresentableBy ι n e A Φ r U hr).homEquiv (𝟙 _) :
        (locallyNoetherianHilbertFunctor ι A Φ).obj (op (openHilbertSchemeOver ι n e A Φ r U))).1 =
      (universalHilbertFamily ι n e A Φ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
          (openHilbertSchemeOver ι n e A Φ r U).obj.hom (openHilbertSchemeι ι n e A Φ r U)
          rfl) :=
  locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe ι n e A Φ r U hr

/-- `Hilb^Φ_U` is an open subfunctor of the Hilbert functor on all schemes over `Spec A`; no
Noetherian hypothesis is needed. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] (Φ : ℚ[X])
    (U : (ProjectiveSpace A ι).Opens) :
    Scheme.LocalRepresentability.IsOpenOverSubfunctor (openHilbertSubfunctor ι Φ U) :=
  isOpenOverSubfunctor_openHilbertSubfunctor ι Φ U

/-- **The containment locus of a closed subscheme of `P^n_T` is universal**, for an arbitrary
closed subscheme (no flatness). -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (U : (ProjectiveSpace A ι).Opens) :
    f ⁻¹ᵁ containmentLocus ι g Z U = ⊤ ↔
      ∀ x ∈ (Z.comap (baseChangeMap ι g g' f h)).support, pullback.fst (toSpec A ι) g' x ∈ U :=
  preimage_containmentLocus_eq_top_iff ι g g' f h Z U

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianOpenHilbertSubfunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianOpenHilbertSubfunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isOpenOverSubfunctor_openHilbertSubfunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isOpenOverSubfunctor_openHilbertSubfunctor
