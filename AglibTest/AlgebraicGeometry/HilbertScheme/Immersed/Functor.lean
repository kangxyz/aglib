/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor

/-! Focused consumer of the Hilbert functor of an immersed scheme (Nitsure, arXiv:math/0504590v1,
§1, pp. 3–4; Thm 6.1, p. 28): the bridge between closed subschemes of `Y_T` proper over `T` and
closed subschemes of `P_T` contained in `Y_T`, the functor and its isomorphism with the
subfunctor of `Hilb^Φ` of families contained in `Y`, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {Y : Scheme.{u}}

/-- The Hilbert functor of a locally closed subscheme `Y ⊆ P^n_A`, with structure morphism
`i ≫ toSpec A ι`, on all schemes over `Spec A`, and its restriction to locally Noetherian test
schemes. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X]) :
    ((Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u) ×
      ((Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u) :=
  (immersedHilbertFunctor i rfl Φ, locallyNoetherianImmersedHilbertFunctor i rfl Φ)

/-- The base change `i_T` is Mathlib's `pullback.map` of `i` and its over-category base change,
and it is again an immersion. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) :
    immersionBaseChange i rfl g =
        pullback.map _ g (toSpec A ι) g i (𝟙 T) (𝟙 _) (by simp) (by simp) ∧
      immersionBaseChange i rfl g = ((Over.pullback g).map
        (Over.homMk (U := Over.mk (i ≫ toSpec A ι)) (V := Over.mk (toSpec A ι)) i rfl)).left ∧
      IsImmersion (immersionBaseChange i rfl g) :=
  ⟨immersionBaseChange_eq_pullbackMap i rfl g, immersionBaseChange_eq_overPullbackMap i rfl g,
    inferInstance⟩

/-- A closed subscheme of `Y_T` is proper over `T` if and only if it is closed in
`P_T`. -/
example [Finite ι] (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData) :
    IsProper (V.subschemeι ≫ pullback.snd _ g) ↔
      IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i rfl g) :=
  isProper_subschemeι_comp_snd_iff_isClosedImmersion i rfl g V

/-- `V ↦ V.map i_T` and `W ↦ W.comap i_T` are inverse bijections. -/
example [Finite ι] (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (V : {V : (pullback (i ≫ toSpec A ι) g).IdealSheafData //
      IsProper (V.subschemeι ≫ pullback.snd _ g)}) :
    ((properClosedSubschemeEquiv i rfl g V).1.comap (immersionBaseChange i rfl g)) = V.1 := by
  rw [← properClosedSubschemeEquiv_symm_apply_coe, Equiv.symm_apply_apply]

/-- Both maps commute with base change along `f : T' ⟶ T` over `Spec A`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i rfl g)]
    (W : (pullback (toSpec A ι) g).IdealSheafData) :
    (V.map (immersionBaseChange i rfl g)).comap (baseChangeMap ι g (f ≫ g) f rfl) =
        (V.comap (pullback.map _ (f ≫ g) _ g (𝟙 Y) f (𝟙 _) (by simp) (by simp))).map
          (immersionBaseChange i rfl (f ≫ g)) ∧
      (W.comap (immersionBaseChange i rfl g)).comap
          (pullback.map _ (f ≫ g) _ g (𝟙 Y) f (𝟙 _) (by simp) (by simp)) =
        (W.comap (baseChangeMap ι g (f ≫ g) f rfl)).comap (immersionBaseChange i rfl (f ≫ g)) :=
  ⟨comap_baseChangeMap_map_immersionBaseChange i rfl g (f ≫ g) f rfl V,
    comap_pullbackMap_comap_immersionBaseChange i rfl g (f ≫ g) f rfl W⟩

/-- Points of the Hilbert functor of `Y` are closed in `P_T` and flat over `T`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X])
    {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (V : (immersedHilbertFunctor i rfl Φ).obj T) :
    IsClosedImmersion (V.1.subschemeι ≫ immersionBaseChange i rfl T.unop.hom) ∧
      Flat (V.1.subschemeι ≫ pullback.snd _ T.unop.hom) :=
  ⟨V.2.isClosedImmersion, V.2.flat⟩

/-- The Nitsure-form functor is isomorphic to the subfunctor of `Hilb^Φ` of the families whose
inclusion factors through `i_T`; the isomorphism is the image `V ↦ V.map i_T`, with inverse
`W ↦ W.comap i_T`. -/
example [Finite ι] (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X])
    (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ) (V : (immersedHilbertFunctor i rfl Φ).obj T)
    (W : (immersedHilbertSubfunctor i rfl Φ).toFunctor.obj T) :
    ((immersedHilbertFunctorIso i rfl Φ).hom.app T V).1.1 =
        V.1.map (immersionBaseChange i rfl T.unop.hom) ∧
      ((immersedHilbertFunctorIso i rfl Φ).inv.app T W).1 =
        W.1.1.comap (immersionBaseChange i rfl T.unop.hom) :=
  ⟨immersedHilbertFunctorIso_hom_app_coe i rfl Φ T V,
    immersedHilbertFunctorIso_inv_app_coe i rfl Φ T W⟩

/-- For a closed subscheme `X = V(C)` of `P^n_A` (the case of `Div^θ_X`), properness of a point
is automatic. -/
example [Finite ι] (C : (ProjectiveSpace A ι).IdealSheafData) (Φ : ℚ[X]) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback (C.subschemeι ≫ toSpec A ι) g).IdealSheafData) :
    IsImmersedHilbertFamily C.subschemeι rfl Φ g V ↔
      IsHilbertFamily ι Φ g (V.map (immersionBaseChange C.subschemeι rfl g)) :=
  isImmersedHilbertFamily_iff_of_isClosedImmersion C.subschemeι rfl Φ g V

/-- Membership in the subfunctor of families contained in `Y`. -/
example (i : Y ⟶ ProjectiveSpace A ι) (Φ : ℚ[X]) {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ}
    (W : (hilbertFunctor ι Φ).obj T) :
    W ∈ (immersedHilbertSubfunctor i rfl Φ).obj T ↔
      ∃ w : W.1.subscheme ⟶ pullback (i ≫ toSpec A ι) T.unop.hom,
        w ≫ immersionBaseChange i rfl T.unop.hom = W.1.subschemeι :=
  mem_immersedHilbertSubfunctor_obj i rfl Φ W

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_immersionBaseChange_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_immersionBaseChange_baseChangeMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isProper_subschemeι_comp_snd_iff_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isProper_subschemeι_comp_snd_iff_isClosedImmersion

/--
info: 'AlgebraicGeometry.ProjectiveSpace.properClosedSubschemeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.properClosedSubschemeEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.comap_baseChangeMap_map_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.comap_baseChangeMap_map_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamily.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsImmersedHilbertFamily.comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertFunctorIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamily_iff_of_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isImmersedHilbertFamily_iff_of_isClosedImmersion
