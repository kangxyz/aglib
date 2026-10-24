/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Subfunctor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-! Focused consumer of the description of the families of `Hilb^Φ` contained in an immersed
scheme `Y ⊆ P^n_A` (the combination step of Nitsure, arXiv:math/0504590v1, Thm 6.1, p. 28): the
closed and the open condition for `C = i.ker` and `U = i.coborderRange`, the meet of the closed
and the open Hilbert subfunctor, the closed case, and the restriction to locally Noetherian test
schemes, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {Y : Scheme.{u}}

/-- **Over a Noetherian ring, the families of `Hilb^Φ` contained in a locally closed subscheme
`Y ⊆ P^n_A` are `Hilb^Φ_C ⊓ Hilb^Φ_U`**, for the scheme-theoretic image `C` and `U` the largest
open in which `Y` is closed: every immersion into `P^n_A` is quasi-compact. -/
example [IsNoetherianRing A] [Finite ι] (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]
    (Φ : ℚ[X]) :
    immersedHilbertSubfunctor i rfl Φ =
      closedHilbertSubfunctor ι Φ i.ker ⊓ openHilbertSubfunctor ι Φ i.coborderRange :=
  have := quasiCompact_of_isImmersion_of_isLocallyNoetherian i
  immersedHilbertSubfunctor_eq_inf i rfl Φ

/-- A closed subscheme of `P^n_T` lies in `Y_T` exactly when it lies in `C_T` and in `U_T`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] [QuasiCompact i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (W : (pullback (toSpec A ι) g).IdealSheafData) :
    (∃ w : W.subscheme ⟶ pullback (i ≫ toSpec A ι) g,
        w ≫ immersionBaseChange i rfl g = W.subschemeι) ↔
      i.ker.comap (pullback.fst (toSpec A ι) g) ≤ W ∧
        ∀ x ∈ W.support, pullback.fst (toSpec A ι) g x ∈ i.coborderRange :=
  exists_lift_immersionBaseChange_iff_closed_and_open i rfl

/-- The closed condition needs no hypothesis on `i`: a family in `Y_T` lies in `C_T`. -/
example (i : Y ⟶ ProjectiveSpace A ι) {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (W : (pullback (toSpec A ι) g).IdealSheafData)
    (w : W.subscheme ⟶ pullback (i ≫ toSpec A ι) g)
    (hw : w ≫ immersionBaseChange i rfl g = W.subschemeι) :
    i.ker.comap (pullback.fst (toSpec A ι) g) ≤ W :=
  comap_ker_le_of_comp_eq i rfl hw

/-- `W ⊆ C_T` exactly when `W ⟶ P^n_A` factors through `C`. -/
example {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (W : (pullback (toSpec A ι) g).IdealSheafData) (C : (ProjectiveSpace A ι).IdealSheafData) :
    C.comap (pullback.fst (toSpec A ι) g) ≤ W ↔
      ∃ a : W.subscheme ⟶ C.subscheme,
        a ≫ C.subschemeι = W.subschemeι ≫ pullback.fst (toSpec A ι) g :=
  comap_fst_le_iff_exists_lift g W C

/-- **The closed case**: the families contained in a closed subscheme `C ⊆ P^n_A` are the Hilbert
subfunctor of `C`. -/
example (C : (ProjectiveSpace A ι).IdealSheafData) (Φ : ℚ[X]) :
    immersedHilbertSubfunctor C.subschemeι rfl Φ = closedHilbertSubfunctor ι Φ C :=
  immersedHilbertSubfunctor_subschemeι Φ C

/-- On locally Noetherian test schemes, the Nitsure-form Hilbert functor of `Y` is isomorphic to
the restricted subfunctor of families contained in `Y`, by `V ↦ V.map i_T` and `W ↦ W.comap i_T`. -/
example [Finite ι] (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X])
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (V : (locallyNoetherianImmersedHilbertFunctor i rfl Φ).obj T)
    (W : (locallyNoetherianImmersedHilbertSubfunctor i rfl Φ).toFunctor.obj T) :
    ((locallyNoetherianImmersedHilbertFunctorIso i rfl Φ).hom.app T V).1.1 =
        V.1.map (immersionBaseChange i rfl T.unop.obj.hom) ∧
      ((locallyNoetherianImmersedHilbertFunctorIso i rfl Φ).inv.app T W).1 =
        W.1.1.comap (immersionBaseChange i rfl T.unop.obj.hom) :=
  ⟨locallyNoetherianImmersedHilbertFunctorIso_hom_app_coe i rfl Φ T V,
    locallyNoetherianImmersedHilbertFunctorIso_inv_app_coe i rfl Φ T W⟩

/-- A family contained in `Y` is the image of its pullback to `Y_T`; no hypothesis on `i`. -/
example (i : Y ⟶ ProjectiveSpace A ι) (Φ : ℚ[X]) {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ}
    (W : (hilbertFunctor ι Φ).obj T) (hW : W ∈ (immersedHilbertSubfunctor i rfl Φ).obj T) :
    (W.1.comap (immersionBaseChange i rfl T.unop.hom)).map (immersionBaseChange i rfl T.unop.hom) =
      W.1 :=
  map_comap_immersionBaseChange_of_mem i rfl Φ hW

/-- **The closed case**: for a closed immersion `i`, the kernel of `i_T` is `C_T`, a closed
subscheme of `P_T` lies in `Y_T` exactly when it lies in `C_T`, and the families contained in `Y`
are the Hilbert subfunctor of `C = i.ker`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback (toSpec A ι) g).IdealSheafData) (Φ : ℚ[X]) :
    (immersionBaseChange i rfl g).ker = i.ker.comap (pullback.fst (toSpec A ι) g) ∧
      ((∃ w : V.subscheme ⟶ pullback (i ≫ toSpec A ι) g,
          w ≫ immersionBaseChange i rfl g = V.subschemeι) ↔
        i.ker.comap (pullback.fst (toSpec A ι) g) ≤ V) ∧
      immersedHilbertSubfunctor i rfl Φ = closedHilbertSubfunctor ι Φ i.ker :=
  ⟨ker_immersionBaseChange i rfl g, exists_lift_immersionBaseChange_iff i rfl g V,
    immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker i rfl Φ⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_immersionBaseChange_iff_closed_and_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_immersionBaseChange_iff_closed_and_open

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_eq_inf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_eq_inf

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_subschemeι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_subschemeι

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctorIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_comap_immersionBaseChange_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_comap_immersionBaseChange_of_mem

/--
info: 'AlgebraicGeometry.ProjectiveSpace.ker_immersionBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ker_immersionBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_immersionBaseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_immersionBaseChange_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker
