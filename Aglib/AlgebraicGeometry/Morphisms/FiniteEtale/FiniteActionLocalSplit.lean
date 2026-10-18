/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverNormalize
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLocalEquality
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.LocalSplitting

/-! A finite action becomes constant on a neighbourhood of a geometric point
once its object has been trivialized. The action can have arbitrary stabilizers. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange fiberToFinite)

universe u
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)
    {G : Type} [Group G] [Finite G] (D : SingleObj G ⥤ Scheme.FiniteEtale X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_open_action_trivialization {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor X).obj A ≅ D.obj (SingleObj.star G)) :
    ∃ U : X.Opens, s default ∈ U ∧
      Nonempty ((D ⋙ fiberToFinite s ⋙ trivialCoverFunctor X) ⋙ baseChange U.ι ≅
        D ⋙ baseChange U.ι) := by
  let e' := normalizedTrivialCoverIso s e
  obtain ⟨U, hu, hU⟩ := exists_open_maps_eq_of_fiber_eq s
    (fun g : G => (trivialCoverFunctor X).map ((fiberToFinite s).map (D.map g)) ≫ e'.hom)
    (fun g : G => e'.hom ≫ D.map g)
    (fun g => normalizedTrivialCoverIso_fiber_naturality s e (D.map g))
  refine ⟨U, hu, ⟨NatIso.ofComponents (fun j => ?_) (fun {i j} g => ?_)⟩⟩
  · cases j
    exact (baseChange U.ι).mapIso e'
  · cases i
    cases j
    change (baseChange U.ι).map ((trivialCoverFunctor X).map ((fiberToFinite s).map (D.map g))) ≫
        (baseChange U.ι).map e'.hom =
      (baseChange U.ι).map e'.hom ≫ (baseChange U.ι).map (D.map g)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact hU g

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9dc66d41bbdedbd2848990a4145c4bbb7643148ff8276fa5d5a3b0d04ed426fb.
Definitions, hypotheses and universes are retained modulo native names. -/
