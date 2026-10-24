/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Subsheaf

/-!
# Descent of the subsheaf `Pic^C` along surjective morphisms

Let `p : X ⟶ S` be a morphism of schemes and `C : FiberCondition p` a fiber condition
([Subsheaf](Subsheaf.lean)). A section `ξ` of `Pic_{X/S,(fppf)}` over `T` lies in `Pic^C` exactly
when it satisfies the condition at every point of `T` (`FiberCondition.mem_subfunctor_iff`), and
the condition at a point is invariant under base change (`FiberCondition.holdsAt_map`). Hence for
a morphism `g : T' ⟶ T` over `S` that is surjective on points, `g^* ξ ∈ Pic^C(T')` if and only if
`ξ ∈ Pic^C(T)` (`FiberCondition.map_mem_subfunctor_iff_of_surjective`). No flatness of `g`, and
no hypothesis on `p`, `S` or the test schemes, is used.

This is the descent of `G = Pic^C` along the quotient map `q` in the fppf form of Kleiman's
Lemma 4.9 (arXiv:math/0504020v1, p. 30; `Scheme.fppfQuotientSection_mem`), where `q` is flat,
surjective and locally of finite presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.FiberCondition

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

/-- **Descent along surjections**: if the pullback of a section `ξ` of `Pic_{X/S,(fppf)}` along a
morphism `g : T' ⟶ T` that is surjective on points lies in `Pic^C`, then `ξ` lies in `Pic^C`. -/
theorem mem_subfunctor_of_map_mem {T T' : Over S} (g : T' ⟶ T)
    (hg : Function.Surjective g.left) {ξ : (fppfPicardSheaf p).obj.obj (op T)}
    (h : (fppfPicardSheaf p).obj.map g.op ξ ∈ C.subfunctor.obj (op T')) :
    ξ ∈ C.subfunctor.obj (op T) := by
  rw [mem_subfunctor_iff] at h ⊢
  intro t
  obtain ⟨t', rfl⟩ := hg t
  exact (C.holdsAt_map g ξ t').mp (h t')

/-- Along a morphism that is surjective on points, a section of `Pic_{X/S,(fppf)}` lies in
`Pic^C` if and only if its pullback does. -/
theorem map_mem_subfunctor_iff_of_surjective {T T' : Over S} (g : T' ⟶ T)
    (hg : Function.Surjective g.left) (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    (fppfPicardSheaf p).obj.map g.op ξ ∈ C.subfunctor.obj (op T') ↔
      ξ ∈ C.subfunctor.obj (op T) :=
  ⟨C.mem_subfunctor_of_map_mem g hg, fun h => C.subfunctor.map g.op h⟩

end AlgebraicGeometry.Scheme.RelativePicard.FiberCondition
