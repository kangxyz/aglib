/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The complement of the image of a closed set under a universally closed morphism

Let `f : X ⟶ Y` be a universally closed morphism of schemes (Stacks, Tag 01KB, Definition
26.20.1) and `C ⊆ X` a closed set. Then `f(C)` is closed (`Scheme.Hom.isClosedMap`), and its
complement `f.complImage C` is an open of `Y`: the points `y` whose fibre `f⁻¹(y)` is disjoint
from `C` (`Scheme.Hom.mem_complImage`), that is, the points over which `C` is empty. It is
universal for this condition: for a cartesian square of schemes
```
P --fst--> X
|          |
snd        f
v          v
Y' --g---> Y
```
the morphism `g` factors through `f.complImage C` (that is, `g ⁻¹ᵁ f.complImage C = ⊤`) if and
only if the preimage of `C` in `P = X ×_Y Y'` is empty
(`Scheme.preimage_complImage_eq_top_iff_of_isPullback`). The proof uses only that images commute
with base change on points, `snd(fst⁻¹ C) = g⁻¹ (f C)`: the points of a fibre product surject onto
the pairs of points with the same image (`Scheme.exists_preimage_of_isPullback`; Stacks, Tag 01JT,
Lemma 26.17.5).

For `i : X ⟶ W` and an open `O ⊆ W`, the open `f.complImage (i ⁻¹ᵁ O).compl` consists of the
points over which the fibre of `f` maps into `O` (`Scheme.Hom.mem_complImage_compl_preimage`), and
`g` factors through it if and only if the base change `P ⟶ X ⟶ W` maps into `O`
(`Scheme.preimage_complImage_compl_preimage_eq_top_iff_of_isPullback`). For a proper family
`V ⟶ T` with `V ⊆ X_T` and an open `U ⊆ X` (with `i : V ⟶ X`), this is the open locus of the
points `t ∈ T` with `V_t ⊆ U_t`, universal for the condition "`V_{T'} ⊆ U_{T'}`". No flatness
or Noetherian hypothesis is needed.

This is the topological part of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §6, p. 28, first Exercise ("Exercise A"), with closed sets in place of
supports of coherent sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]

/-- **The complement of the image of a closed set** under a universally closed morphism
`f : X ⟶ Y`: the open set `Y ∖ f(C)` of the points of `Y` whose fibre is disjoint from the closed
set `C ⊆ X`. It is open since `f` is a closed map. -/
def complImage (C : Closeds X) : Y.Opens :=
  ⟨(f '' C)ᶜ, (f.isClosedMap _ C.isClosed).isOpen_compl⟩

theorem coe_complImage (C : Closeds X) : (f.complImage C : Set Y) = (f '' C)ᶜ :=
  rfl

/-- A point lies in `f.complImage C` if and only if no point of `C` maps to it. -/
theorem mem_complImage (C : Closeds X) (y : Y) : y ∈ f.complImage C ↔ ∀ x ∈ C, f x ≠ y := by
  change y ∉ f '' C ↔ _
  constructor
  · intro hy x hx hxy
    exact hy ⟨x, hx, hxy⟩
  · rintro hy ⟨x, hx, hxy⟩
    exact hy x hx hxy

/-- A point lies in `f.complImage (i ⁻¹ᵁ O).compl` if and only if every point of its fibre maps
into `O` under `i : X ⟶ W`. -/
theorem mem_complImage_compl_preimage {W : Scheme.{u}} (i : X ⟶ W) (O : W.Opens) (y : Y) :
    y ∈ f.complImage (i ⁻¹ᵁ O).compl ↔ ∀ x, f x = y → i x ∈ O := by
  rw [mem_complImage]
  constructor
  · intro h x hxy
    by_contra hx
    exact h x hx hxy
  · intro h x hx hxy
    exact hx (h x hxy)

end Scheme.Hom

namespace Scheme

/-- **The complement of the image of a closed set is universal** (Nitsure, arXiv:math/0504590v1,
§6, p. 28, Exercise A, topological part): for a cartesian square with `f : X ⟶ Y` universally
closed and base change `fst : P ⟶ X` of `g : Y' ⟶ Y`, the morphism `g` factors through
`f.complImage C` if and only if the preimage of `C` in `P` is empty. Images commute with base
change on points (`exists_preimage_of_isPullback`; Stacks, Tag 01JT). -/
theorem preimage_complImage_eq_top_iff_of_isPullback {P X Y Y' : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [UniversallyClosed f] (h : IsPullback fst snd f g)
    (C : Closeds X) : g ⁻¹ᵁ f.complImage C = ⊤ ↔ fst ⁻¹' C = ∅ := by
  constructor
  · intro hg
    refine Set.eq_empty_of_forall_notMem fun p hp => ?_
    have hy : snd p ∈ g ⁻¹ᵁ f.complImage C := by
      rw [hg]
      trivial
    refine (f.mem_complImage C (g (snd p))).1 hy (fst p) hp ?_
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  · intro hC
    rw [eq_top_iff]
    intro y _
    refine (f.mem_complImage C (g y)).2 fun x hx hxy => ?_
    obtain ⟨p, hp, -⟩ := exists_preimage_of_isPullback h x y hxy
    have hmem : p ∈ fst ⁻¹' (C : Set X) := by
      rw [Set.mem_preimage, hp]
      exact hx
    rw [hC] at hmem
    exact hmem

/-- **Fibres contained in an open set** (Nitsure, arXiv:math/0504590v1, §6, p. 28,
Exercise A, topological part): let `f : X ⟶ Y` be universally closed, `i : X ⟶ W` a morphism and
`O ⊆ W` open. For a cartesian square with base change `fst : P ⟶ X` of `g : Y' ⟶ Y`, the
morphism `g` factors through the open `f.complImage (i ⁻¹ᵁ O).compl` of the points over which
the fibre of `f` maps into `O` if and only if `P ⟶ X ⟶ W` maps into `O`. -/
theorem preimage_complImage_compl_preimage_eq_top_iff_of_isPullback {P X Y Y' W : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [UniversallyClosed f]
    (h : IsPullback fst snd f g) (i : X ⟶ W) (O : W.Opens) :
    g ⁻¹ᵁ f.complImage (i ⁻¹ᵁ O).compl = ⊤ ↔ (fst ≫ i) ⁻¹ᵁ O = ⊤ := by
  rw [preimage_complImage_eq_top_iff_of_isPullback h]
  constructor
  · intro hC
    rw [eq_top_iff]
    intro p _
    by_contra hp
    have hmem : p ∈ fst ⁻¹' ((i ⁻¹ᵁ O).compl : Set X) := hp
    rw [hC] at hmem
    exact hmem
  · intro hO
    refine Set.eq_empty_of_forall_notMem fun p hp => ?_
    have hmem : p ∈ (fst ≫ i) ⁻¹ᵁ O := by
      rw [hO]
      trivial
    exact hp hmem

end Scheme

end AlgebraicGeometry
