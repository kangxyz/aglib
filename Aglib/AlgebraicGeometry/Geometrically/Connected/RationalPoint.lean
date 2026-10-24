/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# A connected scheme with a rational point is geometrically connected

Let `q : Y ⟶ Spec k` be a scheme over a field `k` with a rational point, that is a section
`o : Spec k ⟶ Y` with `o ≫ q = 𝟙 _`. If `Y` is connected, then `q` is geometrically connected
(`AlgebraicGeometry.Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section`).
This is the rational-point case of Stacks Project, Tag 04KV. No finiteness or separation
hypothesis on `Y` is needed.

The proof differs from the Stacks proof, which passes to a separable algebraic closure and applies
Stacks 056R and 0387. For an integral extension `K` of `k` (`connectedSpace_pullback_of_section`),
the projection `π : Y_K ⟶ Y` is universally open, as a base change of `Spec K ⟶ Spec k`, and every
morphism to the spectrum of a field is universally open, and universally closed, because `Spec K ⟶
Spec k` is integral. Its fibre over the rational point has at most one point
(`subsingleton_preimage_of_section`): the pullback of `π` along `o` is the pullback of `o ≫ q = 𝟙 _`
along `Spec K ⟶ Spec k`, which is `Spec K`. If `s` is a clopen subset of `Y_K` with `s` and its
complement nonempty, then `π '' s` and `π '' sᶜ` are nonempty clopen subsets of the connected `Y`,
so both contain the rational point, and the fibre over it meets both `s` and `sᶜ`, which is
impossible. For `K` the algebraic closure, Aglib's
`AlgebraicGeometry.Scheme.Geometrically.geometricallyConnected_of_connected_algebraicClosure`
concludes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set

namespace AlgebraicGeometry.Scheme.Geometrically

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- **The fibre of a field base change over a rational point is a single point**: for every
field extension `K` of `k` and every section `o` of `q`, the projection `Y_K ⟶ Y` has at most one
point over the rational point `o`. -/
theorem subsingleton_preimage_of_section (K : Type u) [Field K] [Algebra k K]
    (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _) :
    (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹'
      {o default}).Subsingleton := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIso (o ≫ q) := by rw [ho]; infer_instance
  have hP : Subsingleton (pullback o (pullback.fst q b) : Scheme.{u}) :=
    ((pullbackRightPullbackFstIso q b o).hom ≫ pullback.snd (o ≫ q) b).homeomorph.subsingleton
  intro a ha a' ha'
  have ha : o default = pullback.fst q b a := (mem_singleton_iff.mp ha).symm
  have ha' : o default = pullback.fst q b a' := (mem_singleton_iff.mp ha').symm
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback default a ha
  obtain ⟨z', -, hz'⟩ := Scheme.Pullback.exists_preimage_pullback default a' ha'
  rw [← hz, ← hz', Subsingleton.elim z z']

/-- **Connectedness over an integral extension**: if `Y` is connected and has a rational point,
then its base change to every integral (that is, algebraic) field extension of `k` is
connected. -/
theorem connectedSpace_pullback_of_section (K : Type u) [Field K] [Algebra k K]
    [Algebra.IsIntegral k K] [ConnectedSpace Y] (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _) :
    ConnectedSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIntegralHom b :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have hfib := subsingleton_preimage_of_section q K o ho
  rw [connectedSpace_iff_clopen]
  refine ⟨?_, fun s hs => ?_⟩
  · obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := b) (o default)
      default (Subsingleton.elim _ _)
    exact ⟨z⟩
  have himage : ∀ t : Set (pullback q b : Scheme.{u}), IsClopen t → t.Nonempty →
      o default ∈ pullback.fst q b '' t := fun t ht hne => by
    have hclopen : IsClopen (pullback.fst q b '' t) :=
      ⟨(pullback.fst q b).isClosedMap _ ht.1, (pullback.fst q b).isOpenMap _ ht.2⟩
    rcases isClopen_iff.mp hclopen with h | h
    · exact absurd h (hne.image _).ne_empty
    · exact h ▸ mem_univ _
  by_contra hs'
  rw [not_or] at hs'
  obtain ⟨a, has, ha⟩ := himage s hs (nonempty_iff_ne_empty.mpr hs'.1)
  obtain ⟨a', has', ha'⟩ := himage sᶜ hs.compl (nonempty_compl.mpr hs'.2)
  exact has' (hfib ha' ha ▸ has)

/-- **A connected scheme with a rational point is geometrically connected** (Stacks 04KV, the
case of a rational point). -/
theorem geometricallyConnected_of_connectedSpace_of_section [ConnectedSpace Y]
    (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _) : GeometricallyConnected q :=
  geometricallyConnected_of_connected_algebraicClosure k q
    (connectedSpace_pullback_of_section q (AlgebraicClosure k) o ho)

end AlgebraicGeometry.Scheme.Geometrically
