/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.IsSepClosed
public import Aglib.AlgebraicGeometry.Spec.PolynomialRationalPoint
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Rational points of smooth schemes over separably closed fields

The point is chosen inside the specified nonempty open of the original scheme.
Polynomial coordinates and the native etale point lifting theorem preserve
both the original field and the original structural morphism.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonempty smooth scheme over a separably closed field has a section over
that same field, with its original structural map. -/
theorem exists_section_of_smooth_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = 𝟙 _ := by
  let : Infinite K := IsSepClosed.infinite K
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hUt : U = ⊤ := by
    apply top_unique
    intro z _
    have hz : z = f x := Subsingleton.elim _ _
    exact hz ▸ e hx
  subst U
  let φ := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmooth := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp, RingHom.isStandardSmooth_respectsIso.cancel_left_isIso]
    exact hf
  obtain ⟨n, g, hg, hge⟩ := hφ.exists_etale_mvPolynomial
  let c : Spec Γ(X, V) ⟶ Spec (.of (MvPolynomial (Fin n) K)) :=
    Spec.map (CommRingCat.ofHom g)
  have : Etale c := HasRingHomProperty.Spec_iff.mpr hge
  have ht : c ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = hV.fromSpec ≫ f := by
    dsimp only [c]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)) = _
    rw [hg]
    change Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V e) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  obtain ⟨z, hz⟩ : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hx
  let W : (Spec (.of (MvPolynomial (Fin n) K))).Opens :=
    ⟨Set.range c, by simpa using c.isOpenMap Set.univ isOpen_univ⟩
  obtain ⟨a, ha⟩ := exists_eval_mem_open K (Fin n) W ⟨c z, ⟨z, rfl⟩⟩
  obtain ⟨y, hy⟩ := ha
  obtain ⟨l, hl, _⟩ := exists_fac_of_etale_of_isSepClosed c
    (Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))) y hy
  refine ⟨l ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← ht, ← Category.assoc, hl, ← Spec.map_comp]
  have heval : (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) ≫
      CommRingCat.ofHom (MvPolynomial.eval a) = 𝟙 (CommRingCat.of K) := by
    ext k
    simp
  rw [heval, Spec.map_id]

/-- A section of a smooth scheme over a separably closed field can be chosen
inside any specified nonempty open, without replacing the original field or
structural morphism. -/
theorem exists_section_mem_open_of_smooth_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (U : X.Opens)
    (hU : (U : Set X).Nonempty) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = 𝟙 _ ∧
      q (IsLocalRing.closedPoint K) ∈ U := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨q, hq⟩ := exists_section_of_smooth_of_isSepClosed K (U.ι ≫ f) ⟨x, hx⟩
  refine ⟨q ≫ U.ι, ?_, ?_⟩
  · simpa only [Category.assoc] using hq
  · exact (q (IsLocalRing.closedPoint K)).property

end AlgebraicGeometry.Scheme
