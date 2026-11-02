/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.LocalCoordinates
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Smooth coordinates over the original field

A smooth relative-dimension chart over a field has the entire original base
as its target open. The canonical global-sections comparison then supplies
coordinates over that same field, retaining the original structural map.
No replacement field or new chart structure is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SmoothLocalCoordinates

universe u

/-- Around each original point of a smooth scheme of relative dimension `n`
over a field, an actual affine open has etale coordinates over the original
field. The original structure map is retained as an equality of morphisms. -/
theorem exists_field_coordinates
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ γ : MvPolynomial (Fin n) K →+* Γ(X, U), γ.Etale ∧
        Spec.map (CommRingCat.ofHom (γ.comp MvPolynomial.C)) = hU.fromSpec ≫ f := by
  obtain ⟨c, hc⟩ := exists_chart_of_smoothOfRelativeDimension (f := f) n x
  rcases c with ⟨V, hV, U, hU, hx, hm, m, g, hg, he⟩
  change m = n at hc
  subst m
  have hVtop : V = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    rw [hy]
    exact hm hx
  subst V
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let γ : MvPolynomial (Fin n) K →+* Γ(X, U) := g.comp (MvPolynomial.map e.toRingHom)
  have hγ : γ.comp MvPolynomial.C = (f.appLE ⊤ U hm).hom.comp e.toRingHom := by
    ext a
    change g (MvPolynomial.map e.toRingHom (MvPolynomial.C a)) =
      (f.appLE ⊤ U hm).hom (e a)
    rw [MvPolynomial.map_C]
    exact DFunLike.congr_fun hg (e a)
  refine ⟨U, hU, hx, γ, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv (Fin n) e).bijective) he
  · rw [hγ]
    change Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U hm) = hU.fromSpec ≫ f
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU hm

end AlgebraicGeometry.Scheme.SmoothLocalCoordinates
