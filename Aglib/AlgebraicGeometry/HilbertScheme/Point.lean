/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianPoint
public import Aglib.AlgebraicGeometry.HilbertScheme.ResidueField

/-!
# Grassmannian points of the Hilbert functor over affine pieces

For a point `Z` of `Hilb^Φ(T)` (`IsHilbertFamily ι Φ g Z`) and a morphism `x : Spec B ⟶ T` from
the spectrum of a Noetherian ring, `IsHilbertFamily.grassmannianPoint` is the Grassmannian point
`grassmannianPoint` of the pullback `Z_x ⊆ P^n_B` in degree `r ≥ hilbertRegularityBound n Φ`: the
kernel of `H^0(P^n_B, 𝒪(r)) ⟶ H^0(P^n_B, 𝒪_{Z_x}(r))`, with finite projective quotient of rank
`Φ(r)` (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5,
pp. 25–26). Over an affine test scheme `T = Spec B` (`x = 𝟙`), two points with the same
Grassmannian point are equal (`IsHilbertFamily.eq_of_grassmannianPoint_eq`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

/-- **The Grassmannian point of a point of the Hilbert functor over an affine piece** (Nitsure,
arXiv:math/0504590v1, §5, p. 26): for `x : Spec B ⟶ T` with `B` Noetherian and a natural number
`r ≥ hilbertRegularityBound n Φ`, the point `[H^0(𝒪(r)) ↠ H^0(𝒪_{Z_x}(r))]` of the Grassmannian of
rank-`Φ(r)` quotients of `H^0(P^n_B, 𝒪(r))`. -/
def IsHilbertFamily.grassmannianPoint (hZ : IsHilbertFamily ι Φ g Z) {B : Type u} [CommRing B]
    [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    Module.Grassmannian B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (unitTwist (B := B) ι r)) 0) ⌊Φ.eval (r : ℚ)⌋₊ :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.grassmannianPoint ι n e (Z.comap (pointMap ι g x))
    (hZ.primeFiber_comap_pointMap ι x) r hr

include e in
/-- **Direct images of the structure module over an affine piece** (Nitsure,
arXiv:math/0504590v1, §5, p. 25): for a point `Z` of `Hilb^Φ(T)`, `x : Spec B ⟶ T` with `B`
Noetherian and `r ≥ hilbertRegularityBound n Φ`: `H^0(P^n_B, 𝒪_{Z_x}(r))` is projective,
its cohomology commutes with every base change, and
`0 → H^0(I_{Z_x}(r)) → H^0(𝒪(r)) → H^0(𝒪_{Z_x}(r)) → 0` is exact. -/
theorem IsHilbertFamily.projective_moduleCohomology_quotientTwist (hZ : IsHilbertFamily ι Φ g Z)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    (letI := h0Module ι (quotientTwist ι (Z.comap (pointMap ι g x)) r);
      Module.Projective B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
        (quotientTwist ι (Z.comap (pointMap ι g x)) r)) 0)) ∧
    (∀ (q : ℕ) {C : Type u} [CommRing C] (σ : B →+* C),
      IsIso (moduleCohomologyBaseChangeMap (toSpec B ι) σ
        (quotientTwist ι (Z.comap (pointMap ι g x)) r) q)) ∧
    Function.Surjective (restrictionH0 ι (Z.comap (pointMap ι g x)) r) :=
  haveI := hZ.flat_comap_pointMap ι x
  ⟨ProjectiveSpace.projective_moduleCohomology_quotientTwist ι n e _
      (hZ.primeFiber_comap_pointMap ι x) r hr,
    fun q _ _ σ => ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_quotientTwist ι n e _
      (hZ.primeFiber_comap_pointMap ι x) r hr q σ,
    (ProjectiveSpace.exact_moduleCohomology_twistedShortComplex ι n e _
      (hZ.primeFiber_comap_pointMap ι x) r hr).2.2⟩

include e in
/-- **Injectivity of the Grassmannian point over an affine test scheme** (Nitsure,
arXiv:math/0504590v1, §5, p. 26): two points of `Hilb^Φ(Spec B)`, `B` Noetherian, with the same
Grassmannian point in a degree `r ≥ hilbertRegularityBound n Φ`, are equal. -/
theorem IsHilbertFamily.eq_of_grassmannianPoint_eq {B : Type u} [CommRing B]
    [IsNoetherianRing B] {g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)}
    {Z Z' : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z)
    (hZ' : IsHilbertFamily ι Φ g Z') (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    hZ.grassmannianPoint ι n e (𝟙 _) r hr = hZ'.grassmannianPoint ι n e (𝟙 _) r hr → Z = Z' := by
  intro h
  have := hZ.flat_comap_pointMap ι (𝟙 _)
  have := hZ'.flat_comap_pointMap ι (𝟙 _)
  have hc := ProjectiveSpace.eq_of_grassmannianPoint_eq ι n e _ _
    (hZ.primeFiber_comap_pointMap ι (𝟙 _)) (hZ'.primeFiber_comap_pointMap ι (𝟙 _)) r hr h
  have hinv (W : (pullback (toSpec A ι) g).IdealSheafData) :
      (W.comap (pointMap ι g (𝟙 _))).comap (inv (pointMap ι g (𝟙 _))) = W := by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [← hinv Z, ← hinv Z', hc]

end ProjectiveSpace

end AlgebraicGeometry
