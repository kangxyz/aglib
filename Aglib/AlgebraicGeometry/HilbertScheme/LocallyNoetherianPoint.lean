/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.DirectImageSheafEpi
public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianTransport
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Reindex
public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# The Grassmannian point of a Hilbert family over a locally Noetherian base

Let `T` be a locally Noetherian scheme over `Spec A`, `Z` a point of `Hilb^Φ(T)`,
`ι ≃ Fin (n + 1)` and `r ≥ hilbertRegularityBound n Φ` a natural number, and
`N = (n + r).choose r` the number of monomials of degree `r` (`monomialsEquiv`,
`ProjectiveSpace/Monomials`). The evaluation map
`𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` is an epimorphism onto a finite locally free sheaf of constant rank
`⌊Φ(r)⌋₊` (`IsHilbertFamily.epi_directImageQuotientMap`,
`IsHilbertFamily.sheafHasRank_directImageSheaf`), so it is a rank-`⌊Φ(r)⌋₊` locally free quotient
of `𝒪_T^N` (`IsHilbertFamily.grassmannianQuotient`, through `LocallyFreeQuotient.ofFree`). Its
classifying map is the **Grassmannian point** `IsHilbertFamily.grassmannianMap : T ⟶ Gr` over
`Spec A` of Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26:
`Z ↦ [π_{T*} E_T(r) → π_{T*} F(r)] ∈ Grass(Sym^r, Φ(r))(T)`.

**Naturality.** For a morphism `f : T' ⟶ T` over `Spec A` of locally Noetherian schemes, the
quotient of the pullback `Z.comap b` (`b = baseChangeMap ι g g' f h`) is isomorphic under
`𝒪_{T'}^N` to the pullback of the quotient of `Z`
(`IsHilbertFamily.nonempty_isoUnder_pullback_grassmannianQuotient`): the isomorphism is the
base-change mate of `isPullback_baseChangeMap`, invertible by (*) of p. 25, and the evaluation maps
correspond by `directImageQuotientMap_baseChange`. Hence the points are natural
(`IsHilbertFamily.grassmannianMap_comp`).

The route is sheaf-level: no affine quotients are glued; the overlap compatibility is the
naturality of the canonical base-change mate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))

variable {A : Type u} [CommRing A] {Φ : ℚ[X]} {T : Scheme.{u}} [IsLocallyNoetherian T]
  {g : T ⟶ Spec (CommRingCat.of A)} {Z : (pullback (toSpec A ι) g).IdealSheafData}

/-- **The Grassmannian quotient of a Hilbert family** (Nitsure, arXiv:math/0504590v1, §5, p. 26):
for a locally Noetherian `T`, a point `Z` of `Hilb^Φ(T)` and a natural number
`r ≥ hilbertRegularityBound n Φ`, the evaluation map `𝒪_T^N ⟶ π_* 𝒪_Z(r)`, a rank-`⌊Φ(r)⌋₊`
locally free quotient of `𝒪_T^N`. -/
def IsHilbertFamily.grassmannianQuotient (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Grassmannian.LocallyFreeQuotient T ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r) :=
  haveI := hZ.epi_directImageQuotientMap ι n e r hr
  Grassmannian.LocallyFreeQuotient.ofFree (monomialsEquiv ι n e r)
    (directImageQuotientMap ι g Z r) (hZ.sheafHasRank_directImageSheaf ι n e r hr)

/-- **The Grassmannian point of a Hilbert family** (Nitsure, arXiv:math/0504590v1, §5, p. 26):
the classifying map over `Spec A` of `grassmannianQuotient`, from `T` to the Grassmannian of
rank-`⌊Φ(r)⌋₊` quotients of `𝒪^N`, `N = (n + r).choose r`. -/
def IsHilbertFamily.grassmannianMap (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Over.mk g ⟶ Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r) :=
  Grassmannian.classifyingMap (T := Over.mk g) (hZ.grassmannianQuotient ι n e r hr)

theorem IsHilbertFamily.grassmannianMap_def (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    hZ.grassmannianMap ι n e r hr =
      Grassmannian.classifyingMap (T := Over.mk g) (hZ.grassmannianQuotient ι n e r hr) :=
  rfl

variable {T' : Scheme.{u}} [IsLocallyNoetherian T'] (g' : T' ⟶ Spec (CommRingCat.of A))
  (f : T' ⟶ T) (h : f ≫ g = g')

include e in
/-- **The quotient is compatible with base change**: for `f : T' ⟶ T` over `Spec A` of locally
Noetherian schemes, the pullback along `f` of the quotient of `Z` is isomorphic under `𝒪_{T'}^N` to
the quotient of `Z.comap (baseChangeMap ι g g' f h)`. -/
theorem IsHilbertFamily.nonempty_isoUnder_pullback_grassmannianQuotient
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Nonempty (Grassmannian.LocallyFreeQuotient.IsoUnder
      ((hZ.grassmannianQuotient ι n e r hr).pullback f)
      ((hZ.comap ι f h).grassmannianQuotient ι n e r hr)) := by
  have := hZ.isIso_cartesianBaseChangeMap_baseChangeMap ι n e r hr g' f h
  have := hZ.epi_directImageQuotientMap ι n e r hr
  have := (hZ.comap ι f h).epi_directImageQuotientMap ι n e r hr
  unfold IsHilbertFamily.grassmannianQuotient
  rw [Grassmannian.LocallyFreeQuotient.ofFree_pullback]
  have := Grassmannian.LocallyFreeQuotient.epi_pullbackFreeIso_inv_comp f
    (directImageQuotientMap ι g Z r)
  exact ⟨Grassmannian.LocallyFreeQuotient.isoUnderOfFree _ _ _
    (asIso ((cartesianBaseChangeMap (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
      (pullback.snd (toSpec A ι) g) f (isPullback_baseChangeMap ι g g' f h)).app
        (familyQuotientTwist ι g Z r)) ≪≫
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).mapIso
        (familyQuotientTwistBaseChangeIso ι g g' f h Z r))
    (directImageQuotientMap_baseChange ι g g' f h Z r)⟩

include e in
/-- **The Grassmannian point is natural** (Nitsure, arXiv:math/0504590v1, §5, p. 26): for a
morphism `f : T' ⟶ T` over `Spec A` of locally Noetherian schemes, the point of the pullback of
`Z` is `f` followed by the point of `Z`. -/
theorem IsHilbertFamily.grassmannianMap_comp (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Over.homMk f h ≫ hZ.grassmannianMap ι n e r hr =
      (hZ.comap ι f h).grassmannianMap ι n e r hr := by
  obtain ⟨i⟩ := hZ.nonempty_isoUnder_pullback_grassmannianQuotient ι n e g' f h r hr
  rw [IsHilbertFamily.grassmannianMap_def, IsHilbertFamily.grassmannianMap_def,
    ← Grassmannian.classifyingMap_pullback]
  exact Grassmannian.classifyingMap_eq_of_isoUnder i

end ProjectiveSpace

end AlgebraicGeometry
