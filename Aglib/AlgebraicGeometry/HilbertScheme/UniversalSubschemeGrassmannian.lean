/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubscheme
public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianTransport
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Reindex
public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# The universal closed subscheme over the Grassmannian

Let `G = Gr(k, A^N)` be the Grassmannian of rank-`k` locally free quotients of `𝒪^N`
(`Grassmannian.schemeOver (CommRingCat.of A) k N`, a scheme over `Spec A`), and let
`e : I ≃ ULift (Fin N)` be a bijection, so that the universal kernel `K_univ` is a subsheaf of
`𝒪_G^I` (`Grassmannian.universalKernelιFree`). For a family `s : I → A[x]_r` of homogeneous
polynomials of degree `r`, the **universal closed subscheme** is
`Z_univ = Z(K_univ) ⊆ P^n_A ×_{Spec A} G` (`universalEvaluationIdeal`), the closed subscheme cut
out by the image of `π^* K_univ(-r) ⟶ 𝒪` (`evaluationIdeal`).

* `universalEvaluationIdeal_comap`: for every `φ : T ⟶ G` over `Spec A`, the pullback of
  `Z_univ` along `P^n_φ = baseChangeMap` is `Z(φ^* K_univ)`, by base change of `Z(K)`
  (`evaluationIdeal_comap_baseChangeMap`).
* `universalEvaluationIdeal_comap_classifyingMap`: for a rank-`k` locally free quotient
  `q : 𝒪_T^I ⟶ Q` with classifying map `φ`, the pullback of `Z_univ` along `P^n_φ` is
  `Z(ker q)`, since `φ^* K_univ = ker q` inside `𝒪_T^I`
  (`Grassmannian.pullbackUniversalKernelIsoOfFree_hom_ι`).
* `evaluationIdeal_kernel_comap_baseChangeMap`: for a rank-`k` locally free quotient
  `q : 𝒪_T^I ⟶ Q` and `f : T' ⟶ T`, the pullback of `Z(ker q)` is `Z(ker f^* q)`.
* For the Hilbert scheme, `I` is the type of monomials of degree `r` in `n + 1` variables,
  `N = (n + r).choose r` (`monomialsEquiv`), and `s` the monomial family (`monomialFamily`):
  `universalHilbertSubscheme` and `universalHilbertSubscheme_comap_classifyingMap`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5,
pp. 26–27, "Embedding Quot into Grassmannian" and "Use of Flattening Stratification": for
`G = Grass(W ⊗ Sym^r V, Φ(r))` with universal kernel `v : K → p_G^* E`, and `φ : Y → G`,
`K_Y = ker(f_Y) = φ^* ker(f)`; since pullback is right exact, the cokernel of
`h_Y : π_Y^* K_Y → E_Y(r)` is the pullback of the universal one, so the closed subscheme over `Y`
is the pullback of the universal closed subscheme. Encoded subset: `E = 𝒪`, `W = 𝒪`,
`V = 𝒪^{n+1}` over `Spec A`; all `T` over `Spec A`, all `r` and `k`; no Noetherian or flatness
hypothesis. The Grassmannian classification uses the premise `BaseChangeMkQFormula`, supplied by
the instance of `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.Grassmannian AlgebraicGeometry.Grassmannian.LocallyFreeQuotient

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A]

variable (r k N : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r)
  (eI : I ≃ ULift.{u} (Fin N))

include eI in
/-- **Base change of the subscheme of a kernel** (Nitsure, arXiv:math/0504590v1, §5, p. 26,
`K_Y = ker(f_Y) = φ^* ker(f)`): for a rank-`k` locally free quotient `q : 𝒪_T^I ⟶ Q` and
`f : T' ⟶ T` over `Spec A`, the pullback of `Z(ker q)` along `X_{T'} ⟶ X_T` is `Z(ker f^* q)`,
with `ker f^* q ⊆ f^* 𝒪_T^I ≅ 𝒪_{T'}^I`. The kernel of `q` is quasi-coherent, being finite
locally free through `eI` (`LocallyFreeQuotient.ofFreeKernelIso`), and its formation commutes
with every pullback (`Scheme.Modules.pullbackKernelIso`). -/
theorem evaluationIdeal_kernel_comap_baseChangeMap {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') {Q : T.Modules} (q : SheafOfModules.free I ⟶ Q) [Epi q]
    (hQ : Scheme.Modules.SheafHasRank Q k) :
    (evaluationIdeal ι g r s (Limits.kernel.ι q)).comap (baseChangeMap ι g g' f h) =
      evaluationIdeal ι g' r s (Limits.kernel.ι ((Scheme.Modules.pullback f).map q) ≫
        (Scheme.Modules.pullbackFreeIso f I).hom) := by
  have : (Limits.kernel q).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (ofFreeKernelIso eI q hQ)
      inferInstance
  have := hQ.isFiniteLocallyFree
  rw [evaluationIdeal_comap_baseChangeMap ι g' f h r s (Limits.kernel.ι q)]
  exact evaluationIdeal_eq_of_iso ι g' r s (Scheme.Modules.pullbackKernelIso f q) _ _
    (Scheme.Modules.pullbackKernelIso_hom_ι_assoc f q _)

/-- **The universal closed subscheme** `Z_univ ⊆ P^n_A ×_{Spec A} G` over the Grassmannian
`G = Gr(k, A^N)` of rank-`k` quotients of `𝒪^N`: `Z(K_univ)` for the universal kernel
`K_univ ⊆ 𝒪_G^I` (Nitsure, arXiv:math/0504590v1, §5, p. 26). -/
def universalEvaluationIdeal :
    (pullback (toSpec A ι) (schemeOver (CommRingCat.of A) k N).hom).IdealSheafData :=
  evaluationIdeal ι (schemeOver (CommRingCat.of A) k N).hom r s
    (universalKernelιFree (CommRingCat.of A) k N eI)

/-- **Base change of the universal subscheme**: for every `φ : T ⟶ G` over `Spec A`, the pullback
of `Z_univ` along `P^n_φ` is `Z(φ^* K_univ)`, with `φ^* K_univ ⊆ 𝒪_T^I` through the pulled-back
inclusion. -/
theorem universalEvaluationIdeal_comap {T : Over (Spec (CommRingCat.of A))}
    (φ : T ⟶ schemeOver (CommRingCat.of A) k N) :
    (universalEvaluationIdeal ι r k N s eI).comap
        (baseChangeMap ι (schemeOver (CommRingCat.of A) k N).hom T.hom φ.left (Over.w φ)) =
      evaluationIdeal ι T.hom r s
        ((Scheme.Modules.pullback φ.left).map (universalKernelιFree (CommRingCat.of A) k N eI) ≫
          (Scheme.Modules.pullbackFreeIso φ.left I).hom) :=
  evaluationIdeal_comap_baseChangeMap ι T.hom φ.left (Over.w φ) r s _

/-- **The universal subscheme pulls back to the subscheme of a quotient** (Nitsure,
arXiv:math/0504590v1, §5, p. 26, property (F), `K_Y = φ^* ker(f)`): for a rank-`k` locally free
quotient `q : 𝒪_T^I ⟶ Q` on a scheme `T` over `Spec A`, with classifying map `φ` to the
Grassmannian, the pullback of `Z_univ` along `P^n_φ` is `Z(ker q)`. -/
theorem universalEvaluationIdeal_comap_classifyingMap {T : Over (Spec (CommRingCat.of A))}
    {Q : T.left.Modules} (q : SheafOfModules.free I ⟶ Q) [Epi q]
    (hQ : Scheme.Modules.SheafHasRank Q k) :
    (universalEvaluationIdeal ι r k N s eI).comap
        (baseChangeMap ι (schemeOver (CommRingCat.of A) k N).hom T.hom
          (classifyingMap (ofFree eI q hQ)).left (Over.w (classifyingMap (ofFree eI q hQ)))) =
      evaluationIdeal ι T.hom r s (Limits.kernel.ι q) := by
  rw [universalEvaluationIdeal_comap]
  exact evaluationIdeal_eq_of_iso ι T.hom r s
    (pullbackUniversalKernelIsoOfFree eI q hQ ≪≫ ofFreeKernelIso eI q hQ) _ _
    (pullbackUniversalKernelIsoOfFree_hom_ι eI q hQ)

/-- **The universal subscheme of the Hilbert scheme construction**: `Z_univ` for the monomials
of degree `r` in `n + 1` variables, over the Grassmannian of rank-`k` quotients of `𝒪^N`,
`N = (n + r).choose r`. -/
def universalHilbertSubscheme (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (pullback (toSpec A ι)
      (schemeOver (CommRingCat.of A) k ((n + r).choose r)).hom).IdealSheafData :=
  universalEvaluationIdeal ι r k ((n + r).choose r) (monomialFamily (A := A) ι r)
    (monomialsEquiv ι n e r)

/-- **The universal subscheme pulls back to `Z(ker q)`** for the Hilbert scheme construction
(Nitsure, arXiv:math/0504590v1, §5, pp. 26–27): for a rank-`k` locally free quotient `q` of the
free sheaf on the monomials of degree `r`, with classifying map `φ`, the pullback of the
universal subscheme along `P^n_φ` is the subscheme cut out by `ker q` under evaluation of the
monomials. -/
theorem universalHilbertSubscheme_comap_classifyingMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    {T : Over (Spec (CommRingCat.of A))} {Q : T.left.Modules}
    (q : SheafOfModules.free {a : ι →₀ ℕ // a.degree = r} ⟶ Q) [Epi q]
    (hQ : Scheme.Modules.SheafHasRank Q k) :
    (universalHilbertSubscheme ι r k n e).comap
        (baseChangeMap ι (schemeOver (CommRingCat.of A) k ((n + r).choose r)).hom T.hom
          (classifyingMap (ofFree (monomialsEquiv ι n e r) q hQ)).left
          (Over.w (classifyingMap (ofFree (monomialsEquiv ι n e r) q hQ)))) =
      evaluationIdeal ι T.hom r (monomialFamily (A := A) ι r) (Limits.kernel.ι q) :=
  universalEvaluationIdeal_comap_classifyingMap ι r k _ _ _ q hQ

end AlgebraicGeometry.ProjectiveSpace
