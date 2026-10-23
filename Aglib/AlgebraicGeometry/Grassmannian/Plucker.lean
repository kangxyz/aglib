/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.FunctorOfPoints
public import Aglib.RingTheory.Grassmannian.LinearEquiv
public import Aglib.RingTheory.Grassmannian.PluckerInjective

/-!
# The Plücker morphism of the Grassmannian

Let `R` be a commutative ring and `N = n.choose k`. The wedge basis `e_S`, `S` a `k`-subset of
`Fin n`, identifies `⋀[R]^k (Fin n → R)` with `Fin N → R` (`exteriorPowerEquivFin`, with the
`k`-subsets ordered by `pluckerIndexEquiv`). Composing Mathlib's Grassmannian points with the
Plücker transformation `Module.Grassmannian.pluckerNatTrans` and this identification gives a natural
transformation `pluckerFinNatTrans R k n` from Mathlib's functor of rank-`k` quotients of `R^n` to
that of rank-one quotients of `R^N`. Through the functor of points of the glued Grassmannians
(`Grassmannian.homEquivNatTrans`) it is the **Plücker morphism**

* `Grassmannian.plucker R k n : schemeOver R k n ⟶ schemeOver R 1 N` over `Spec R`, characterized
  by `homEquivNatTrans_comp_plucker` and, on affine points, by `representableEquiv_comp_plucker`;
* `Grassmannian.pluckerProjective R k n : schemeOver R k n ⟶ ProjectiveSpace.schemeOver R ι`, its
  composite with `ProjectiveSpace.grassmannianOverIso`, where the homogeneous coordinates
  `ι = ULift (Set.powersetCard (Fin n) k)` are the Plücker coordinates `p_S`; on affine points it
  is again the Plücker transformation (`representableEquiv_comp_pluckerProjective`).

The Plücker transformation is injective on points (`pluckerFinNatTrans_app_injective`, from
`Module.Grassmannian.plucker_injective`), so the Plücker morphisms are monomorphisms
(`mono_plucker`, `mono_pluckerProjective`; the reduction is `mono_plucker_of_injective`). The
closed-immersion property is not proved here.

Sources: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 5
(item (2)) and p. 9 ("Projective embedding": the Plücker sections `σ_I` with
`σ_I|_{U^J} = P^J_I`); there the closed embedding is deduced from properness. Stacks,
Section 27.22 (Tag 089R) has no Plücker morphism; projective space is the Grassmannian of rank-one
quotients by Stacks, Tag 089V (Lemma 27.22.3), here through `ProjectiveSpace.grassmannianOverIso`.
The named premise `BaseChangeMkQFormula` is supplied by the instance in
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`, imported through the projective-space
comparison and `MapCriterion`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) (k n : ℕ)

/-- The `k`-subsets of `Fin n`, numbered by `Fin (n.choose k)`. -/
def pluckerIndexEquiv : Set.powersetCard (Fin n) k ≃ Fin (n.choose k) :=
  Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin])

/-- **Plücker coordinates**: `⋀[R]^k R^n ≃ R^{n.choose k}`, the coordinates in the wedge basis
`e_S = e_{s₁} ∧ ⋯ ∧ e_{s_k}` (`s₁ < ⋯ < s_k` the elements of the `k`-subset `S`), with the
subsets numbered by `pluckerIndexEquiv`. -/
def exteriorPowerEquivFin : ⋀[R]^k (Fin n → R) ≃ₗ[R] (Fin (n.choose k) → R) :=
  ((Pi.basisFun R (Fin n)).exteriorPower k).equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft R R (pluckerIndexEquiv k n).symm

/-- The Plücker transformation with values in Mathlib's functor of rank-one quotients of
`R^{n.choose k}`: `N ↦ ker (A ⊗ ⋀^k R^n → ⋀^k ((A ⊗ R^n) ⧸ N))`, transported along
`exteriorPowerEquivFin`. -/
def pluckerFinNatTrans :
    Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k ⟶
      Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin (n.choose k) → R) 1 :=
  Module.Grassmannian.pluckerNatTrans R (Fin n → R) k ≫
    (Module.Grassmannian.functorIsoOfLinearEquiv 1 (exteriorPowerEquivFin R k n)).hom

/-- **The Plücker morphism** `Gr(R^n, k) ⟶ Gr(R^{n.choose k}, 1)` over `Spec R`: the map whose
functor of points is `pluckerFinNatTrans`. -/
def plucker : schemeOver R k n ⟶ schemeOver R 1 (n.choose k) :=
  (homEquivNatTrans 1 (n.choose k) (schemeOver R k n)).symm
    (homEquivNatTrans k n (schemeOver R k n) (𝟙 _) ≫ pluckerFinNatTrans R k n)

/-- The functor of points of `g ≫ plucker R k n` is that of `g` followed by the Plücker
transformation. -/
theorem homEquivNatTrans_comp_plucker {T : Over (Spec R)} (g : T ⟶ schemeOver R k n) :
    homEquivNatTrans 1 (n.choose k) T (g ≫ plucker R k n) =
      homEquivNatTrans k n T g ≫ pluckerFinNatTrans R k n := by
  rw [homEquivNatTrans_comp, plucker, Equiv.apply_symm_apply, ← Category.assoc,
    ← homEquivNatTrans_comp, Category.comp_id]

/-- On affine points, the Plücker morphism is the Plücker transformation: for
`g : Spec A ⟶ Gr` with point `N`, the point of `g ≫ plucker R k n` is the Plücker point of `N`. -/
theorem representableEquiv_comp_plucker (A : CommAlgCat.{u} R)
    (g : affineOver A ⟶ schemeOver R k n) :
    representableEquiv R 1 (n.choose k) A (g ≫ plucker R k n) =
      (pluckerFinNatTrans R k n).app A (representableEquiv R k n A g) := by
  have h : representableEquiv R 1 (n.choose k) A (𝟙 _ ≫ g ≫ plucker R k n) =
      (pluckerFinNatTrans R k n).app A (representableEquiv R k n A (𝟙 _ ≫ g)) :=
    congrArg (fun α => α.app A (𝟙 (affineOver A))) (homEquivNatTrans_comp_plucker R k n g)
  rwa [Category.id_comp, Category.id_comp] at h

/-- **The Plücker morphism into projective space** `P(⋀^k R^n)`, whose homogeneous coordinates are
indexed by the `k`-subsets of `Fin n` (Plücker coordinates). -/
def pluckerProjective :
    schemeOver R k n ⟶ ProjectiveSpace.schemeOver R (ULift.{u} (Set.powersetCard (Fin n) k)) :=
  plucker R k n ≫
    (ProjectiveSpace.grassmannianOverIso R (Equiv.ulift.trans (pluckerIndexEquiv k n))).hom

/-- On affine points, the Plücker morphism into projective space is the Plücker transformation,
through `ProjectiveSpace.representableEquiv`. -/
theorem representableEquiv_comp_pluckerProjective (A : CommAlgCat.{u} R)
    (g : affineOver A ⟶ schemeOver R k n) :
    ProjectiveSpace.representableEquiv R (Equiv.ulift.trans (pluckerIndexEquiv k n)) A
        (g ≫ pluckerProjective R k n) =
      (pluckerFinNatTrans R k n).app A (representableEquiv R k n A g) := by
  rw [← representableEquiv_comp_plucker]
  change representableEquiv R 1 (n.choose k) A
      ((g ≫ plucker R k n ≫ (ProjectiveSpace.grassmannianOverIso R _).hom) ≫
        (ProjectiveSpace.grassmannianOverIso R _).inv) = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The Plücker morphism is a monomorphism if the Plücker transformation is injective on
points**: maps into the Grassmannians are natural transformations of functors of points
(`homEquivNatTrans`). -/
theorem mono_plucker_of_injective
    (h : ∀ A : CommAlgCat.{u} R, Function.Injective ((pluckerFinNatTrans R k n).app A)) :
    Mono (plucker R k n) := by
  refine ⟨fun {T} a b hab => (homEquivNatTrans k n T).injective ?_⟩
  have h' := congrArg (homEquivNatTrans 1 (n.choose k) T) hab
  rw [homEquivNatTrans_comp_plucker, homEquivNatTrans_comp_plucker] at h'
  refine NatTrans.ext (funext fun A ↦ ?_)
  ext v
  have e : (pluckerFinNatTrans R k n).app A ((homEquivNatTrans k n T a).app A v) =
      (pluckerFinNatTrans R k n).app A ((homEquivNatTrans k n T b).app A v) :=
    congrArg (fun α => α.app A v) h'
  exact h A e

/-- The Plücker transformation is injective on points: a point of the Grassmannian is determined
by its Plücker point (`Module.Grassmannian.plucker_injective`), and the transport along
`exteriorPowerEquivFin` is injective. -/
theorem pluckerFinNatTrans_app_injective (A : CommAlgCat.{u} R) :
    Function.Injective ((pluckerFinNatTrans R k n).app A) := by
  intro N₁ N₂ h
  have h' : Module.Grassmannian.ofLinearEquiv
        ((exteriorPowerEquivFin R k n).baseChange R A _ _) (Module.Grassmannian.plucker N₁) =
      Module.Grassmannian.ofLinearEquiv
        ((exteriorPowerEquivFin R k n).baseChange R A _ _) (Module.Grassmannian.plucker N₂) :=
    h
  exact Module.Grassmannian.plucker_injective
    (Module.Grassmannian.ofLinearEquiv_injective _ h')

/-- **The Plücker morphism is a monomorphism.** -/
instance mono_plucker : Mono (plucker R k n) :=
  mono_plucker_of_injective R k n (pluckerFinNatTrans_app_injective R k n)

/-- The Plücker morphism into projective space is a monomorphism. -/
instance mono_pluckerProjective : Mono (pluckerProjective R k n) :=
  mono_comp _ _

end AlgebraicGeometry.Grassmannian
