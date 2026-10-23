/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianFunctor
public import Aglib.AlgebraicGeometry.Cohomology.Modules.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.PolynomialSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.HomogeneousSections
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Naturality of the Grassmannian point of a Hilbert family

For an `A`-algebra map `f : B → B'` of Noetherian rings and a point `Z` of `Hilb^Φ(Spec B)`,
Mathlib's base change along `f` of the point `IsHilbertFamily.grassmannianFunctorPoint` of `Z`
is the point of the pullback of `Z` to `Spec B'`
(`IsHilbertFamily.map_grassmannianFunctorPoint`; Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, §5, p. 26). Consequently the points form a natural
transformation from the Hilbert functor on Noetherian affine test schemes,
`B ↦ Hilb^Φ(Spec B)`, to Mathlib's Grassmannian functor `B ↦ G(⌊Φ(r)⌋₊, B ⊗[A] A[x]_r; B)`
(`noetherianAffineGrassmannianNatTrans`), for every `r ≥ hilbertRegularityBound n Φ`.

By `Module.Grassmannian.map_eq_of_forall` it suffices that `f ⊗ id` maps the kernel of
`B ⊗[A] A[x]_r ≅ H^0(𝒪(r) ⊗ 𝒪) ⟶ H^0(𝒪_W(r))` into the kernel at `B'`, where
`W ⊆ P^n_B` is the restriction of `Z` and `W' = W.comap (map f ι)` that of the pullback
(`comap_baseChangeMap_comap_eq`). This is `restrictionH0_unitTwistH0Equiv_rTensor_eq_zero`,
proved on global sections over `⊤` through the unit `η` of the pullback-pushforward adjunction
along `π = map f ι : P^n_{B'} ⟶ P^n_B`:

* `homogeneousSubmoduleBaseChangeEquiv_rTensor` (`RingTheory/MvPolynomial/HomogeneousBaseChange`):
  under `B ⊗[A] A[x]_r ≃ B[x]_r`, `f ⊗ id` is the coefficient map `B[x]_r → B'[x]_r`;
* `unitTwistPullbackHom_unit_homogeneousSection`: the comparison
  `unitTwistPullbackHom : π^*(𝒪(r) ⊗ 𝒪) ⟶ 𝒪(r) ⊗ 𝒪` sends `η` of the section of a polynomial `p`
  to the section of `f(p)` (`twistingPullbackIso_hom_unit_homogeneousSection`,
  `twistingTensorPullbackIso_rightUnitor`);
* `restriction_unitTwistPullbackHom_unit_eq_zero`: `η` and the comparisons commute with the
  restriction to the subscheme (`twistingTensorPullbackIso_hom_naturality` and
  `pullback_map_toQuotientModule_quotientModulePullbackIso_hom`, with no flatness of `W`), so a
  section vanishing on `W` pulls back to one vanishing on `W'`;
* `equiv₀_unitTwistH0Equiv`, with `equiv₀_moduleCohomologyMapOfHom`
  (`Cohomology/Modules/DegreeZero`): the passage between `H^0` and sections over `⊤`.

The core statements are stated at variable data on `P^n_B` (`map_ofLinearEquiv_grassmannianPoint`)
and instantiated once at the fiber products over `Spec A`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped Polynomial TensorProduct

universe u

namespace AlgebraicGeometry

/-- `Spec` of an algebra map, as the underlying morphism of `algSpec`. -/
theorem algSpec_map_left_eq {R : Type u} [CommRing R] {B B' : CommAlgCat.{u} R} (φ : B ⟶ B') :
    ((algSpec (CommRingCat.of R)).map φ.op).left =
      Spec.map (CommRingCat.ofHom (φ.hom : B →+* B')) :=
  rfl

namespace Scheme.Modules

/-- Naturality of the unit of the pullback-pushforward adjunction on global sections. -/
private theorem pullbackPushforward_unit_app_top_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) (s : Γ(M, ⊤)) :
    ((pullbackPushforwardAdjunction f).unit.app N).val.app (op ⊤) (g.val.app (op ⊤) s) =
      ((Scheme.Modules.pullback f).map g).val.app (op ⊤)
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) s) :=
  congrArg (fun k => k.val.app (op ⊤) s) ((pullbackPushforwardAdjunction f).unit.naturality g)

end Scheme.Modules

namespace ProjectiveSpace

open Scheme.Cohomology Scheme.Modules

section Pullback

variable (ι : Type u) {B B' : Type u} [CommRing B] [CommRing B'] (σ : B →+* B')

/-- The comparison `π^*(𝒪(r) ⊗ 𝒪) ⟶ 𝒪(r) ⊗ 𝒪` on `P_{B'}`, for `π = map σ ι`:
`twistingTensorPullbackIso` followed by `pullbackUnitIso` on the second factor. -/
def unitTwistPullbackHom (r : ℤ) :
    (Scheme.Modules.pullback (map σ ι)).obj (unitTwist (B := B) ι r) ⟶
      unitTwist (B := B') ι r :=
  (twistingTensorPullbackIso σ ι r (𝟙_ _)).hom ≫
    (twistingSheaf B' ι r ◁ (Scheme.Modules.pullbackUnitIso (map σ ι)).hom)

/-- The comparison `unitTwistPullbackHom` commutes with the restrictions to a subscheme
`W ⊆ P_B` and to `W.comap (map σ ι)`, through `twistingTensorPullbackIso` and
`quotientModulePullbackIso` on the structure modules. -/
theorem unitTwistPullbackHom_comp_g (W : (ProjectiveSpace B ι).IdealSheafData) (r : ℤ) :
    unitTwistPullbackHom ι σ r ≫ (twistedShortComplex ι (W.comap (map σ ι)) r).g =
      (Scheme.Modules.pullback (map σ ι)).map (twistedShortComplex ι W r).g ≫
        (twistingTensorPullbackIso σ ι r W.quotientModule).hom ≫
          (moduleTensorLeftFunctor _ (twistingSheaf B' ι r)).map
            (W.quotientModulePullbackIso (map σ ι)).hom := by
  change _ ≫ (moduleTensorLeftFunctor _ (twistingSheaf B' ι r)).map
      (W.comap (map σ ι)).toQuotientModule =
    (Scheme.Modules.pullback (map σ ι)).map
      ((moduleTensorLeftFunctor _ (twistingSheaf B ι r)).map W.toQuotientModule) ≫ _
  have hnat := twistingTensorPullbackIso_hom_naturality_assoc σ ι r W.toQuotientModule
    ((moduleTensorLeftFunctor _ (twistingSheaf B' ι r)).map
      (W.quotientModulePullbackIso (map σ ι)).hom)
  erw [hnat]
  rw [← Functor.map_comp]
  erw [Scheme.IdealSheafData.pullback_map_toQuotientModule_quotientModulePullbackIso_hom]
  erw [Functor.map_comp]
  exact Category.assoc _ _ _

-- The restriction maps are compared on sections of differently presented module sheaves.
set_option backward.isDefEq.respectTransparency false in
/-- **A section vanishing on `W` pulls back to one vanishing on `W.comap (map σ ι)`**: for a
global section `s` of `𝒪(r) ⊗ 𝒪` on `P_B` whose restriction to the subscheme `W` is zero,
the restriction of `unitTwistPullbackHom (η s)` to `W.comap (map σ ι)` is zero. -/
theorem restriction_unitTwistPullbackHom_unit_eq_zero (W : (ProjectiveSpace B ι).IdealSheafData)
    (r : ℤ) (s : Γ(unitTwist (B := B) ι r, ⊤))
    (hs : (twistedShortComplex ι W r).g.val.app (op ⊤) s = 0) :
    (twistedShortComplex ι (W.comap (map σ ι)) r).g.val.app (op ⊤)
      ((unitTwistPullbackHom ι σ r).val.app (op ⊤)
        (((pullbackPushforwardAdjunction (map σ ι)).unit.app (unitTwist (B := B) ι r)).val.app
          (op ⊤) s)) = 0 := by
  have h := congrArg (fun k => k.val.app (op ⊤)
    (((pullbackPushforwardAdjunction (map σ ι)).unit.app (unitTwist (B := B) ι r)).val.app
      (op ⊤) s)) (unitTwistPullbackHom_comp_g ι σ W r)
  refine h.trans ?_
  change ((twistingTensorPullbackIso σ ι r W.quotientModule).hom ≫
          (moduleTensorLeftFunctor _ (twistingSheaf B' ι r)).map
            (W.quotientModulePullbackIso (map σ ι)).hom).val.app (op ⊤)
      (((Scheme.Modules.pullback (map σ ι)).map (twistedShortComplex ι W r).g).val.app (op ⊤)
        (((pullbackPushforwardAdjunction (map σ ι)).unit.app (unitTwist (B := B) ι r)).val.app
          (op ⊤) s)) = 0
  refine (congrArg (fun y => ((twistingTensorPullbackIso σ ι r W.quotientModule).hom ≫
          (moduleTensorLeftFunctor _ (twistingSheaf B' ι r)).map
            (W.quotientModulePullbackIso (map σ ι)).hom).val.app (op ⊤) y)
    (pullbackPushforward_unit_app_top_naturality (map σ ι) (twistedShortComplex ι W r).g
      s).symm).trans ?_
  dsimp only
  rw [hs, map_zero, map_zero]

-- The unitors and the comparison are evaluated on sections of the unit twist.
set_option backward.isDefEq.respectTransparency false in
/-- **The pullback of a polynomial section of the unit twist**: `unitTwistPullbackHom` sends the
pullback `η` of the section `p ⊗ 1` of `𝒪(r) ⊗ 𝒪` on `P_B` to the section `σ(p) ⊗ 1` on
`P_{B'}`. -/
theorem unitTwistPullbackHom_unit_homogeneousSection (r : ℕ)
    (q : MvPolynomial.homogeneousSubmodule ι B r) :
    (unitTwistPullbackHom ι σ r).val.app (op ⊤)
        (((pullbackPushforwardAdjunction (map σ ι)).unit.app (unitTwist (B := B) ι r)).val.app
          (op ⊤) ((ρ_ (twistingSheaf B ι r)).inv.val.app (op ⊤) (homogeneousSection B ι r q))) =
      (ρ_ (twistingSheaf B' ι r)).inv.val.app (op ⊤)
        (homogeneousSection B' ι r ((MvPolynomial.gradedMap (ι := ι) σ).gradedAddHom r q)) := by
  have h := congrArg (fun k => k.val.app (op ⊤)
    (((pullbackPushforwardAdjunction (map σ ι)).unit.app (twistingSheaf B ι r)).val.app (op ⊤)
      (homogeneousSection B ι r q))) (twistingTensorPullbackIso_rightUnitor σ ι r)
  dsimp only at h
  refine (congrArg (fun y => (unitTwistPullbackHom ι σ r).val.app (op ⊤) y)
    (pullbackPushforward_unit_app_top_naturality (map σ ι) (ρ_ (twistingSheaf B ι r)).inv
      (homogeneousSection B ι r q))).trans ?_
  refine h.trans ?_
  change (ρ_ (twistingSheaf B' ι r)).inv.val.app (op ⊤)
    ((twistingPullbackIso σ ι r).hom.val.app (op ⊤)
      (((pullbackPushforwardAdjunction (map σ ι)).unit.app (twistingSheaf B ι r)).val.app (op ⊤)
        (homogeneousSection B ι r q))) = _
  rw [twistingPullbackIso_hom_unit_homogeneousSection]

end Pullback

section H0

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : Type u} [CommRing A]

/-- `unitTwistH0Equiv`, unfolded into its three steps. -/
theorem unitTwistH0Equiv_apply (B : Type u) [CommRing B] [Algebra A B] (r : ℕ)
    (x : B ⊗[A] MvPolynomial.homogeneousSubmodule ι A r) :
    letI := Fintype.ofEquiv (Fin (n + 1)) e.symm
    unitTwistH0Equiv ι n e B r x =
      ((moduleCohomologyFunctorOfHom (ProjectiveSpace B ι)
        ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) 0).mapIso
          (ρ_ (twistingSheaf B ι (r : ℤ))).symm).toLinearEquiv
        ((twistingH0PolynomialLinearEquiv B ι (e.symm 0) r).symm
          (MvPolynomial.homogeneousSubmoduleBaseChangeEquiv ι r A B x)) :=
  rfl

-- The cohomology classes are compared with sections through presentations of `Sheaf.H`.
set_option backward.isDefEq.respectTransparency false in
/-- The section over `⊤` of the element of `H^0(𝒪(r) ⊗ 𝒪)` of `x ∈ B ⊗[A] A[x]_r`: the section
`p ⊗ 1` of the polynomial `p ∈ B[x]_r` of `x`. -/
theorem equiv₀_unitTwistH0Equiv (B : Type u) [CommRing B] [Algebra A B] (r : ℕ)
    (x : B ⊗[A] MvPolynomial.homogeneousSubmodule ι A r) :
    Sheaf.H.equiv₀ (moduleAddSheaf _ (unitTwist (B := B) ι r)) Limits.isTerminalTop
        (unitTwistH0Equiv ι n e B r x) =
      (ρ_ (twistingSheaf B ι r)).inv.val.app (op ⊤) (homogeneousSection B ι r
        (MvPolynomial.homogeneousSubmoduleBaseChangeEquiv ι r A B x)) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  refine (congrArg (Sheaf.H.equiv₀ (moduleAddSheaf _ (unitTwist (B := B) ι r))
    Limits.isTerminalTop) (unitTwistH0Equiv_apply ι n e B r x)).trans ?_
  refine (equiv₀_moduleCohomologyFunctorOfHom_mapIso _ (ρ_ (twistingSheaf B ι r)).symm _).trans ?_
  rw [equiv₀_twistingH0PolynomialLinearEquiv_symm]
  rfl

-- Cohomology classes are compared with sections through presentations of `Sheaf.H`.
set_option backward.isDefEq.respectTransparency false in
/-- **The kernel of the restriction is stable under base change**: for an `A`-algebra map
`f : B → B'`, a subscheme `W ⊆ P^n_B` and `x ∈ B ⊗[A] A[x]_r` whose section of `𝒪(r)`
vanishes on `W`, the section of `(f ⊗ id) x` vanishes on `W.comap (map f ι)`. -/
theorem restrictionH0_unitTwistH0Equiv_rTensor_eq_zero {B B' : Type u} [CommRing B]
    [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B')
    (W : (ProjectiveSpace B ι).IdealSheafData)
    (r : ℕ) (x : B ⊗[A] MvPolynomial.homogeneousSubmodule ι A r)
    (hx : restrictionH0 ι W r (unitTwistH0Equiv ι n e B r x) = 0) :
    restrictionH0 ι (W.comap (map (f : B →+* B') ι)) r
      (unitTwistH0Equiv ι n e B' r (f.toLinearMap.rTensor _ x)) = 0 := by
  apply (Sheaf.H.equiv₀ (moduleAddSheaf _ (quotientTwist ι (W.comap (map (f : B →+* B') ι)) r))
    Limits.isTerminalTop).injective
  refine (equiv₀_moduleCohomologyMapOfHom _ _ _).trans ?_
  rw [map_zero]
  refine (congrArg (fun y => (twistedShortComplex ι (W.comap (map (f : B →+* B') ι)) r).g.val.app
    (op ⊤) y) (equiv₀_unitTwistH0Equiv ι n e B' r _)).trans ?_
  dsimp only
  rw [MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_rTensor,
    ← unitTwistPullbackHom_unit_homogeneousSection]
  apply restriction_unitTwistPullbackHom_unit_eq_zero
  rw [← equiv₀_unitTwistH0Equiv ι n e B r x]
  refine (equiv₀_moduleCohomologyMapOfHom
    ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    (twistedShortComplex ι W r).g _).symm.trans ?_
  exact (congrArg (Sheaf.H.equiv₀ (moduleAddSheaf _ (quotientTwist ι W r)) Limits.isTerminalTop)
    hx).trans (map_zero _)

end H0

section Naturality

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : Type u} [CommRing A] {Φ : ℚ[X]}

/-- The restriction to `P^n_{B'}` of the pullback of a closed subscheme along a morphism
`t = Spec f : Spec B' ⟶ Spec B` is the pullback along `ProjectiveSpace.map f ι` of its restriction
to `P^n_B`. -/
theorem comap_baseChangeMap_comap_eq {B B' : Type u} [CommRing B] [CommRing B']
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (g' : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of A)) (f : B →+* B')
    (t : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
    (ht : t = Spec.map (CommRingCat.ofHom f)) (h : t ≫ g = g')
    (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    (Z.comap (baseChangeMap ι g g' t h)).comap (pointMap ι g' (𝟙 _)) =
      (Z.comap (pointMap ι g (𝟙 _))).comap (map f ι) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    pointMap_comp_baseChangeMap, map_comp_pointMap, Category.id_comp, Category.comp_id, ht]

include e in
/-- Membership in the Grassmannian point is vanishing of the restriction to the subscheme. -/
theorem mem_grassmannianPoint_toSubmodule_iff {B : Type u} [CommRing B] [IsNoetherianRing B]
    (W : (ProjectiveSpace B ι).IdealSheafData) [Flat (W.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι W p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    (v : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (unitTwist (B := B) ι r)) 0) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    v ∈ (grassmannianPoint ι n e W hfib r hr).toSubmodule ↔ restrictionH0 ι W r v = 0 := by
  let := h0Module ι (unitTwist (B := B) ι r)
  let := h0Module ι (quotientTwist ι W r)
  rw [grassmannianPoint_toSubmodule, LinearMap.mem_ker]

include e in
/-- **Naturality of the Grassmannian point at variable data**: for an `A`-algebra map
`f : B → B'` of Noetherian rings and flat subschemes `W ⊆ P^n_B`, `W' = W.comap (map f ι)` with all
fiber Hilbert polynomials `Φ`, Mathlib's base change along `f` of the point of `W` in
`G(⌊Φ(r)⌋₊, B ⊗[A] A[x]_r; B)` is the point of `W'`. -/
theorem map_ofLinearEquiv_grassmannianPoint {B B' : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [CommRing B'] [Algebra A B'] [IsNoetherianRing B'] (f : B →ₐ[A] B')
    (W : (ProjectiveSpace B ι).IdealSheafData) [Flat (W.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι W p) = Φ)
    (W' : (ProjectiveSpace B' ι).IdealSheafData) [Flat (W'.subschemeι ≫ toSpec B' ι)]
    (hfib' : ∀ p : PrimeSpectrum B',
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι W' p) = Φ)
    (hW : W.comap (map (f : B →+* B') ι) = W') (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    letI := h0Module ι (unitTwist (B := B') ι r)
    Module.Grassmannian.map f (Module.Grassmannian.ofLinearEquiv
        (unitTwistH0Equiv ι n e B r).symm (grassmannianPoint ι n e W hfib r hr)) =
      Module.Grassmannian.ofLinearEquiv (unitTwistH0Equiv ι n e B' r).symm
        (grassmannianPoint ι n e W' hfib' r hr) := by
  subst hW
  let := h0Module ι (unitTwist (B := B) ι r)
  let := h0Module ι (unitTwist (B := B') ι r)
  let := h0Module ι (quotientTwist ι W r)
  let := h0Module ι (quotientTwist ι (W.comap (map (f : B →+* B') ι)) r)
  apply Module.Grassmannian.map_eq_of_forall
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [SetLike.mem_coe, mem_grassmannianPoint_toSubmodule_iff] at hy
  rw [LinearEquiv.coe_coe]
  refine ⟨unitTwistH0Equiv ι (A := A) n e B' r
    (f.toLinearMap.rTensor _ ((unitTwistH0Equiv ι (A := A) n e B r).symm y)), ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_grassmannianPoint_toSubmodule_iff]
    refine restrictionH0_unitTwistH0Equiv_rTensor_eq_zero ι n e f W r _ ?_
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

include e in
/-- The point of the Grassmannian functor is the transported Grassmannian point of the restriction
of the family to `P^n_B`. -/
theorem IsHilbertFamily.grassmannianFunctorPoint_eq {B : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing B]
    {Z : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    haveI := hZ.flat_comap_pointMap ι (𝟙 _)
    hZ.grassmannianFunctorPoint ι n e r hr = Module.Grassmannian.ofLinearEquiv
        (unitTwistH0Equiv ι n e B r).symm (ProjectiveSpace.grassmannianPoint ι n e
          (Z.comap (pointMap ι _ (𝟙 _))) (hZ.primeFiber_comap_pointMap ι (𝟙 _)) r hr) :=
  rfl

include e in
/-- **Naturality of the Grassmannian point** (Nitsure, arXiv:math/0504590v1, §5, p. 26): for an
`A`-algebra map `f : B → B'` of Noetherian rings, `t = Spec f` and a point `Z` of
`Hilb^Φ(Spec B)`, Mathlib's base change along `f` of the point of `Z` is the point of the
pullback of `Z` to `Spec B'`. -/
theorem IsHilbertFamily.map_grassmannianFunctorPoint {B B' : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [CommRing B'] [Algebra A B'] [IsNoetherianRing B'] (f : B →ₐ[A] B')
    {Z : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z)
    (t : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
    (ht : t = Spec.map (CommRingCat.ofHom (f : B →+* B')))
    (h : t ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B')))
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Module.Grassmannian.map f (hZ.grassmannianFunctorPoint ι n e r hr) =
      (hZ.comap ι t h).grassmannianFunctorPoint ι n e r hr := by
  rw [hZ.grassmannianFunctorPoint_eq ι n e r hr,
    (hZ.comap ι t h).grassmannianFunctorPoint_eq ι n e r hr]
  have := hZ.flat_comap_pointMap ι (𝟙 _)
  have := (hZ.comap ι t h).flat_comap_pointMap ι (𝟙 _)
  exact map_ofLinearEquiv_grassmannianPoint ι n e f _ (hZ.primeFiber_comap_pointMap ι (𝟙 _)) _
    ((hZ.comap ι t h).primeFiber_comap_pointMap ι (𝟙 _))
    (comap_baseChangeMap_comap_eq ι _ _ (f : B →+* B') t ht h Z).symm r hr

end Naturality

section NatTrans

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]

/-- The Hilbert functor `B ↦ Hilb^Φ(Spec B)` on Noetherian `A`-algebras: the restriction of
`hilbertFunctor ι Φ` to the affine test schemes `Spec B` with `B` Noetherian. -/
abbrev noetherianAffineHilbertFunctor (Φ : ℚ[X]) :
    (ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A => IsNoetherianRing B) ⥤ Type u :=
  ObjectProperty.ι _ ⋙ (algSpec (CommRingCat.of A)).rightOp ⋙ hilbertFunctor ι Φ

/-- The component at `B` of `noetherianAffineGrassmannianNatTrans`: a point `Z` of
`Hilb^Φ(Spec B)` goes to `IsHilbertFamily.grassmannianFunctorPoint`. -/
def noetherianAffineGrassmannianNatTransApp (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (B : ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A => IsNoetherianRing B) :
    (noetherianAffineHilbertFunctor ι A Φ).obj B →
      (ObjectProperty.ι _ ⋙ Module.Grassmannian.functor.{u, u, u} (R := A)
        (M := MvPolynomial.homogeneousSubmodule ι A r) ⌊Φ.eval (r : ℚ)⌋₊).obj B :=
  fun (Z : {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)))).IdealSheafData //
        IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))) Z}) =>
    haveI := B.property
    Z.2.grassmannianFunctorPoint ι n e r hr

variable {A} in
/-- Naturality of `noetherianAffineGrassmannianNatTransApp`. -/
theorem noetherianAffineGrassmannianNatTransApp_naturality (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    {B B' : ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A => IsNoetherianRing B}
    (φ : B ⟶ B') (Z : (noetherianAffineHilbertFunctor ι A Φ).obj B) :
    noetherianAffineGrassmannianNatTransApp ι n e A Φ r hr B'
        ((noetherianAffineHilbertFunctor ι A Φ).map φ Z) =
      (ObjectProperty.ι _ ⋙ Module.Grassmannian.functor.{u, u, u} (R := A)
        (M := MvPolynomial.homogeneousSubmodule ι A r) ⌊Φ.eval (r : ℚ)⌋₊).map φ
          (noetherianAffineGrassmannianNatTransApp ι n e A Φ r hr B Z) :=
  haveI := B.property
  haveI := B'.property
  (IsHilbertFamily.map_grassmannianFunctorPoint ι n e φ.hom.hom
    (Z := (show {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)))).IdealSheafData //
        IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))) Z} from Z).1)
    (show {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)))).IdealSheafData //
        IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))) Z} from Z).2
    ((algSpec (CommRingCat.of A)).map φ.hom.op).left (algSpec_map_left_eq φ.hom)
    (Over.w ((algSpec (CommRingCat.of A)).map φ.hom.op)) r hr).symm

/-- **The Grassmannian embedding of the Hilbert functor on Noetherian affine test schemes**
(Nitsure, arXiv:math/0504590v1, §5, p. 26): for `r ≥ hilbertRegularityBound n Φ`, the points
`IsHilbertFamily.grassmannianFunctorPoint` form a natural transformation from
`B ↦ Hilb^Φ(Spec B)` to Mathlib's Grassmannian functor `B ↦ G(⌊Φ(r)⌋₊, B ⊗[A] A[x]_r; B)` on
Noetherian `A`-algebras. -/
def noetherianAffineGrassmannianNatTrans (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    noetherianAffineHilbertFunctor ι A Φ ⟶ ObjectProperty.ι _ ⋙
      Module.Grassmannian.functor.{u, u, u} (R := A)
        (M := MvPolynomial.homogeneousSubmodule ι A r) ⌊Φ.eval (r : ℚ)⌋₊ where
  app B := TypeCat.ofHom (noetherianAffineGrassmannianNatTransApp ι n e A Φ r hr B)
  naturality _ _ φ := ConcreteCategory.hom_ext _ _ fun Z =>
    noetherianAffineGrassmannianNatTransApp_naturality ι n e Φ r hr φ Z

include e in
/-- The components of `noetherianAffineGrassmannianNatTrans` are injective: a point of
`Hilb^Φ(Spec B)`, `B` Noetherian, is determined by its point of the Grassmannian functor. -/
theorem noetherianAffineGrassmannianNatTrans_app_injective (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (B : ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A => IsNoetherianRing B) :
    Function.Injective ((noetherianAffineGrassmannianNatTrans ι n e A Φ r hr).app B) := by
  have := B.property
  intro (Z : {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)))).IdealSheafData //
        IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))) Z})
    (Z' : {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)))).IdealSheafData //
        IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))) Z}) h
  exact Subtype.ext (IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq ι n e Z.2 Z'.2 r hr h)

end NatTrans

end ProjectiveSpace

end AlgebraicGeometry
