/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Basic
public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.LinearSystem

/-!
# `R = Z ×_P Z` is represented by a Grassmannian bundle over `Z`

Let `A` be a Noetherian ring, `i : X ⟶ P^N_A` a closed immersion with `ι ≃ Fin (N + 1)` such that
`πX = i ≫ toSpec A ι` is flat and geometrically integral, `φ₀, ψ ∈ ℚ[X]`, `r = k + 1 ≥ 1`,
`C = fineCondition i N e φ₀ ψ 0 (k + 1)` the fibre condition of the stratum `Pic^{φ₀,ψ,r}_0`, and
`E` a representation of `Div^{ψ − φ₀}_X` on locally Noetherian test schemes. Let
`Z = C.abelPreimageOver E` with universal class `α_Z`, universal divisor `W_Z`, `𝒪(W_Z)` on
`X_Z = X ×_S Z`, and `G = Gr(p_{Z*}𝒪(W_Z), k)` the Grassmannian bundle over `Z` representing
`LinSys_{𝒪(W_Z)/X_Z/Z}` (`Picard/Strata/Relation/LinearSystem`). This file proves the
identification of `Z ×_P Z` with that linear system in Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30: "Virtually by definition, the product
`T′ ×_{P_0^{φ0}} Z` is equal to `LinSys_{L′/X_{T′}/T′}`", applied with `L′` the invertible sheaf of
the universal divisor on `X_Z` ("So taking `T := Z` and `T′ := T` above, we conclude that the
product `Z ×_{P_0^{φ0}} Z` is a scheme").

* `RelativePicard.familyMap_comp_isoPullback_hom`: the comparisons `X ×_S U ≅ X_V ×_V U` of
  `Picard/LinearSystem/AbelClass` are natural in `U` (stated at variable data).
* `Strata.abelRelationOver e k E`: the scheme `R = G` as a locally Noetherian scheme over `S`, with
  the first projection `abelRelationFst : R ⟶ Z` (the structure map of `G`) and the second
  projection `abelRelationSnd : R ⟶ Z`, the point of `Z` classifying the universal divisor of the
  linear system transported to `X ×_S R` (`abelRelationSndDivisor`): its fppf class is
  `pr₁^* α_Z` (`fppfAbelClass_abelRelationSndDivisor`), which lies in the stratum, so the divisor
  lies in `Div^{ψ − φ₀}_X` and in `Z`.
* `Strata.abelRelationι e k E : R ⟶ Z ×_S Z`, the pair of projections.
* `Strata.fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd`: `pr₁^* α_Z = pr₂^* α_Z`.
* `Strata.homEquiv_comp_abelRelationSnd_coe`: for `c : T ⟶ R` with `c ≫ pr₁ = a`, the divisor
  classified by `c ≫ pr₂` is the transport to `X ×_S T` of the linear-system divisor classified
  by `c` over `Z`.
* `Strata.exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff`,
  `Strata.abelRelation_hom_ext`, `Strata.abelRelationRepresentableBy`: **`R` represents
  `Z ×_P Z`** on locally Noetherian test schemes: `c ↦ (c ≫ pr₁, c ≫ pr₂)` is a bijection from
  `Hom_S(T, R)` to the pairs `(a, b)` of points of `Z` with `a^* α_Z = b^* α_Z`.

The proof of surjectivity uses `P_{X/S}(T) ↪ P(T)` (Kleiman, Thm 2.5(1), p. 18) through
`fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff`, and the Abel-class form of the linear
system (`isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Modules.Invertible Modules.Invertible.PullbackTensor.Local ProjectiveSpace

section Transport

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- Abel classes of equal divisors are equal. -/
theorem abelClass_congr {T : Over S} {D₁ D₂ : (pullback p T.hom).IdealSheafData} (h : D₁ = D₂)
    (h₁ : Hom.IsRelativeEffectiveCartier D₁.subschemeι (pullback.snd p T.hom))
    (h₂ : Hom.IsRelativeEffectiveCartier D₂.subschemeι (pullback.snd p T.hom)) :
    abelClass p D₁ h₁ = abelClass p D₂ h₂ := by
  subst h
  rfl

/-- **Naturality of `X ×_S U ≅ X_V ×_V U` in `U`**: for `c : U₁ ⟶ U₂` and `g : U₂ ⟶ V` over `S`,
the comparison for `g` after the base-change map `X ×_S U₁ ⟶ X ×_S U₂` is the comparison for
`c ≫ g` followed by the base-change map `X_V ×_V U₁ ⟶ X_V ×_V U₂` of the family over `V`. -/
theorem familyMap_comp_isoPullback_hom {U₁ U₂ V : Over S} (c : U₁ ⟶ U₂) (g : U₂ ⟶ V) :
    LinearSystem.familyMap p c ≫ (LinearSystem.isPullback_familyMap p g).isoPullback.hom =
      (LinearSystem.isPullback_familyMap p (c ≫ g)).isoPullback.hom ≫
        LinearSystem.familyMap (pullback.snd p V.hom)
          (Over.homMk c.left rfl : Over.mk (c ≫ g).left ⟶ Over.mk g.left) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]
    erw [LinearSystem.familyMap_fst, IsPullback.isoPullback_hom_fst]
    rw [LinearSystem.familyMap_comp]
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      LinearSystem.familyMap_snd]
    erw [LinearSystem.familyMap_snd, IsPullback.isoPullback_hom_snd_assoc]
    rfl

end Transport

namespace Strata

open LinearSystem Grassmannian

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- **The scheme `R`** of the proof of Kleiman's Thm 4.8 (arXiv:math/0504020v1, p. 30), as a
locally Noetherian scheme over `S = Spec A`: the Grassmannian bundle `Gr(p_{Z*}𝒪(W_Z), k)` over
`Z`, which is locally of finite type over the locally Noetherian `Z`. -/
def abelRelationOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  ⟨Over.mk ((abelRelationBundle e k E).hom ≫
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom),
    LocallyOfFiniteType.isLocallyNoetherian (abelRelationBundle e k E).hom⟩

theorem abelRelationOver_obj_left :
    (abelRelationOver e k E).obj.left = (abelRelationBundle e k E).left :=
  rfl

/-- **The first projection** `pr₁ : R ⟶ Z`, the structure map of the Grassmannian bundle. -/
def abelRelationFst :
    abelRelationOver e k E ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E :=
  ObjectProperty.homMk (Over.homMk (abelRelationBundle e k E).hom rfl)

theorem abelRelationFst_hom_left :
    (abelRelationFst e k E).hom.left = (abelRelationBundle e k E).hom :=
  rfl

variable [GeometricallyIntegral (i ≫ toSpec A ι)]

/-- **The transported universal divisor**: the universal divisor of the linear system on
`X_Z ×_Z R`, pulled back to `X ×_S R` along `X ×_S R ≅ X_Z ×_Z R`. -/
def abelRelationSndDivisor :
    (pullback (i ≫ toSpec A ι) (abelRelationOver e k E).obj.hom).IdealSheafData :=
  (abelRelationLinearSystemDivisor e k E).1.comap
    (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι) (abelRelationFst e k E).hom).isoPullback.hom

theorem isRelativeEffectiveCartier_abelRelationSndDivisor :
    Hom.IsRelativeEffectiveCartier (abelRelationSndDivisor e k E).subschemeι
      (pullback.snd (i ≫ toSpec A ι) (abelRelationOver e k E).obj.hom) :=
  isRelativeEffectiveCartier_comap_isoPullback_hom _ (abelRelationFst e k E).hom
    (abelRelationLinearSystemDivisor e k E).2.1

/-- **The fppf class of the transported universal divisor is `pr₁^* α_Z`**: the universal divisor
of `LinSys_{𝒪(W_Z)}` differs from `pr₁^* 𝒪(W_Z)` by a class pulled back from `R`. -/
theorem fppfAbelClass_abelRelationSndDivisor :
    fppfAbelClass (i ≫ toSpec A ι) (T := (abelRelationOver e k E).obj)
        (abelRelationSndDivisor e k E) (isRelativeEffectiveCartier_abelRelationSndDivisor e k E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationFst e k E).hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) := by
  rw [← (fineCondition i N e φ₀ ψ 0 (k + 1)).app_classOf_abelPreimageDivisorLineBundle E]
  exact fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor _
    (abelRelationFst e k E).hom _ (abelRelationLinearSystemDivisor e k E).2

/-- The transported universal divisor lies in the stratum: its fppf class is in
`Pic^{φ₀,ψ,k+1}_0(R)`. -/
theorem fppfAbelClass_abelRelationSndDivisor_mem :
    fppfAbelClass (i ≫ toSpec A ι) (T := (abelRelationOver e k E).obj)
        (abelRelationSndDivisor e k E) (isRelativeEffectiveCartier_abelRelationSndDivisor e k E) ∈
      (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.obj (op (abelRelationOver e k E).obj) := by
  rw [fppfAbelClass_abelRelationSndDivisor]
  exact (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.map (abelRelationFst e k E).hom.op
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass_mem_subfunctor E)

/-- The transported universal divisor as a point of `Z = Pic^{φ₀,ψ,k+1}_0 ×_P Div^{ψ − φ₀}_X` over
`R`: it lies in `Div^{ψ − φ₀}_X(R)`
(`isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition`) and its class lies in the
stratum. -/
def abelRelationSndPoint :
    (LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimage i rfl (ψ - φ₀))).toFunctor.obj
        (op (abelRelationOver e k E)) :=
  ⟨⟨abelRelationSndDivisor e k E,
      isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition
        (isRelativeEffectiveCartier_abelRelationSndDivisor e k E)
        (fppfAbelClass_abelRelationSndDivisor_mem e k E)⟩,
    fppfAbelClass_abelRelationSndDivisor_mem e k E⟩

/-- **The second projection** `pr₂ : R ⟶ Z`: the point of `Z` classifying the transported
universal divisor of the linear system. -/
def abelRelationSnd :
    abelRelationOver e k E ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E :=
  ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv.symm
    (abelRelationSndPoint e k E)

/-- The divisor classified by `pr₂` is the transported universal divisor. -/
theorem homEquiv_abelRelationSnd_coe :
    (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
      (abelRelationSnd e k E)).1.1 = abelRelationSndDivisor e k E := by
  rw [abelRelationSnd, Equiv.apply_symm_apply]
  rfl

/-- **`pr₁^* α_Z = pr₂^* α_Z`**: the two projections of `R` pull the universal class of `Z` back
to the same class. -/
theorem fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationFst e k E).hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationSnd e k E).hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) := by
  rw [← fppfAbelClass_abelRelationSndDivisor,
    FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass]
  congr 1
  exact (homEquiv_abelRelationSnd_coe e k E).symm

/-- **The pair of projections** `R ⟶ Z ×_S Z`. -/
def abelRelationι : (abelRelationOver e k E).obj.left ⟶
    pullback ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom :=
  pullback.lift (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left
    ((Over.w (abelRelationFst e k E).hom).trans (Over.w (abelRelationSnd e k E).hom).symm)

@[reassoc (attr := simp)]
theorem abelRelationι_fst :
    abelRelationι e k E ≫ pullback.fst _ _ = (abelRelationFst e k E).hom.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem abelRelationι_snd :
    abelRelationι e k E ≫ pullback.snd _ _ = (abelRelationSnd e k E).hom.left :=
  pullback.lift_snd _ _ _

/-- The lift of `c : T ⟶ R` to a morphism `T ⟶ Gr(p_{Z*}𝒪(W_Z), k)` over `Z`, for `T` a
`Z`-scheme through `a = c ≫ pr₁`. -/
def abelRelationBundleLift {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    {a : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E}
    (c : T ⟶ abelRelationOver e k E) (h : c ≫ abelRelationFst e k E = a) :
    Over.mk a.hom.left ⟶ abelRelationBundle e k E :=
  Over.homMk c.hom.left (by rw [← h]; rfl)

/-- **The divisor classified by `c ≫ pr₂`** is the transport to `X ×_S T` of the linear-system
divisor over `Z` classified by `c`. -/
theorem homEquiv_comp_abelRelationSnd_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    {a : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E}
    (c : T ⟶ abelRelationOver e k E) (h : c ≫ abelRelationFst e k E = a) :
    (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
        (c ≫ abelRelationSnd e k E)).1.1 =
      ((abelRelationBundleRepresentableBy e k E).homEquiv
          (abelRelationBundleLift e k E c h)).1.comap
        (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι) a.hom).isoPullback.hom := by
  subst h
  rw [abelRelationBundleRepresentableBy_homEquiv_coe, ← IdealSheafData.comap_comp]
  have hnat := familyMap_comp_isoPullback_hom (i ≫ toSpec A ι) c.hom (abelRelationFst e k E).hom
  calc (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
        (c ≫ abelRelationSnd e k E)).1.1
      = (abelRelationSndDivisor e k E).comap (LinearSystem.familyMap (i ≫ toSpec A ι) c.hom) := by
        rw [Functor.RepresentableBy.homEquiv_comp]
        exact congrArg
          (fun W => IdealSheafData.comap W (LinearSystem.familyMap (i ≫ toSpec A ι) c.hom))
          (homEquiv_abelRelationSnd_coe e k E)
    _ = (abelRelationLinearSystemDivisor e k E).1.comap
          (LinearSystem.familyMap (i ≫ toSpec A ι) c.hom ≫
            (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι)
              (abelRelationFst e k E).hom).isoPullback.hom) :=
        (IdealSheafData.comap_comp _ _ _).symm
    _ = _ := congrArg (IdealSheafData.comap (abelRelationLinearSystemDivisor e k E).1) hnat

/-- **`R ⟶ Z ×_S Z` is injective on points**: two points of `R` over a locally Noetherian `T` with
the same two projections are equal. Both lift to `Gr(p_{Z*}𝒪(W_Z), k)` over `Z` through the same
`a : T ⟶ Z`, and their linear-system divisors transport to the same divisor of `X ×_S T`. -/
theorem abelRelation_hom_ext {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    {c c' : T ⟶ abelRelationOver e k E}
    (h₁ : c ≫ abelRelationFst e k E = c' ≫ abelRelationFst e k E)
    (h₂ : c ≫ abelRelationSnd e k E = c' ≫ abelRelationSnd e k E) : c = c' := by
  have k₁ := homEquiv_comp_abelRelationSnd_coe e k E c rfl
  have k₂ := homEquiv_comp_abelRelationSnd_coe e k E c' h₁.symm
  rw [h₂] at k₁
  have hD := ((comap_isoPullback_hom_comap_inv (i ≫ toSpec A ι)
      (c ≫ abelRelationFst e k E).hom _).symm.trans
    ((congrArg (fun W => IdealSheafData.comap W (LinearSystem.isPullback_familyMap
      (i ≫ toSpec A ι) (c ≫ abelRelationFst e k E).hom).isoPullback.inv) (k₁.symm.trans k₂)).trans
        (comap_isoPullback_hom_comap_inv _ _ _)))
  have hlift : abelRelationBundleLift e k E c rfl = abelRelationBundleLift e k E c' h₁.symm :=
    (abelRelationBundleRepresentableBy e k E).homEquiv.injective (Subtype.ext hD)
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (congrArg (fun f => f.left) hlift))

variable [IsNoetherianRing A]

omit [GeometricallyIntegral (i ≫ toSpec A ι)] [IsNoetherianRing A] in
/-- The Abel class of the divisor `W_a` classified by `a : T ⟶ Z` is the pullback of the class
of `𝒪(W_Z)` along `X ×_S T ⟶ X ×_S Z`. -/
theorem pullbackClass_familyMap_classOf_abelPreimageDivisorLineBundle
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E) :
    pullbackClass (LinearSystem.familyMap (i ≫ toSpec A ι) a.hom)
        (classOf _ ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E)) =
      abelClass (i ≫ toSpec A ι) (T := T.obj)
        (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv a).1.1
        (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
          a).1.2.isRelativeEffectiveCartier := by
  rw [FiberCondition.classOf_abelPreimageDivisorLineBundle,
    pullbackClass_abelClass _ (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι) a.hom)]
  exact abelClass_congr _ (FiberCondition.abelPreimageRepresentableBy_homEquiv_coe_eq_comap
    _ E a).symm _ _

/-- **The transport of `W_b` to `X_Z ×_Z T` is a divisor of the linear system** over `T`, a
`Z`-scheme through `a`, when `a^* α_Z = b^* α_Z` (Kleiman, arXiv:math/0504020v1, proof of
Thm 4.8, p. 30, with Thm 2.5(1), p. 18). -/
theorem isLinearSystemDivisor_comap_isoPullback_inv_of_eq
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    {a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E}
    (hab : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) :
    IsLinearSystemDivisor (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E) (Over.mk a.hom.left)
      ((((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv b).1.1.comap
        (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι) a.hom).isoPullback.inv) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨n, hn⟩ :=
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff
      E a b).mp hab
  refine (isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage _ a.hom _
    (isRelativeEffectiveCartier_comap_isoPullback_inv _ a.hom
      (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
        b).1.2.isRelativeEffectiveCartier)).mpr ⟨-n, ?_⟩
  change pullbackClass (pullback.snd (i ≫ toSpec A ι) T.obj.hom) (-n) = _
  rw [abelClass_congr _ (comap_isoPullback_inv_comap_hom _ _ _) _
      (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
        b).1.2.isRelativeEffectiveCartier,
    pullbackClass_familyMap_classOf_abelPreimageDivisorLineBundle e k E a, hn, pullbackClass_neg]
  exact (sub_add_cancel_left _ _).symm

/-- **Every pair of points of `Z` with the same class comes from `R`** (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30, with Thm 2.5(1), p. 18): for `a, b : T ⟶ Z` with
`a^* α_Z = b^* α_Z`, the divisors `W_a`, `W_b` differ by a class pulled back from `T`, so the
transport of `W_b` to `X_Z ×_Z T` lies in `LinSys_{𝒪(W_Z)}(T)`, and its classifying map
`T ⟶ Gr(p_{Z*}𝒪(W_Z), k)` over `Z` is a point `c` of `R` with `c ≫ pr₁ = a`, `c ≫ pr₂ = b`. -/
theorem exists_comp_abelRelationFst_and_comp_abelRelationSnd_of_eq
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    {a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E}
    (hab : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) :
    ∃ c : T ⟶ abelRelationOver e k E,
      c ≫ abelRelationFst e k E = a ∧ c ≫ abelRelationSnd e k E = b := by
  obtain ⟨c', hc'⟩ : ∃ c' : Over.mk a.hom.left ⟶ abelRelationBundle e k E,
      ((abelRelationBundleRepresentableBy e k E).homEquiv c').1 =
        (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv b).1.1.comap
          (LinearSystem.isPullback_familyMap (i ≫ toSpec A ι) a.hom).isoPullback.inv :=
    ⟨(abelRelationBundleRepresentableBy e k E).homEquiv.symm
        ⟨_, isLinearSystemDivisor_comap_isoPullback_inv_of_eq e k E hab⟩,
      congrArg Subtype.val ((abelRelationBundleRepresentableBy e k E).homEquiv.apply_symm_apply
        ⟨_, isLinearSystemDivisor_comap_isoPullback_inv_of_eq e k E hab⟩)⟩
  have hw : c'.left ≫ (abelRelationOver e k E).obj.hom = T.obj.hom := by
    change c'.left ≫ (abelRelationBundle e k E).hom ≫ _ = _
    rw [← Category.assoc, Over.w c']
    exact Over.w a.hom
  have hc₁ : (ObjectProperty.homMk (Over.homMk c'.left hw) : T ⟶ abelRelationOver e k E) ≫
      abelRelationFst e k E = a :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Over.w c'))
  refine ⟨_, hc₁, ?_⟩
  apply ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv.injective
  refine Subtype.ext (Subtype.ext ((homEquiv_comp_abelRelationSnd_coe e k E _ hc₁).trans ?_))
  have hlift : abelRelationBundleLift e k E _ hc₁ = c' := Over.OverMorphism.ext rfl
  rw [hlift, hc']
  exact comap_isoPullback_inv_comap_hom _ _ _

/-- **The points of `R` are the pairs with the same class** (Kleiman, arXiv:math/0504020v1,
proof of Thm 4.8, p. 30): a pair `(a, b)` of points of `Z` over a locally Noetherian `T` comes
from a point of `R` if and only if `a^* α_Z = b^* α_Z`. -/
theorem exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E) :
    (∃ c : T ⟶ abelRelationOver e k E,
        c ≫ abelRelationFst e k E = a ∧ c ≫ abelRelationSnd e k E = b) ↔
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) := by
  refine ⟨?_, exists_comp_abelRelationFst_and_comp_abelRelationSnd_of_eq e k E⟩
  rintro ⟨c, rfl, rfl⟩
  rw [FiberCondition.fppfPicardSheaf_map_comp_abelPreimageFppfAbelClass,
    FiberCondition.fppfPicardSheaf_map_comp_abelPreimageFppfAbelClass,
    fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd]

/-- **`R` represents `Z ×_P Z`** on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30): `c ↦ (c ≫ pr₁, c ≫ pr₂)` is a natural bijection
from the points of `R = Gr(p_{Z*}𝒪(W_Z), k)` to the pairs of points of `Z` with the same class in
`Pic_{X/S,(fppf)}`. -/
def abelRelationRepresentableBy :
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelRelation E).RepresentableBy
      (abelRelationOver e k E) where
  homEquiv {T} := Equiv.ofBijective
    (fun c => ⟨(c ≫ abelRelationFst e k E, c ≫ abelRelationSnd e k E),
      (exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff e k E _ _).mp ⟨c, rfl, rfl⟩⟩)
    ⟨fun c c' h => abelRelation_hom_ext e k E (congrArg (fun x => x.1.1) h)
        (congrArg (fun x => x.1.2) h),
      fun ab => by
        obtain ⟨c, h₁, h₂⟩ := exists_comp_abelRelationFst_and_comp_abelRelationSnd_of_eq e k E ab.2
        exact ⟨c, Subtype.ext (Prod.ext h₁ h₂)⟩⟩
  homEquiv_comp {T T'} f c :=
    Subtype.ext (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

theorem abelRelationRepresentableBy_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (c : T ⟶ abelRelationOver e k E) :
    ((abelRelationRepresentableBy e k E).homEquiv c).1 =
      (c ≫ abelRelationFst e k E, c ≫ abelRelationSnd e k E) :=
  rfl

end Strata

end AlgebraicGeometry.Scheme.RelativePicard
