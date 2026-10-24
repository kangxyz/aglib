/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.DivisorLocus
public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Representability
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.AbelClass
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Surjective
public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# Local sections of the Abel map on a fine stratum

Let `A` be a ring and `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed immersion with
`e : ι ≃ Fin (N + 1)`, such that `πX = i ≫ toSpec A ι` is flat with geometrically integral
fibres. Let `φ₀, ψ ∈ ℚ[X]`, `k ∈ ℕ`, `θ = ψ − φ₀`, and let
`C = fineCondition i N e φ₀ ψ 0 (k + 1)` be the fibre condition of the stratum
`Pic^{φ₀,ψ,k+1}_0` (`Picard/Strata/Conditions`). For a representation `E` of `Div^θ_X` on locally
Noetherian test schemes, `Z = C.abelPreimageOver E` is the open subscheme
`Pic^{φ₀,ψ,k+1}_0 ×_P Div^θ_X` of the representing scheme, with universal class
`α_Z = C.abelPreimageFppfAbelClass E` (`Picard/Abel/Divisor`); here `P = Pic_{X/S,(fppf)}` and
`S = Spec A`.

* `exists_lift_abelPreimageOver_of_forall_fineCondition_holds`: for a locally Noetherian `V` over
  `S` and a line bundle `L` on `X ×_S V` that satisfies `C` at every point of `V`, there are a
  locally Noetherian `U`, a flat surjective morphism `g : U ⟶ V` locally of finite presentation,
  and `a : U ⟶ Z` with `a^* α_Z = g^* [L]` in `P(U)`. The scheme `U` is the Grassmannian bundle
  `Gr(E_V, k)` of rank-`k` locally free quotients of `E_V = p_{V*} L`, which is locally free of
  rank `k + 1` with every base-change map of `L` an isomorphism
  (`sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds`). It represents
  `LinSys_{L/X_V/V}` (`LinearSystem.linearSystemRepresentableBy`), and `a` classifies the
  transport to `X ×_S U` of its universal divisor: the fppf Abel class of the transport is `g^*[L]`
  (`LinearSystem.fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor`), hence lies in
  `Pic^{φ₀,ψ,k+1}_0(U)`, so the transport is a point of `Div^θ_X(U)`
  (`isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition`) and of `Z`. The
  morphism `g : Gr(E_V, k) ⟶ V` is flat (`Grassmannian.flat_grassmannianBundle_hom`; it is even
  smooth), locally of finite presentation (it is locally of finite type over the locally Noetherian
  `V`) and, since `k ≤ k + 1`, surjective (`Grassmannian.surjective_grassmannianBundle_hom_of_le`).
* `exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition`: **the Abel map `Z ⟶
  Pic^{φ₀,ψ,k+1}_0` is fppf-locally surjective** on locally Noetherian test schemes. For
  `ξ ∈ Pic^{φ₀,ψ,k+1}_0(T)` and `t ∈ T` there are a locally Noetherian `U`, a flat morphism
  `f : U ⟶ T` locally of finite presentation with `t` in its image, and `a : U ⟶ Z` with
  `a^* α_Z = f^* ξ`. The statement is, up to the name of the bound morphism, hypothesis (h₃) of
  `Scheme.representableByOfFppfQuotient` (`Sites/FppfQuotient`) for
  `F = (fppfPicardSheaf πX).obj ⋙ forget AddCommGrpCat`, `G = C.locallyNoetherianSubfunctor`
  (the restriction of `Pic^{φ₀,ψ,k+1}_0` to locally Noetherian test schemes,
  `FiberCondition.locallyNoetherianSubfunctor`) and `z = α_Z`. The morphism `f` is
  `Gr(E_V, k) ⟶ V ⟶ T` for a representative `L` of the restriction of `ξ` to a flat neighbourhood
  `V ⟶ T` of `t` locally of finite presentation (`FiberCondition.exists_flat_app_eq`); `L`
  satisfies `C` at every point of `V` (`FiberCondition.mem_subfunctor_iff`,
  `FiberCondition.holdsAt_iff`), and `V` is locally Noetherian, being locally of finite type over
  `T`.

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 30 ("Let’s now
prove the projection `α : Z → P_0^{φ0}` is a surjection of étale sheaves"), in the fppf topology
and on locally Noetherian test schemes. Kleiman represents `λ` by an invertible sheaf `L′` on
`X_{T′}` for an étale covering `T′ → T`, identifies `T′ ×_{P_0^{φ0}} Z` with
`LinSys_{L′/X_{T′}/T′} = P(Q)` by Thm 3.13 (pp. 25–26), shows that `Q` is locally free, so that
`P(Q)` is smooth over `T′`, and takes an étale covering `T₁ → T′` with a `T′`-map `T₁ → P(Q)`
(EGA IV₄ 17.16.3 (ii)). Here `T′ = V` is an fppf neighbourhood and `T₁` is `Gr(E_V, k)` itself,
the scheme representing the linear system (Kleiman's `P(Q)`: `Q` is the dual of `E_V`, and
rank-one locally free quotients of `Q` correspond to rank-`k` locally free quotients of `E_V`). It
is an fppf covering of `V` because it is flat, surjective and locally of finite presentation; no
étale-local section is needed. Only the map `T₁ ⟶ Z` is constructed, not the identification of
`T′ ×_P Z` with the linear system. The rank `k + 1 ≥ 1` of the stratum is used for the
surjectivity: at a point where `h^0(X_t, L_t) = 0` the fibre of `P(Q)` is empty.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

open LinearSystem Grassmannian

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- **Local lifts to `Z` of a line bundle on the fine stratum** (Kleiman, arXiv:math/0504020v1,
proof of Thm 4.8, p. 30, with `T₁ = P(Q)`): for a locally Noetherian `V` over `Spec A` and a line
bundle `L` on `X ×_{Spec A} V` satisfying `fineCondition i N e φ₀ ψ 0 (k + 1)` at every point of
`V`, there are a locally Noetherian `U`, a flat surjective morphism `g : U ⟶ V` locally of finite
presentation, and `a : U ⟶ Z` with `a^* α_Z = g^* [L]` in `Pic_{X/S,(fppf)}(U)`. One may take
`U = Gr(p_{V*} L, k)`, with `a` classifying its universal linear-system divisor. -/
theorem exists_lift_abelPreimageOver_of_forall_fineCondition_holds
    {V : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (L : LineBundle (pullback (i ≫ toSpec A ι) V.obj.hom))
    (hL : ∀ v, (fineCondition i N e φ₀ ψ 0 (k + 1)).Holds V.obj (classOf _ L) v) :
    ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))) (g : U ⟶ V)
      (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
      Flat g.hom.left ∧ LocallyOfFinitePresentation g.hom.left ∧ Surjective g.hom.left ∧
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.hom.op
            ((quotientProjection _ ≫ toFppfPicardSheaf _).app (op V.obj) (classOf _ L)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨hE, hbc⟩ := sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds hL
  let Gr : Over V.obj.left := grassmannianBundle
    ((Modules.pushforward (pullback.snd (i ≫ toSpec A ι) V.obj.hom)).obj L.val) k (k + 1) hE
  have : LocallyOfFiniteType Gr.hom := locallyOfFiniteType_grassmannianBundle_hom _ k (k + 1) hE
  let U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
    ⟨Over.mk (Gr.hom ≫ V.obj.hom), LocallyOfFiniteType.isLocallyNoetherian Gr.hom⟩
  let g : U ⟶ V := ObjectProperty.homMk (Over.homMk Gr.hom rfl)
  let W := universalLinearSystemDivisor (pullback.snd (i ≫ toSpec A ι) V.obj.hom) L hbc hE
  have hW : IsLinearSystemDivisor (pullback.snd (i ≫ toSpec A ι) V.obj.hom) L
      (Over.mk g.hom.left) W.1 := W.2
  have heq := fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor
    (i ≫ toSpec A ι) g.hom L hW
  have hmem : fppfAbelClass (i ≫ toSpec A ι) (T := U.obj)
      (W.1.comap (isPullback_familyMap (i ≫ toSpec A ι) g.hom).isoPullback.hom)
      (isRelativeEffectiveCartier_comap_isoPullback_hom _ g.hom hW.1) ∈
        (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.obj (op U.obj) :=
    (congrArg (· ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.obj (op U.obj)) heq).mpr
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.map g.hom.op
        (((fineCondition i N e φ₀ ψ 0 (k + 1)).app_mem_subfunctor_iff _).mpr hL))
  refine ⟨U, g, ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv.symm
    ⟨⟨_, isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition _ hmem⟩, hmem⟩,
    flat_grassmannianBundle_hom _ k (k + 1) hE,
    inferInstanceAs (LocallyOfFinitePresentation Gr.hom),
    surjective_grassmannianBundle_hom_of_le _ k hE (Nat.le_succ k), ?_⟩
  rw [FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass, Equiv.apply_symm_apply]
  exact heq

/-- **The Abel map `Z ⟶ Pic^{φ₀,ψ,k+1}_0` is fppf-locally surjective** (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30, in the fppf topology): for a locally Noetherian
test scheme `T`, a section `ξ ∈ Pic^{φ₀,ψ,k+1}_0(T)` and `t ∈ T`, there are a locally Noetherian
`U`, a flat morphism `f : U ⟶ T` locally of finite presentation with `t` in its image, and
`a : U ⟶ Z` with `a^* α_Z = f^* ξ`. This is hypothesis (h₃) of
`Scheme.representableByOfFppfQuotient` for `F = (fppfPicardSheaf πX).obj ⋙ forget AddCommGrpCat`,
`G = (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor` (the restriction of
`Pic^{φ₀,ψ,k+1}_0` to locally Noetherian test schemes), `Z` and `z = α_Z`. -/
theorem exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition :
    ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
      (ξ : ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).obj
        (op T.obj)),
      ξ ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
        (f : U ⟶ T) (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        Flat f.hom.left ∧ LocallyOfFinitePresentation f.hom.left ∧ t ∈ Set.range f.hom.left ∧
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
            ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              f.hom.op ξ := by
  intro T ξ hξ t
  have hξ' := ((fineCondition i N e φ₀ ψ 0 (k + 1)).mem_subfunctor_iff (T := T.obj) ξ).mp hξ
  obtain ⟨V, h, a, hflat, hlfp, ⟨v, rfl⟩, ha⟩ :=
    FiberCondition.exists_flat_app_eq (p := i ≫ toSpec A ι) (T := T.obj) ξ t
  let V' : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
    ⟨Over.mk (h ≫ T.obj.hom), LocallyOfFiniteType.isLocallyNoetherian h⟩
  let hV : V' ⟶ T := ObjectProperty.homMk (Over.homMk h rfl)
  obtain ⟨L, rfl⟩ :
      ∃ L : LineBundle (pullback (i ≫ toSpec A ι) V'.obj.hom), classOf _ L = a :=
    Quotient.exists_rep a
  have hL : ∀ w, (fineCondition i N e φ₀ ψ 0 (k + 1)).Holds V'.obj (classOf _ L) w := fun w =>
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).holdsAt_iff ξ hV.hom (classOf _ L) ha w).mp (hξ' _)
  obtain ⟨U, g, z, hgflat, hglfp, hgsurj, hz⟩ :=
    exists_lift_abelPreimageOver_of_forall_fineCondition_holds e k E L hL
  obtain ⟨w, rfl⟩ := hgsurj.surj v
  refine ⟨U, g ≫ hV, z, inferInstanceAs (Flat (g.hom.left ≫ h)),
    inferInstanceAs (LocallyOfFinitePresentation (g.hom.left ≫ h)),
    ⟨w, Scheme.Hom.comp_apply g.hom.left h w⟩, ?_⟩
  change (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map z.hom.op _ =
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (g ≫ hV).hom.op ξ
  refine hz.trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact congrArg (fun x => (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.hom.op x) ha

end AlgebraicGeometry.Scheme.RelativePicard.Strata
