/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.PointPullback
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Subfunctor
public import Aglib.AlgebraicGeometry.HilbertScheme.OpenSubscheme
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# The Hilbert scheme of a locally closed subscheme of projective space

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `P = P^n_A = ProjectiveSpace A ι`, `Φ ∈ ℚ[X]`
and `i : Y ⟶ P` an immersion with `i ≫ toSpec A ι = πY`, so that `Y` is a locally closed
subscheme of `P^n_A`. Let `C = i.ker` be the scheme-theoretic image of `i` and
`U = i.coborderRange`; a closed subscheme of `P_T = P ×_{Spec A} T` lies in `Y_T` exactly when it
lies in `C_T` and in `U_T` (`HilbertScheme/Immersed/Subfunctor`; `i` is quasi-compact because `P`
is Noetherian). Fix a natural `r ≥ hilbertRegularityBound n Φ` and sections `φ : 𝒪^J ⟶ 𝒪(r)`
whose section pairing cuts out `C` (`hC : imageIdealData (sectionPairing ι r φ) = i.ker`; such `φ`
exist for all large `r`), so that the closed subscheme `H_C = closedHilbertScheme ι n e A Φ r hr φ`
of the Hilbert scheme `H` of `P^n_A` represents the Hilbert subfunctor of `C`
(`HilbertScheme/ClosedSubscheme/Representability`).

* `immersedHilbertSchemeOpens`: the open of `H_C` over which the universal family lies in `U`,
  the preimage under `H_C ⟶ H` of the open `openHilbertSchemeOpens ι n e A Φ r U` of
  `HilbertScheme/OpenSubscheme` (`mem_immersedHilbertSchemeOpens`);
* `immersedHilbertSchemeOver ι n e A Φ r hr φ i`: the corresponding open subscheme
  `H^Φ_Y = immersedHilbertScheme ι n e A Φ r hr φ i` of `H_C`, as a locally Noetherian test scheme
  over `Spec A`; it is Noetherian (`isNoetherian_immersedHilbertScheme`), and
  `immersedHilbertSchemeι : H^Φ_Y ⟶ H` is an immersion (`isImmersion_immersedHilbertSchemeι`;
  over `Spec A`, `immersedHilbertSchemeToHilbertScheme`) into the open `H^Φ_U`
  (`immersedHilbertSchemeι_preimage_openHilbertSchemeOpens`);
* `exists_lift_immersedHilbertSchemeι_iff`: **a morphism `a : T ⟶ H` from a locally Noetherian
  test scheme factors through `H^Φ_Y` if and only if the point of `Hilb^Φ(T)` given by `a` is
  contained in `Y`**: it factors through `H_C` exactly when the point lies in `C_T`
  (`exists_lift_closedHilbertSchemeι_iff`), and then through the open `H^Φ_Y` exactly when the
  point lies in `U_T` (`preimage_openHilbertSchemeOpens_eq_top_iff`);
* `locallyNoetherianImmersedHilbertSubfunctorRepresentableBy`: hence **`H^Φ_Y` represents the
  families of `Hilb^Φ` contained in `Y`** (`locallyNoetherianImmersedHilbertSubfunctor i hi Φ`)
  on locally Noetherian test schemes over `Spec A`; a morphism `a : T ⟶ H^Φ_Y` corresponds to the
  pullback of the universal family of `H` along `T ⟶ H^Φ_Y ⟶ H`
  (`locallyNoetherianImmersedHilbertSubfunctorRepresentableBy_homEquiv_coe`);
* `locallyNoetherianImmersedHilbertFunctorRepresentableBy`: **`H^Φ_Y` represents the Hilbert
  functor of `Y`** (`locallyNoetherianImmersedHilbertFunctor i hi Φ`, the closed subschemes of
  `Y ×_{Spec A} T` proper over `T` whose images in `P^n_A ×_{Spec A} T` are flat with Hilbert
  polynomials `Φ`), through `locallyNoetherianImmersedHilbertFunctorIso`, with universal family
  `universalImmersedHilbertFamily` (`D^Φ ⊆ Y ×_{Spec A} H^Φ_Y`, the pullback along the base change
  of `i` of the restricted universal family of `H`; `universalImmersedHilbertPoint_coe`), whose
  image in `P^n_A ×_{Spec A} H^Φ_Y` is the restriction of the universal family of `H`
  (`map_universalImmersedHilbertFamily`); it is a point of the Hilbert functor of `Y`
  (`isImmersedHilbertFamily_universalImmersedHilbertFamily`), and the point given by
  `a : T ⟶ H^Φ_Y` is its pullback along `Y ×_{Spec A} T ⟶ Y ×_{Spec A} H^Φ_Y`
  (`locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_eq_comap`);
* `exists_immersedHilbertScheme_representableBy`: for every large `r` such `φ` exist; the
  hypothesis `hC` itself is `exists_sectionPairing_imageIdealData_eq ι n e i.ker`
  (`HilbertScheme/ClosedSubscheme/Generation`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 6.1,
p. 28 (attributed there to Altman and Kleiman), for `E = 𝒪_Y` and trivial bundles `V`, `W`, on
the locally noetherian test schemes of §1, p. 3 (the category `Sch_S`; `Hilb_{X/S}` on p. 4). The
locally closed embedding into `H`, hence into a projective space over `Spec A`, gives
quasi-projectivity (`HilbertScheme/Immersed/QuasiProjective`). The route is Nitsure's: the Hilbert
functor of `Y` is an open subfunctor of that of its schematic closure `C` (the two Exercises on
p. 28 and the proof of Theorem 6.1 there; here `immersedHilbertSubfunctor_eq_inf` with the open
condition of `HilbertScheme/OpenSubscheme`), and that of `C` is represented by a closed subscheme
of `H` (p. 25, Lemma 5.4 (ii) and the remark after its proof;
`HilbertScheme/ClosedSubscheme/Representability`).
Nitsure identifies the Hilbert functor of a subscheme with families in the ambient scheme only
implicitly, for closed subschemes (p. 25, after Lemma 5.4) and for open subschemes of a proper
scheme (the second Exercise on p. 28); the one-step comparison along `i_T`
(`immersedHilbertFunctorIso`, `HilbertScheme/Immersed/Functor`) is a route choice.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.LocalRepresentability

section Scheme

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The open of the closed Hilbert scheme defining the Hilbert scheme of `Y`**: the preimage
under `closedHilbertSchemeι : H_C ⟶ H` of the open of the Hilbert scheme `H` over which the
universal family lies in `U = i.coborderRange` (`openHilbertSchemeOpens`). For `C = i.ker`, cut
out by the sections of `φ`, its points are those of `H_C` over which the universal family lies
in `Y = C ∩ U`. -/
def immersedHilbertSchemeOpens : (closedHilbertScheme ι n e A Φ r hr φ).Opens :=
  closedHilbertSchemeι ι n e A Φ r hr φ ⁻¹ᵁ openHilbertSchemeOpens ι n e A Φ r i.coborderRange

/-- **The Hilbert scheme of an immersed `Y`** as a locally Noetherian test scheme over `Spec A`:
the open subscheme `immersedHilbertSchemeOpens ι n e A Φ r hr φ i` of the Hilbert scheme `H_C` of
the closed subscheme cut out by `φ`. -/
def immersedHilbertSchemeOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  restrictOpens (closedHilbertSchemeOver ι n e A Φ r hr φ)
    (immersedHilbertSchemeOpens ι n e A Φ r hr φ i)

/-- **The Hilbert scheme `H^Φ_Y` of an immersed `Y`**, an open subscheme of the closed subscheme
`H_C` of the Hilbert scheme of `P^n_A`. -/
abbrev immersedHilbertScheme : Scheme.{u} :=
  (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.left

/-- The immersion `H^Φ_Y ⟶ H` of the Hilbert scheme of `Y` into the Hilbert scheme of `P^n_A`:
the open immersion into `H_C` followed by the closed immersion `H_C ⟶ H`. -/
def immersedHilbertSchemeι :
    immersedHilbertScheme ι n e A Φ r hr φ i ⟶ hilbertScheme ι n e A Φ r :=
  (immersedHilbertSchemeOpens ι n e A Φ r hr φ i).ι ≫ closedHilbertSchemeι ι n e A Φ r hr φ

/-- **The Hilbert scheme of `Y` is a locally closed subscheme of the Hilbert scheme of
`P^n_A`.** -/
instance isImmersion_immersedHilbertSchemeι :
    IsImmersion (immersedHilbertSchemeι ι n e A Φ r hr φ i) :=
  inferInstanceAs (IsImmersion ((immersedHilbertSchemeOpens ι n e A Φ r hr φ i).ι ≫
    closedHilbertSchemeι ι n e A Φ r hr φ))

/-- The Hilbert scheme of `Y` is Noetherian, as a locally closed subscheme of the Noetherian
Hilbert scheme. -/
instance isNoetherian_immersedHilbertScheme :
    IsNoetherian (immersedHilbertScheme ι n e A Φ r hr φ i) :=
  haveI : TopologicalSpace.NoetherianSpace (immersedHilbertScheme ι n e A Φ r hr φ i) :=
    (immersedHilbertSchemeι ι n e A Φ r hr φ i).isEmbedding.isInducing.noetherianSpace
  {}

/-- The immersion `H^Φ_Y ⟶ H` as a morphism of locally Noetherian test schemes over `Spec A`. -/
def immersedHilbertSchemeToHilbertScheme :
    immersedHilbertSchemeOver ι n e A Φ r hr φ i ⟶ hilbertSchemeOver ι n e A Φ r :=
  restrictOpensι (closedHilbertSchemeOver ι n e A Φ r hr φ)
      (immersedHilbertSchemeOpens ι n e A Φ r hr φ i) ≫
    closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ

theorem immersedHilbertSchemeToHilbertScheme_hom_left :
    (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom.left =
      immersedHilbertSchemeι ι n e A Φ r hr φ i :=
  rfl

/-- The Hilbert scheme of `Y` maps into the open `H^Φ_U` of the Hilbert scheme of `P^n_A` over
which the universal family lies in `U = i.coborderRange`. -/
theorem immersedHilbertSchemeι_preimage_openHilbertSchemeOpens :
    immersedHilbertSchemeι ι n e A Φ r hr φ i ⁻¹ᵁ
        openHilbertSchemeOpens ι n e A Φ r i.coborderRange = ⊤ :=
  Scheme.Opens.ι_preimage_self (immersedHilbertSchemeOpens ι n e A Φ r hr φ i)

variable {ι n e A Φ r hr φ i} in
/-- A point of the closed Hilbert scheme `H_C` lies in the Hilbert scheme of `Y` if and only if
every point of the universal family over its image in `H` lies in `U_H`. -/
theorem mem_immersedHilbertSchemeOpens (x : closedHilbertScheme ι n e A Φ r hr φ) :
    x ∈ immersedHilbertSchemeOpens ι n e A Φ r hr φ i ↔
      ∀ w ∈ (universalHilbertFamily ι n e A Φ r).support,
        pullback.snd (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w =
            closedHilbertSchemeι ι n e A Φ r hr φ x →
          pullback.fst (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w ∈ i.coborderRange :=
  mem_openHilbertSchemeOpens ι n e A Φ r i.coborderRange (closedHilbertSchemeι ι n e A Φ r hr φ x)

end Scheme

section Representability

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  {Y : Scheme.{u}} {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι)
  [IsImmersion i] (hi : i ≫ toSpec A ι = πY)

variable {ι n e A Φ r hr φ i} in
/-- **The locally closed condition** (Nitsure, arXiv:math/0504590v1, Theorem 6.1, p. 28, for
`E = 𝒪_Y`): for an immersion `i : Y ⟶ P^n_A` over `Spec A` and sections `φ` cutting out the
scheme-theoretic image `i.ker`, a morphism `a : T ⟶ H` from a locally Noetherian test scheme
factors through the Hilbert scheme `H^Φ_Y` if and only if the point of `Hilb^Φ(T)` given by `a` is
contained in `Y`. It factors through `H_C` exactly when the point lies in `C_T`
(`exists_lift_closedHilbertSchemeι_iff`), and then through the open `H^Φ_Y` exactly when the point
lies in `U_T` (`preimage_openHilbertSchemeOpens_eq_top_iff`); together these say that the point is
contained in `Y` (`mem_immersedHilbertSubfunctor_obj_iff_closed_and_open`). -/
theorem exists_lift_immersedHilbertSchemeι_iff
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (∃ c : T.obj.left ⟶ immersedHilbertScheme ι n e A Φ r hr φ i,
        c ≫ immersedHilbertSchemeι ι n e A Φ r hr φ i = a.hom.left) ↔
      (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a ∈
        (immersedHilbertSubfunctor i hi Φ).obj (op T.obj) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have := quasiCompact_of_isImmersion_of_isLocallyNoetherian i
  rw [mem_immersedHilbertSubfunctor_obj_iff_closed_and_open i hi Φ (T := op T.obj)]
  change _ ↔ i.ker.comap (pullback.fst (toSpec A ι) T.obj.hom) ≤
      ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a).1 ∧ _
  rw [← exists_lift_closedHilbertSchemeι_iff hr hC a]
  change _ ↔ _ ∧ ∀ x ∈ ((locallyNoetherianHilbertFunctor ι A Φ).map a.op
      (universalHilbertPoint ι n e A Φ r)).1.support,
        pullback.fst (toSpec A ι) T.obj.hom x ∈ i.coborderRange
  rw [← preimage_openHilbertSchemeOpens_eq_top_iff a]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c ≫ (immersedHilbertSchemeOpens ι n e A Φ r hr φ i).ι,
      (Category.assoc _ _ _).trans hc⟩, ?_⟩
    have h : (c ≫ immersedHilbertSchemeι ι n e A Φ r hr φ i) ⁻¹ᵁ
        openHilbertSchemeOpens ι n e A Φ r i.coborderRange = ⊤ := by
      rw [Scheme.Hom.comp_preimage, immersedHilbertSchemeι_preimage_openHilbertSchemeOpens,
        Scheme.Hom.preimage_top]
    exact (congrArg (fun f => f ⁻¹ᵁ openHilbertSchemeOpens ι n e A Φ r i.coborderRange)
      hc).symm.trans h
  · rintro ⟨⟨c, hc⟩, hU⟩
    have hcV : c ⁻¹ᵁ immersedHilbertSchemeOpens ι n e A Φ r hr φ i = ⊤ := by
      rw [immersedHilbertSchemeOpens, ← Scheme.Hom.comp_preimage]
      exact (congrArg (fun f => f ⁻¹ᵁ openHilbertSchemeOpens ι n e A Φ r i.coborderRange)
        hc).trans hU
    obtain ⟨d, hd⟩ : ∃ d : T.obj.left ⟶ immersedHilbertSchemeOpens ι n e A Φ r hr φ i,
        d ≫ (immersedHilbertSchemeOpens ι n e A Φ r hr φ i).ι = c :=
      ⟨IsOpenImmersion.lift _ c (range_subset_range_ι_of_preimage_eq_top c _ hcV),
        IsOpenImmersion.lift_fac _ _ _⟩
    refine ⟨d, ?_⟩
    rw [← hc, ← hd]
    exact (Category.assoc d (immersedHilbertSchemeOpens ι n e A Φ r hr φ i).ι
      (closedHilbertSchemeι ι n e A Φ r hr φ)).symm

/-- **The Hilbert scheme of an immersed `Y` represents the families of `Hilb^Φ` contained in `Y`**
(Nitsure, arXiv:math/0504590v1, Theorem 6.1, p. 28, for `E = 𝒪_Y` and trivial bundles): for a
Noetherian ring `A`, `ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, a natural `r ≥ hilbertRegularityBound n Φ`, an
immersion `i : Y ⟶ P^n_A` over `Spec A` and sections `φ : 𝒪^J ⟶ 𝒪(r)` whose section pairing cuts
out the scheme-theoretic image `i.ker`, the subfunctor of `Hilb^Φ` of the families contained in
`Y` is represented, on locally Noetherian test schemes over `Spec A`, by the open subscheme
`immersedHilbertSchemeOver ι n e A Φ r hr φ i` of the Hilbert scheme of `i.ker`. A morphism
`a : T ⟶ H^Φ_Y` corresponds to the point of `Hilb^Φ(T)` given by `T ⟶ H^Φ_Y ⟶ H`
(`exists_lift_immersedHilbertSchemeι_iff`). -/
def locallyNoetherianImmersedHilbertSubfunctorRepresentableBy
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (locallyNoetherianImmersedHilbertSubfunctor i hi Φ).toFunctor.RepresentableBy
      (immersedHilbertSchemeOver ι n e A Φ r hr φ i) where
  homEquiv {T} := Equiv.ofBijective
    (fun a => ⟨(locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i),
      (exists_lift_immersedHilbertSchemeι_iff hi hC
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i)).mp ⟨a.hom.left, rfl⟩⟩)
    ⟨fun a b hab => by
      have h₁ := (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv.injective
        (congrArg Subtype.val hab)
      have h₂ : a.hom.left ≫ immersedHilbertSchemeι ι n e A Φ r hr φ i =
          b.hom.left ≫ immersedHilbertSchemeι ι n e A Φ r hr φ i :=
        congrArg (fun c => c.hom.left) h₁
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact (cancel_mono (immersedHilbertSchemeι ι n e A Φ r hr φ i)).mp h₂,
    fun Z => by
      let a₀ := (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv.symm Z.1
      have hZ : (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a₀ ∈
          (immersedHilbertSubfunctor i hi Φ).obj (op T.obj) := by
        rw [Equiv.apply_symm_apply]
        exact Z.2
      obtain ⟨a', ha'⟩ := (exists_lift_immersedHilbertSchemeι_iff hi hC a₀).mpr hZ
      let a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i := ObjectProperty.homMk
        (Over.homMk a' (by
          rw [← Over.w (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom,
            ← Category.assoc]
          exact (congrArg (· ≫ (hilbertSchemeOver ι n e A Φ r).obj.hom) ha').trans
            (Over.w a₀.hom)))
      have ha : a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i = a₀ := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact ha'
      refine ⟨a, Subtype.ext ?_⟩
      change (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i) = Z.1
      rw [ha, Equiv.apply_symm_apply]⟩
  homEquiv_comp {T T'} f a := Subtype.ext (by
    change (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        ((f ≫ a) ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i) =
      (locallyNoetherianHilbertFunctor ι A Φ).map f.op
        ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
          (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i))
    rw [Category.assoc, Functor.RepresentableBy.homEquiv_comp])

/-- The representing equivalence sends `a : T ⟶ H^Φ_Y` to the pullback of the universal family of
the Hilbert scheme of `P^n_A` along `T ⟶ H^Φ_Y ⟶ H`. -/
theorem locallyNoetherianImmersedHilbertSubfunctorRepresentableBy_homEquiv_coe
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i) :
    ((locallyNoetherianImmersedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ i hi hC).homEquiv
        a : (locallyNoetherianHilbertFunctor ι A Φ).obj (op T)) =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).op
        (universalHilbertPoint ι n e A Φ r) :=
  rfl

/-- **Representability of the Hilbert functor of a locally closed subscheme of projective space**
(Nitsure, arXiv:math/0504590v1, Theorem 6.1, p. 28, for `E = 𝒪_Y` and trivial bundles `V`, `W`,
on the locally Noetherian test schemes of §1, pp. 3–4): for a Noetherian ring `A`,
`ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, a natural `r ≥ hilbertRegularityBound n Φ`, an immersion
`i : Y ⟶ P^n_A` over `Spec A` and sections `φ : 𝒪^J ⟶ 𝒪(r)` whose section pairing cuts out the
scheme-theoretic image `i.ker`, the Hilbert functor of `Y` (closed subschemes of
`Y ×_{Spec A} T` proper over `T` whose images in `P^n_A ×_{Spec A} T` are flat over `T` with
fibre Hilbert polynomials `Φ`) on locally Noetherian test schemes over `Spec A` is represented by
the scheme `immersedHilbertSchemeOver ι n e A Φ r hr φ i`, a locally closed subscheme of the
Hilbert scheme of `P^n_A` (`isImmersion_immersedHilbertSchemeι`). -/
def locallyNoetherianImmersedHilbertFunctorRepresentableBy
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (locallyNoetherianImmersedHilbertFunctor i hi Φ).RepresentableBy
      (immersedHilbertSchemeOver ι n e A Φ r hr φ i) :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  (locallyNoetherianImmersedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ i hi hC).ofIso
    (locallyNoetherianImmersedHilbertFunctorIso i hi Φ).symm

/-- The representing equivalence of the Hilbert functor of `Y` sends `a : T ⟶ H^Φ_Y` to the
pullback along `i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` of the pullback of the universal family
of the Hilbert scheme of `P^n_A` along `T ⟶ H^Φ_Y ⟶ H`. -/
theorem locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_coe
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i hi hC).homEquiv
        a).1 =
      ((locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).op
        (universalHilbertPoint ι n e A Φ r)).1.comap (immersionBaseChange i hi T.obj.hom) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  change ((locallyNoetherianImmersedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ i hi
    hC).homEquiv a).1.1.comap (immersionBaseChange i hi T.obj.hom) = _
  rw [locallyNoetherianImmersedHilbertSubfunctorRepresentableBy_homEquiv_coe]

/-- **The universal family of the Hilbert scheme of `Y`**: the closed subscheme
`D^Φ ⊆ Y ×_{Spec A} H^Φ_Y`, the pullback along the base change of `i` of the restriction to
`H^Φ_Y` of the universal family of the Hilbert scheme of `P^n_A`. -/
def universalImmersedHilbertFamily :
    (pullback πY (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom).IdealSheafData :=
  ((universalHilbertFamily ι n e A Φ r).comap
    (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
      (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
      (immersedHilbertSchemeι ι n e A Φ r hr φ i)
      (Over.w (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom))).comap
    (immersionBaseChange i hi (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom)

/-- **The universal point of the Hilbert functor of `Y`**: the point corresponding to the identity
of `H^Φ_Y` (`universalImmersedHilbertPoint_coe`). -/
def universalImmersedHilbertPoint
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (locallyNoetherianImmersedHilbertFunctor i hi Φ).obj
      (op (immersedHilbertSchemeOver ι n e A Φ r hr φ i)) :=
  (locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i hi hC).homEquiv (𝟙 _)

/-- The universal point of the Hilbert functor of `Y` is the universal family
`universalImmersedHilbertFamily`. -/
theorem universalImmersedHilbertPoint_coe
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (universalImmersedHilbertPoint ι n e A Φ r hr φ i hi hC).1 =
      universalImmersedHilbertFamily ι n e A Φ r hr φ i hi := by
  rw [universalImmersedHilbertPoint,
    locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_coe, Category.id_comp]
  rfl

/-- **The point given by `a : T ⟶ H^Φ_Y` is the pullback of the universal family**: under the
representation of the Hilbert functor of `Y`, `a` corresponds to the pullback of
`universalImmersedHilbertFamily` along
`pullback.map πY _ πY _ (𝟙 Y) a (𝟙 _) : Y ×_{Spec A} T ⟶ Y ×_{Spec A} H^Φ_Y`
(`locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap`,
`HilbertScheme/Immersed/PointPullback`, followed by `universalImmersedHilbertPoint_coe`). -/
theorem locallyNoetherianImmersedHilbertFunctorRepresentableBy_homEquiv_eq_comap
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ immersedHilbertSchemeOver ι n e A Φ r hr φ i) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i hi hC).homEquiv
        a).1 =
      (universalImmersedHilbertFamily ι n e A Φ r hr φ i hi).comap
        (pullback.map πY T.obj.hom πY (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
          (𝟙 Y) a.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w a.hom])) := by
  rw [locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i hi
    (locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i hi hC) a]
  exact congrArg (fun V => Scheme.IdealSheafData.comap V
      (pullback.map πY T.obj.hom πY (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
        (𝟙 Y) a.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w a.hom])))
    (universalImmersedHilbertPoint_coe ι n e A Φ r hr φ i hi hC)

/-- **The universal family of `Y` is a point of the Hilbert functor of `Y`**: a closed subscheme
of `Y ×_{Spec A} H^Φ_Y`, proper over `H^Φ_Y`, whose image in `P^n_A ×_{Spec A} H^Φ_Y` is flat with
fibre Hilbert polynomials `Φ`. -/
theorem isImmersedHilbertFamily_universalImmersedHilbertFamily
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    IsImmersedHilbertFamily i hi Φ (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
      (universalImmersedHilbertFamily ι n e A Φ r hr φ i hi) := by
  have h := (universalImmersedHilbertPoint ι n e A Φ r hr φ i hi hC).2
  rw [universalImmersedHilbertPoint_coe] at h
  exact h

/-- **The image of the universal family of `Y`** in `P^n_A ×_{Spec A} H^Φ_Y` is the restriction to
`H^Φ_Y` of the universal family of the Hilbert scheme of `P^n_A`. -/
theorem map_universalImmersedHilbertFamily
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (universalImmersedHilbertFamily ι n e A Φ r hr φ i hi).map
        (immersionBaseChange i hi (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom) =
      (universalHilbertFamily ι n e A Φ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
          (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom
          (immersedHilbertSchemeι ι n e A Φ r hr φ i)
          (Over.w (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have h := map_comap_immersionBaseChange_of_mem i hi Φ
    (T := op (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj)
    ((locallyNoetherianImmersedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ i hi hC).homEquiv
      (𝟙 _)).2
  rw [locallyNoetherianImmersedHilbertSubfunctorRepresentableBy_homEquiv_coe,
    Category.id_comp] at h
  exact h

end Representability

section Existence

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) {Y : Scheme.{u}} {πY : Y ⟶ Spec (CommRingCat.of A)}
  (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (hi : i ≫ toSpec A ι = πY)

/-- **Existence of the Hilbert scheme of a locally closed subscheme of projective space** (Nitsure,
arXiv:math/0504590v1, Theorem 6.1, p. 28, for `E = 𝒪_Y` and trivial bundles, on locally
Noetherian test schemes): for a Noetherian ring `A` and an immersion `i : Y ⟶ P^n_A` over
`Spec A`, for every large enough natural `r` there are sections `φ` of `𝒪(r)` cutting out the
scheme-theoretic image of `i`, and then `immersedHilbertSchemeOver ι n e A Φ r hr φ i` represents
the Hilbert functor of `Y`. The sections, with the hypothesis `hC` of the representations, come
from `exists_sectionPairing_imageIdealData_eq ι n e i.ker`
(`HilbertScheme/ClosedSubscheme/Generation`); consumers that need `hC` itself (the lifting
criterion, the universal family) take it from there. -/
theorem exists_immersedHilbertScheme_representableBy :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ (hr : hilbertRegularityBound n Φ ≤ r) (J : Type u)
      (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
        twistingSheaf A ι (r : ℤ)),
      Nonempty ((locallyNoetherianImmersedHilbertFunctor i hi Φ).RepresentableBy
        (immersedHilbertSchemeOver ι n e A Φ r hr φ i)) := by
  obtain ⟨m, hm⟩ := exists_sectionPairing_imageIdealData_eq ι n e i.ker
  refine ⟨max (hilbertRegularityBound n Φ).toNat m.toNat, fun r hr₀ => ?_⟩
  have hr : hilbertRegularityBound n Φ ≤ r :=
    (Int.self_le_toNat _).trans (by exact_mod_cast le_trans (le_max_left _ _) hr₀)
  have hmr : m ≤ (r : ℤ) :=
    (Int.self_le_toNat m).trans (by exact_mod_cast le_trans (le_max_right _ _) hr₀)
  obtain ⟨J, φ, hC⟩ := hm r hmr
  exact ⟨hr, J, φ,
    ⟨locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ r hr φ i hi hC⟩⟩

end Existence

end AlgebraicGeometry.ProjectiveSpace
