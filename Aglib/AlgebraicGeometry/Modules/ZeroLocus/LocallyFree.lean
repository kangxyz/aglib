/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Rank
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.ConstantRank
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.Quotient
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Order
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.EqualRank
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Quotient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# The zero scheme of a morphism into a finite locally free sheaf of constant rank

Let `X` be a scheme, `E` a finite locally free `𝒪_X`-module of constant rank `d`
(`Scheme.Modules.SheafHasRank E d`), `F` a quasi-coherent `𝒪_X`-module and `σ : F ⟶ E`. The
**zero scheme** `Z(σ) ⊆ X` is the closed subscheme cut out by the ideal sheaf
`Hom.zeroLocusIdeal σ d = Fitt_{d-1}(coker σ)` (with `Fitt_{-1} = 0`, `fittingIdealSheafPred`).

* `Hom.exists_lift_zeroLocusSchemeι_iff`: a morphism `g : T ⟶ X` factors through `Z(σ)` if and
  only if `g^* σ = 0`. Every scheme `T` is allowed.
* `Hom.zeroLocusIdeal_comap`: `Z(σ)` pulls back to `Z(f^* σ)` along every `f : Y ⟶ X`, as ideal
  sheaves: `(Hom.zeroLocusIdeal σ d).comap f = Hom.zeroLocusIdeal (f^* σ) d`.
* `Hom.zeroLocusIdeal_eq_bot_iff`: `Z(σ) = X` if and only if `σ = 0`.
* `Hom.zeroLocusIdeal_one_eq_imageIdealData`: for `E = 𝒪_X` (rank one, `sheafHasRank_unit`), the
  zero scheme is the image-ideal zero scheme `Hom.imageIdealData σ` of `Modules/ZeroLocus`, since
  both represent the vanishing of `g^* σ`.
* For a family of sections `s i : 𝒪_X ⟶ E`, `i ∈ I`, the zero scheme of
  `freeDesc s : 𝒪_X^{(I)} ⟶ E` represents the morphisms `g` along which every pulled-back
  section `g^* s_i` vanishes (`exists_lift_zeroLocusSchemeι_freeDesc_iff`; as elements of
  `Γ(T, g^* E)`, `exists_lift_zeroLocusSchemeι_freeDesc_iff_globalSections`), and it pulls back
  to the zero scheme of the pulled-back sections `𝒪_Y ≅ f^* 𝒪_X ⟶ f^* E`
  (`zeroLocusIdeal_freeDesc_comap`). The index type `I` is arbitrary.

**Sources and route.** Stacks Project, Tag 0FA8 (Section 42.44, in the text before Lemma
42.44.1; there `X` is locally of finite type over the base of Situation 42.7.1) defines the zero
scheme of a section `s` of a finite locally free `E` as the closed subscheme cut out by the image
of `s : E^∨ ⟶ 𝒪_X`. For an invertible `E` this is Tag 02OQ (Definition 31.15.8), and Tag 02OR
(Lemma 31.15.9 (2)) is the universal property: `f` factors through `Z(s)` if and only if
`f^* s = 0`. Section 42.44 does not state the universal property for finite locally free `E`.
Aglib has no dual of a general finite locally free sheaf with its pullback comparison, so the
ideal is taken from Fitting ideals instead. Locally `E ≅ 𝒪^d`, `coker σ` has a
presentation with relation matrix the coordinates of `σ`, and `Fitt_{d-1}(coker σ)` is generated
by these coordinates, the ideal of the dual map; this identification is not formalized here, and
`Z(σ)` is characterized by its universal property. That property is proved directly: `g` factors
through `V(Fitt_{d-1}(coker σ))` iff `Fitt_k(g^* coker σ) = 0` for `k < d` (Fitting ideals commute
with pullback, Stacks Project, Tags 07ZA (3) and 0C3D, `fittingIdealSheaf_comap`); since
`g^* coker σ` is a quotient of the rank-`d` sheaf `g^* E`, `Fitt_d(g^* coker σ) = 𝒪_T`, so this
holds iff `g^* coker σ` is finite locally free of rank `d` (Stacks Project, Tag 0C3G,
`fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank`), iff the epimorphism
`g^* E ⟶ g^* coker σ = coker (g^* σ)` between sheaves of rank `d` is an isomorphism
(`isIso_of_epi_of_sheafHasRank`), iff `g^* σ = 0`. The pullback formula then follows formally,
since a closed subscheme is determined by the morphisms that factor through it
(`IdealSheafData.eq_of_forall_comap_eq_bot_iff`).

The constant rank `d` is part of the data: a finite locally free sheaf of varying rank is not
covered (its rank strata are open and closed, so the construction can be applied on each of
them; this is not formalized). No Noetherian, flatness or finite-presentation hypothesis on `X`,
`F` or the test schemes is used.

Consumer: the closed subfunctor `Hilb^Φ_C` of the Hilbert functor of `P^n_A` for a closed
subscheme `C ⊆ P^n_A` (Picard plan, row F13; Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 5.4 (ii), p. 25, used for Theorem 6.1, p. 28), where this zero
scheme stands in for Nitsure's vanishing scheme (Remark 3.6, p. 17).

Relocation candidates: `IdealSheafData.le_of_comap_subschemeι_eq_bot`,
`IdealSheafData.eq_of_forall_comap_eq_bot_iff` and `pullback_map_comp_eq_zero_iff` are general
and may move to new sibling leaves under `IdealSheaf/` and `Modules/Pullback/`, not into the
widely imported `IdealSheaf/LocallyClosed`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace IdealSheafData

variable {X : Scheme.{u}}

/-- If `I` pulls back to zero along the closed immersion of `V(J)`, then `I ≤ J`. -/
theorem le_of_comap_subschemeι_eq_bot {I J : X.IdealSheafData}
    (h : I.comap J.subschemeι = ⊥) : I ≤ J := by
  have h' : I ≤ map ⊥ J.subschemeι := (map_gc J.subschemeι I ⊥).mp h.le
  rwa [map_bot, ker_subschemeι] at h'

/-- **A closed subscheme is determined by the morphisms factoring through it**: two ideal sheaves
that pull back to zero along the same morphisms are equal. -/
theorem eq_of_forall_comap_eq_bot_iff {I J : X.IdealSheafData}
    (h : ∀ (T : Scheme.{u}) (g : T ⟶ X), I.comap g = ⊥ ↔ J.comap g = ⊥) : I = J :=
  le_antisymm (le_of_comap_subschemeι_eq_bot ((h _ _).mpr (comap_subschemeι_self J)))
    (le_of_comap_subschemeι_eq_bot ((h _ _).mp (comap_subschemeι_self I)))

end IdealSheafData

namespace Modules

variable {X Y T : Scheme.{u}}

/-- Pulling back a morphism along a composite: `(g ≫ f)^* σ = 0` if and only if
`g^* (f^* σ) = 0`. -/
theorem pullback_map_comp_eq_zero_iff (g : T ⟶ Y) (f : Y ⟶ X) {F E : X.Modules} (σ : F ⟶ E) :
    (pullback (g ≫ f)).map σ = 0 ↔ (pullback g).map ((pullback f).map σ) = 0 := by
  have hnat : (pullback g).map ((pullback f).map σ) ≫ (pullbackComp g f).hom.app E =
      (pullbackComp g f).hom.app F ≫ (pullback (g ≫ f)).map σ :=
    (pullbackComp g f).hom.naturality σ
  constructor
  · intro h
    rw [← cancel_mono ((pullbackComp g f).hom.app E), hnat, h, comp_zero, zero_comp]
  · intro h
    rw [← cancel_epi ((pullbackComp g f).hom.app F), ← hnat, h, zero_comp, comp_zero]

namespace Hom

variable {F E : X.Modules} (σ : F ⟶ E)

/-- For `E` of constant rank `d`, the pullback `g^* (coker σ)` has constant rank `d` if and only
if `g^* σ = 0`: the epimorphism `g^* E ⟶ g^* (coker σ) = coker (g^* σ)` between sheaves of the
same constant rank is an isomorphism exactly when `g^* σ` vanishes. -/
theorem sheafHasRank_pullback_cokernel_iff {d : ℕ} (hE : SheafHasRank E d) (g : T ⟶ X) :
    SheafHasRank ((pullback g).obj (cokernel σ)) d ↔ (pullback g).map σ = 0 := by
  constructor
  · intro h
    have : IsIso ((pullback g).map (cokernel.π σ)) :=
      isIso_of_epi_of_sheafHasRank _ (sheafHasRank_pullback g hE) h
    rw [← cancel_mono ((pullback g).map (cokernel.π σ)), ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, zero_comp]
  · intro h
    have : IsIso ((pullback g).map (cokernel.π σ)) :=
      CokernelCofork.IsColimit.isIso_π _
        (CokernelCofork.mapIsColimit _ (cokernelIsCokernel σ) (pullback g)) h
    exact sheafHasRank_of_iso (asIso ((pullback g).map (cokernel.π σ)))
      (sheafHasRank_pullback g hE)

section Vanishing

variable [F.IsQuasicoherent] [IsFiniteLocallyFree X E]

/-- The cokernel of a morphism from a quasi-coherent sheaf to a finite locally free sheaf is
quasi-coherent of finite type. -/
theorem affineLocallyFiniteType_cokernel_of_isFiniteLocallyFree :
    QuasiCoherent.affineLocallyFiniteType X (cokernel σ) :=
  QuasiCoherent.affineLocallyFiniteType_cokernel σ
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation E)

/-- The ideal sheaf of the **zero scheme** of `σ : F ⟶ E`, for `E` finite locally free of constant
rank `d`: the Fitting ideal sheaf `Fitt_{d-1}(coker σ)`, with `Fitt_{-1} = 0`. -/
def zeroLocusIdeal (d : ℕ) : X.IdealSheafData :=
  fittingIdealSheafPred (cokernel σ) (affineLocallyFiniteType_cokernel_of_isFiniteLocallyFree σ) d

/-- The zero scheme `Z(σ)` of `σ : F ⟶ E`, for `E` finite locally free of constant rank `d`. -/
abbrev zeroLocusScheme (d : ℕ) : Scheme.{u} :=
  (zeroLocusIdeal σ d).subscheme

/-- The closed immersion `Z(σ) ⟶ X`. -/
abbrev zeroLocusSchemeι (d : ℕ) : zeroLocusScheme σ d ⟶ X :=
  (zeroLocusIdeal σ d).subschemeι

/-- For `E` of constant rank `d`, the `d`-th Fitting ideal sheaf of `coker σ` is the unit ideal
sheaf. -/
theorem fittingIdealSheaf_cokernel_eq_top {d : ℕ} (hE : SheafHasRank E d) :
    fittingIdealSheaf (cokernel σ) (affineLocallyFiniteType_cokernel_of_isFiniteLocallyFree σ) d =
      ⊤ := by
  have := QuasiCoherent.quasicoherent_cokernel σ
  have := QuasiCoherent.quasicoherent_kernel (cokernel.π σ)
  exact fittingIdealSheaf_eq_top_of_epi_of_sheafHasRank (cokernel.π σ)
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation E) _ hE

/-- **Universal property of the zero scheme, ideal form**: for `E` of constant rank `d` and any
`g : T ⟶ X`, the ideal sheaf of `Z(σ)` pulls back to zero along `g` if and only if `g^* σ = 0`. -/
theorem zeroLocusIdeal_comap_eq_bot_iff {d : ℕ} (hE : SheafHasRank E d) (g : T ⟶ X) :
    (zeroLocusIdeal σ d).comap g = ⊥ ↔ (pullback g).map σ = 0 := by
  have hQ := affineLocallyFiniteType_cokernel_of_isFiniteLocallyFree σ
  have : (cokernel σ).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel σ
  have : (kernel ((pullback g).map (cokernel.π σ))).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_kernel _
  have hgQ : QuasiCoherent.affineLocallyFiniteType T ((pullback g).obj (cokernel σ)) :=
    QuasiCoherent.affineLocallyFiniteType_of_epi ((pullback g).map (cokernel.π σ))
      (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation ((pullback g).obj E))
  have htop : fittingIdealSheaf ((pullback g).obj (cokernel σ)) hgQ d = ⊤ := by
    rw [← fittingIdealSheaf_comap g (cokernel σ) hQ hgQ, fittingIdealSheaf_cokernel_eq_top σ hE,
      IdealSheafData.comap_top]
  rw [zeroLocusIdeal, comap_fittingIdealSheafPred_eq_bot_iff,
    ← sheafHasRank_pullback_cokernel_iff σ hE g,
    ← fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank _ hgQ, and_iff_left htop]
  simp only [fittingIdealSheaf_comap g (cokernel σ) hQ hgQ]

/-- **Universal property of the zero scheme**: for `E` finite locally free of constant rank `d`,
a morphism `g : T ⟶ X` factors through the zero scheme `Z(σ)` if and only if `g^* σ = 0`. -/
theorem exists_lift_zeroLocusSchemeι_iff {d : ℕ} (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ zeroLocusScheme σ d, g' ≫ zeroLocusSchemeι σ d = g) ↔ (pullback g).map σ = 0 :=
  (IdealSheafData.exists_lift_subschemeι_iff _ g).trans (zeroLocusIdeal_comap_eq_bot_iff σ hE g)

/-- **Zero schemes are determined by their universal property**: if `σ : F ⟶ E` and
`σ' : F' ⟶ E'` (with `E`, `E'` of constant ranks `d`, `d'`) pull back to zero along the same
morphisms, their zero schemes agree. -/
theorem zeroLocusIdeal_eq_of_forall_iff {F' E' : X.Modules} (σ' : F' ⟶ E') [F'.IsQuasicoherent]
    [IsFiniteLocallyFree X E'] {d d' : ℕ} (hE : SheafHasRank E d) (hE' : SheafHasRank E' d')
    (h : ∀ (T : Scheme.{u}) (g : T ⟶ X), (pullback g).map σ = 0 ↔ (pullback g).map σ' = 0) :
    zeroLocusIdeal σ d = zeroLocusIdeal σ' d' :=
  IdealSheafData.eq_of_forall_comap_eq_bot_iff fun T g => by
    rw [zeroLocusIdeal_comap_eq_bot_iff σ hE, zeroLocusIdeal_comap_eq_bot_iff σ' hE', h]

/-- **The zero scheme pulls back to the zero scheme of the pullback**: for `E` finite locally free
of constant rank `d` and any `f : Y ⟶ X`, `Z(σ) ×_X Y = Z(f^* σ)`, as ideal sheaves on `Y`. -/
theorem zeroLocusIdeal_comap {d : ℕ} (hE : SheafHasRank E d) (f : Y ⟶ X) :
    (zeroLocusIdeal σ d).comap f = zeroLocusIdeal ((pullback f).map σ) d :=
  IdealSheafData.eq_of_forall_comap_eq_bot_iff fun T g => by
    rw [← IdealSheafData.comap_comp, zeroLocusIdeal_comap_eq_bot_iff σ hE,
      zeroLocusIdeal_comap_eq_bot_iff _ (sheafHasRank_pullback f hE),
      pullback_map_comp_eq_zero_iff]

/-- The zero scheme of `σ` is all of `X` if and only if `σ = 0`. -/
theorem zeroLocusIdeal_eq_bot_iff {d : ℕ} (hE : SheafHasRank E d) :
    zeroLocusIdeal σ d = ⊥ ↔ σ = 0 := by
  rw [← IdealSheafData.comap_id (zeroLocusIdeal σ d), zeroLocusIdeal_comap_eq_bot_iff σ hE]
  have hnat : (pullback (𝟙 X)).map σ ≫ (pullbackId X).hom.app E =
      (pullbackId X).hom.app F ≫ σ :=
    (pullbackId X).hom.naturality σ
  constructor
  · intro h
    rw [← cancel_epi ((pullbackId X).hom.app F), ← hnat, h, zero_comp, comp_zero]
  · intro h
    rw [← cancel_mono ((pullbackId X).hom.app E), hnat, h, comp_zero, zero_comp]

end Vanishing

end Hom

/-- The structure sheaf has constant rank one. -/
theorem sheafHasRank_unit (X : Scheme.{u}) :
    SheafHasRank (SheafOfModules.unit X.ringCatSheaf) 1 :=
  sheafHasRank_of_iso
    (coproductUniqueIso fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    ⟨(SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf) PUnit.{u + 1}).localGeneratorsData,
      inferInstance, fun _ => ⟨Equiv.ofUnique PUnit.{u + 1} (Fin 1)⟩⟩

instance isFiniteLocallyFree_unit (X : Scheme.{u}) :
    IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) :=
  (sheafHasRank_unit X).isFiniteLocallyFree

namespace Hom

/-- **For `E = 𝒪_X` the zero scheme is the image-ideal zero scheme**: for `σ : F ⟶ 𝒪_X` with `F`
quasi-coherent, `zeroLocusIdeal σ 1 = imageIdealData σ`; both pull back to zero exactly along the
morphisms `g` with `g^* σ = 0` (`zeroLocusIdeal_comap_eq_bot_iff`,
`Hom.imageIdealData_pullback`, `Hom.imageIdealData_eq_bot_iff`). -/
theorem zeroLocusIdeal_one_eq_imageIdealData {F : X.Modules} [F.IsQuasicoherent]
    (σ : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    zeroLocusIdeal σ 1 = imageIdealData σ :=
  IdealSheafData.eq_of_forall_comap_eq_bot_iff fun T g => by
    rw [zeroLocusIdeal_comap_eq_bot_iff σ (sheafHasRank_unit X) g,
      ← imageIdealData_pullback g σ, imageIdealData_eq_bot_iff, pullbackToUnit,
      Preadditive.IsIso.comp_right_eq_zero]

end Hom

section Sections

/-- A morphism from the structure sheaf vanishes if and only if its global section, the image of
`1`, vanishes. -/
theorem unitHom_eq_zero_iff {M : X.Modules}
    (τ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    τ = 0 ↔ τ.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = 0 := by
  let := moduleCategoryLinearOfHom X (RingHom.id Γ(X, ⊤))
  let : Module Γ(X, ⊤) (M.val.obj (Opposite.op ⊤)) := Module.compHom _ (RingHom.id Γ(X, ⊤))
  exact ((unitHomGlobalSectionsLinearEquivOfHom X (RingHom.id _) M).map_eq_zero_iff).symm

variable {E : X.Modules} {I : Type u}
  (s : I → ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ E))

/-- The morphism `𝒪_X^{(I)} ⟶ E` from the free sheaf on `I` whose components are the sections
`s i : 𝒪_X ⟶ E`. -/
def freeDesc : (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I) ⟶ E :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I) s

@[reassoc (attr := simp)]
theorem ιFree_freeDesc (i : I) : SheafOfModules.ιFree i ≫ freeDesc s = s i :=
  Cofan.IsColimit.fac _ _ i

/-- `g^*` of the morphism from the free sheaf vanishes if and only if every pulled-back section
`g^* s_i` vanishes. -/
theorem pullback_map_freeDesc_eq_zero_iff (g : T ⟶ X) :
    (pullback g).map (freeDesc s) = 0 ↔ ∀ i, (pullback g).map (s i) = 0 := by
  constructor
  · intro h i
    rw [← ιFree_freeDesc s i, Functor.map_comp, h, comp_zero]
  · intro h
    have : PreservesColimitsOfSize.{u, u} (pullback g) :=
      (pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
    refine (isColimitOfPreserves (pullback g) (SheafOfModules.isColimitFreeCofan I)).hom_ext
      fun ⟨i⟩ => ?_
    change (pullback g).map (SheafOfModules.ιFree i) ≫ (pullback g).map (freeDesc s) =
      (pullback g).map (SheafOfModules.ιFree i) ≫ 0
    rw [comp_zero, ← Functor.map_comp, ιFree_freeDesc, h i]

variable [IsFiniteLocallyFree X E]

/-- **Universal property of the zero scheme of finitely or infinitely many sections**: for `E`
finite locally free of constant rank `d` and sections `s i : 𝒪_X ⟶ E`, a morphism `g : T ⟶ X`
factors through the zero scheme of `freeDesc s` if and only if every pulled-back section
`g^* s_i` vanishes. -/
theorem exists_lift_zeroLocusSchemeι_freeDesc_iff {d : ℕ} (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ Hom.zeroLocusScheme (freeDesc s) d,
        g' ≫ Hom.zeroLocusSchemeι (freeDesc s) d = g) ↔
      ∀ i, (pullback g).map (s i) = 0 := by
  rw [Hom.exists_lift_zeroLocusSchemeι_iff _ hE, pullback_map_freeDesc_eq_zero_iff]

/-- The universal property of the zero scheme of sections, with the pulled-back sections as
global sections: `g` factors through the zero scheme of `freeDesc s` if and only if every
pulled-back section `g^* s_i ∈ Γ(T, g^* E)`, the image of `1` under
`𝒪_T ≅ g^* 𝒪_X ⟶ g^* E`, vanishes. -/
theorem exists_lift_zeroLocusSchemeι_freeDesc_iff_globalSections {d : ℕ}
    (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ Hom.zeroLocusScheme (freeDesc s) d,
        g' ≫ Hom.zeroLocusSchemeι (freeDesc s) d = g) ↔
      ∀ i, ((pullbackUnitIso g).inv ≫ (pullback g).map (s i)).val.app (Opposite.op ⊤)
        (1 : Γ(T, ⊤)) = 0 := by
  rw [exists_lift_zeroLocusSchemeι_freeDesc_iff s hE g]
  refine forall_congr' fun i => ?_
  rw [← unitHom_eq_zero_iff, Preadditive.IsIso.comp_left_eq_zero]

/-- **The zero scheme of sections pulls back to the zero scheme of the pulled-back sections**:
for `f : Y ⟶ X`, the zero scheme of `freeDesc s` pulls back to the zero scheme of the sections
`𝒪_Y ≅ f^* 𝒪_X ⟶ f^* E`. -/
theorem zeroLocusIdeal_freeDesc_comap {d : ℕ} (hE : SheafHasRank E d) (f : Y ⟶ X) :
    (Hom.zeroLocusIdeal (freeDesc s) d).comap f =
      Hom.zeroLocusIdeal (freeDesc fun i => (pullbackUnitIso f).inv ≫ (pullback f).map (s i))
        d := by
  have hfE := sheafHasRank_pullback f hE
  rw [Hom.zeroLocusIdeal_comap _ hE]
  refine Hom.zeroLocusIdeal_eq_of_forall_iff _ _ hfE hfE fun T g => ?_
  rw [← pullback_map_comp_eq_zero_iff, pullback_map_freeDesc_eq_zero_iff,
    pullback_map_freeDesc_eq_zero_iff]
  refine forall_congr' fun i => ?_
  rw [Functor.map_comp, Preadditive.IsIso.comp_left_eq_zero, pullback_map_comp_eq_zero_iff]

end Sections

end Modules

end AlgebraicGeometry.Scheme
