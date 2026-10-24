/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Functor
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Representability
public import Aglib.AlgebraicGeometry.Properties.Noetherian.Coproduct

/-!
# The disjoint union of Hilbert schemes of an immersed scheme

Let `A` be a ring, `ι ≃ Fin (n + 1)`, `i : Y ⟶ P^n_A` a preimmersion over `Spec A`
(`hi : i ≫ toSpec A ι = πY`) and `F` a set of polynomials. The Hilbert functor of `Y` with Hilbert
polynomials in `F` (`locallyNoetherianImmersedHilbertFunctorIn i hi F`,
`HilbertScheme/Coproduct/Functor`: closed subschemes `V ⊆ Y ×_{Spec A} T` proper and flat over
`T` whose images in `P^n_A ×_{Spec A} T` have all fibre Hilbert polynomials in `F`) is represented,
on locally Noetherian test schemes, by the disjoint union of the Hilbert schemes `Hilb^Φ_Y`,
`Φ ∈ F`.

**From representations of the pieces.** Let `E Φ` represent `Hilb^Φ_Y`
(`locallyNoetherianImmersedHilbertFunctor i hi Φ`) by `H Φ` for every `Φ ∈ F`, with universal
family `D^Φ = (E Φ).homEquiv (𝟙 _)`, and let `H_F = ∐_{Φ ∈ F} H Φ`
(`Scheme.LocallyNoetherianOver.sigma H`, `Properties/Noetherian/Coproduct`).

* `sigmaImmersedHilbertFamily E`: the family `D_F ⊆ Y ×_{Spec A} H_F` glued from the `D^Φ`
  (`Scheme.IdealSheafData.sigmaGlue`, `IdealSheaf/GlueCoproduct`); it restricts to `D^Φ` on
  `Y ×_{Spec A} H Φ` (`comap_sigmaImmersedHilbertFamily`) and is a point of the functor with
  polynomials in `F` (`isImmersedHilbertFamilyIn_sigmaImmersedHilbertFamily`).
* `eq_of_comap_sigmaImmersedHilbertFamily_eq` (**injectivity**): two morphisms `a, b : T ⟶ H_F`
  over `Spec A` from a locally Noetherian scheme with the same pulled-back family on
  `Y ×_{Spec A} T` are equal. The pulled-back family `V` has image with fibre polynomial `Φ`
  exactly over `a⁻¹(H Φ)` and over `b⁻¹(H Φ)`
  (`fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff`),
  so on the stratum `T_Φ` of the image of `V` (an open and closed subscheme,
  `HilbertScheme/Coproduct/Decomposition`) both factor through `H Φ`, where they agree by the
  injectivity of `E Φ`; morphisms out of `T` are determined on the strata
  (`hom_ext_of_flatteningStratumι_of_relativeFlat`).
* `exists_comap_sigmaImmersedHilbertFamily_eq` (**surjectivity**): every point `V` of the functor
  at a locally Noetherian `T` is the pullback of `D_F` along some `a : T ⟶ H_F` over `Spec A`. The
  restriction of `V` to the stratum `T_Φ` of its image is a point of `Hilb^Φ_Y(T_Φ)`
  (`isHilbertFamily_comap_flatteningStratumι`), hence the pullback of `D^Φ` along some
  `T_Φ ⟶ H Φ`; these assemble along the decomposition `∐_Φ T_Φ ≅ T`
  (`flatteningDecompositionIso`) and the families agree on the strata
  (`Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq`).
* `sigmaImmersedHilbertRepresentableBy E n e`: hence **`H_F` represents the Hilbert functor of `Y`
  with Hilbert polynomials in `F`** on locally Noetherian test schemes over `Spec A`, the point
  given by `a : T ⟶ H_F` being the pullback of `D_F`
  (`sigmaImmersedHilbertRepresentableBy_homEquiv_coe`).

**For the Hilbert schemes of `HilbertScheme/Immersed/Representability`.** For a Noetherian ring
`A`, an immersion `i` and, for every `Φ ∈ F`, a natural `r Φ ≥ hilbertRegularityBound n Φ` and
sections `φ Φ` of `𝒪(r Φ)` cutting out the scheme-theoretic image `i.ker`:

* `sigmaImmersedHilbertSchemeOver ι n e A r hr φ i`: `H_F = ∐_{Φ ∈ F} H^Φ_Y` with
  `H^Φ_Y = immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i`;
* `universalSigmaImmersedHilbertFamily`: the family `D_F` glued from the universal families
  `universalImmersedHilbertFamily` (`comap_universalSigmaImmersedHilbertFamily`), a point of the
  functor with polynomials in `F` (`isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily`);
  its image in `P^n_A ×_{Spec A} H_F` is glued from the images of the `D^Φ`
  (`map_universalSigmaImmersedHilbertFamily`), which are the restrictions of the universal family
  of the Hilbert scheme of `P^n_A` (`map_universalImmersedHilbertFamily`);
* `locallyNoetherianImmersedHilbertFunctorInRepresentableBy`: the representation, with
  `locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe` (the point given by `a`
  is the pullback of `D_F`) and the forms needed by the quotient construction:
  `eq_of_comap_universalSigmaImmersedHilbertFamily_eq` (injectivity on locally Noetherian `T`, for
  plain morphisms over `Spec A`), `exists_comap_universalSigmaImmersedHilbertFamily_eq`
  (classifying morphisms) and `surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem`
  (`D_F ⟶ H_F` is surjective when `0 ∉ F`);
* `exists_sigmaImmersedHilbertScheme_representableBy`: such `r`, `φ` exist for every set `F`
  (`exists_sectionPairing_imageIdealData_eq ι n e i.ker`,
  `HilbertScheme/ClosedSubscheme/Generation`; one bound works for all `Φ`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of
Thm 6.8, p. 33: "Let H be the finite disjoint union of the corresponding open subschemes
Hilb^{Φ,L}_{X/S} of Hilb_{X/S}", with "D ⊂ X ×_S H [...] the restriction to H of the universal
family over Hilb_{X/S}"; for all `Φ` at once, `Hilb_{X/S} = ∐_Φ Hilb^{Φ,L}_{X/S}` (§1, p. 4: "the
functor Quot_{E/X/S} naturally decomposes as a co-product", for `E = 𝒪_X`). Nitsure takes `H`
inside the Hilbert scheme `Hilb_{X/S}` of Thm 6.3; here the disjoint union is built directly from
the pieces and its representability is proved through the decomposition of the base by fibre
Hilbert polynomial (proof of Thm 4.3 (ii), p. 22, "the open and closed subscheme of T where the
Hilbert polynomial is f"), which is a route choice. The test schemes are locally Noetherian, as in
Nitsure §1, p. 3 (the category `Sch_S`). No finiteness of `F` is needed here; for finite `F`, `H_F`
is H-quasi-projective (`HilbertScheme/Coproduct/QuasiProjective`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {S Y : Scheme.{u}} (πY : Y ⟶ S)

/-- **Pulling back a family along a composite**: for `f : T' ⟶ T` and `a : T ⟶ G` over `S`, the
pullback of a closed subscheme of `Y ×_S G` along `Y ×_S T ⟶ Y ×_S G` and then along
`Y ×_S T' ⟶ Y ×_S T` is its pullback along `Y ×_S T' ⟶ Y ×_S G`, induced by `c = f ≫ a`. -/
theorem comap_pullbackMap_comap_pullbackMap {T' T G : Scheme.{u}} {gT' : T' ⟶ S} {gT : T ⟶ S}
    {gG : G ⟶ S} (I : (pullback πY gG).IdealSheafData) (f : T' ⟶ T) (a : T ⟶ G) (c : T' ⟶ G)
    (hc : f ≫ a = c) (hf : f ≫ gT = gT') (ha : a ≫ gG = gT) :
    (I.comap (pullback.map πY gT πY gG (𝟙 Y) a (𝟙 S) (by simp) (by simp [ha]))).comap
        (pullback.map πY gT' πY gT (𝟙 Y) f (𝟙 S) (by simp) (by simp [hf])) =
      I.comap (pullback.map πY gT' πY gG (𝟙 Y) c (𝟙 S) (by simp)
        (by rw [← hc, Category.assoc, ha, hf, Category.comp_id])) := by
  subst hc
  rw [← comap_comp, pullback.map_comp]
  simp only [Category.comp_id]

end Scheme.IdealSheafData

namespace ProjectiveSpace

open Scheme.Cohomology

section Pieces

variable {ι : Type u} {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πY)
  [IsPreimmersion i]

section Single

variable {Φ : ℚ[X]} {H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianImmersedHilbertFunctor i hi Φ).RepresentableBy H)

/-- A representation of `Hilb^Φ_Y` is injective on plain morphisms `T ⟶ H` over `Spec A` from a
locally Noetherian `T`: two such morphisms with the same pullback of the universal family agree. -/
private theorem eq_of_comap_homEquiv_id_eq {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) (b c : T ⟶ H.obj.left) (hb : b ≫ H.obj.hom = g)
    (hc : c ≫ H.obj.hom = g)
    (h : (E.homEquiv (𝟙 H)).1.comap (pullback.map πY g πY H.obj.hom (𝟙 Y) b (𝟙 _) (by simp)
        (by simp [hb])) =
      (E.homEquiv (𝟙 H)).1.comap (pullback.map πY g πY H.obj.hom (𝟙 Y) c (𝟙 _) (by simp)
        (by simp [hc]))) :
    b = c := by
  let T' : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
    ⟨Over.mk g, ‹IsLocallyNoetherian T›⟩
  let b' : T' ⟶ H := ObjectProperty.homMk (Over.homMk b hb)
  let c' : T' ⟶ H := ObjectProperty.homMk (Over.homMk c hc)
  have hbc : b' = c' := E.homEquiv.injective (Subtype.ext
    ((locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i hi E b').trans
      (h.trans (locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i hi E c').symm)))
  exact congrArg (fun x => x.hom.left) hbc

/-- A representation of `Hilb^Φ_Y` is surjective on plain morphisms: every point of `Hilb^Φ_Y` at a
locally Noetherian `T` over `Spec A` is the pullback of the universal family along some
`T ⟶ H` over `Spec A`. -/
private theorem exists_comap_homEquiv_id_eq {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData)
    (hV : IsImmersedHilbertFamily i hi Φ g V) :
    ∃ (b : T ⟶ H.obj.left) (hb : b ≫ H.obj.hom = g),
      (E.homEquiv (𝟙 H)).1.comap (pullback.map πY g πY H.obj.hom (𝟙 Y) b (𝟙 _) (by simp)
        (by simp [hb])) = V := by
  let T' : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
    ⟨Over.mk g, ‹IsLocallyNoetherian T›⟩
  obtain ⟨b', hb'⟩ := (E.homEquiv (X := T')).surjective ⟨V, hV⟩
  refine ⟨b'.hom.left, Over.w b'.hom, ?_⟩
  have h := locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i hi E b'
  rw [hb'] at h
  exact h.symm

end Single

section Sigma

variable {F : Set ℚ[X]} {H : F → Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : ∀ Φ : F, (locallyNoetherianImmersedHilbertFunctor i hi Φ).RepresentableBy (H Φ))

/-- **The universal family glued from the pieces**: for representations `E Φ` of `Hilb^Φ_Y` by
`H Φ`, `Φ ∈ F`, the closed subscheme `D_F ⊆ Y ×_{Spec A} ∐_Φ H Φ` glued from the universal families
`D^Φ = (E Φ).homEquiv (𝟙 _)`. -/
abbrev sigmaImmersedHilbertFamily :
    (pullback πY (Sigma.desc fun Φ : F => (H Φ).obj.hom)).IdealSheafData :=
  Scheme.IdealSheafData.sigmaGlue πY (fun Φ : F => (H Φ).obj.hom)
    fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1

/-- The glued universal family restricts to the universal family `D^Φ` on `Y ×_{Spec A} H Φ`. -/
theorem comap_sigmaImmersedHilbertFamily (Φ : F) :
    (sigmaImmersedHilbertFamily i hi E).comap
        (Scheme.pullbackSigmaι πY (fun Φ : F => (H Φ).obj.hom) Φ) =
      ((E Φ).homEquiv (𝟙 (H Φ))).1 :=
  Scheme.IdealSheafData.comap_sigmaGlue πY (fun Φ : F => (H Φ).obj.hom)
    (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) Φ

variable [Finite ι]

/-- **The glued universal family is a point of the Hilbert functor of `Y` with polynomials in
`F`**: it is proper and flat over `∐_Φ H Φ`, and its image has fibre polynomial `Φ` over `H Φ`. -/
theorem isImmersedHilbertFamilyIn_sigmaImmersedHilbertFamily :
    IsImmersedHilbertFamilyIn i hi F (Sigma.desc fun Φ : F => (H Φ).obj.hom)
      (sigmaImmersedHilbertFamily i hi E) :=
  isImmersedHilbertFamilyIn_sigmaGlue i hi (fun Φ : F => (H Φ).obj.hom)
    (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) (fun Φ : F => (Φ : ℚ[X])) (fun Φ => Φ.2)
    fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).2

/-- **Over the locus of polynomial `Φ` the classifying morphism lands in `H Φ`**: if
`c : T ⟶ ∐_Φ H Φ` over `Spec A` and `s : U ⟶ T` is such that the image of the pulled-back family
`c^* D_F` has fibre polynomial `Φ` at every point `s u`, then `s ≫ c` lands in the component `H Φ`
(`fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff`). -/
theorem range_comp_subset_range_sigmaι_of_fiberHilbertPolynomialAt_eq {T U : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (c : T ⟶ ∐ fun Φ : F => (H Φ).obj.left)
    (hc : c ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g) (s : U ⟶ T) (Φ : F)
    (hs : ∀ u, fiberHilbertPolynomialAt ι g (((sigmaImmersedHilbertFamily i hi E).comap
        (pullback.map πY g πY (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) c (𝟙 _) (by simp)
          (by simp [hc]))).map (immersionBaseChange i hi g)).quotientModule (s u) = Φ) :
    Set.range (s ≫ c) ⊆ Set.range (Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ) := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff i hi (fun Φ : F => (H Φ).obj.hom)
    (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) (Subtype.val : F → ℚ[X]) Subtype.val_injective
    (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).2) g c hc (s u) Φ).mp (hs u)

omit [Finite ι] in
/-- **Injectivity on a piece**: if `a, b : T ⟶ ∐_Φ H Φ` over `Spec A` pull the glued universal
family back to the same family and `s : U ⟶ T`, with `U` locally Noetherian, is such that `s ≫ a`
and `s ≫ b` both land in the component `H Φ`, then `s ≫ a = s ≫ b`: the two lifts to `H Φ` pull
the universal family `D^Φ` back to the same family on `U`, so they agree by the injectivity of
`E Φ`. -/
theorem comp_eq_comp_of_comap_sigmaImmersedHilbertFamily_eq {T U : Scheme.{u}}
    [IsLocallyNoetherian U] (g : T ⟶ Spec (CommRingCat.of A))
    (a b : T ⟶ ∐ fun Φ : F => (H Φ).obj.left)
    (ha : a ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g)
    (hb : b ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g)
    (h : (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
          (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a (𝟙 _) (by simp) (by simp [ha])) =
      (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
          (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) b (𝟙 _) (by simp) (by simp [hb])))
    (s : U ⟶ T) (Φ : F)
    (hsa : Set.range (s ≫ a) ⊆ Set.range (Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ))
    (hsb : Set.range (s ≫ b) ⊆ Set.range (Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ)) :
    s ≫ a = s ≫ b := by
  obtain ⟨a', ha'⟩ : ∃ a', a' ≫ Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ = s ≫ a :=
    ⟨IsOpenImmersion.lift _ _ hsa, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' ≫ Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ = s ≫ b :=
    ⟨IsOpenImmersion.lift _ _ hsb, IsOpenImmersion.lift_fac _ _ _⟩
  have ha'g : a' ≫ (H Φ).obj.hom = s ≫ g := by
    rw [← Sigma.ι_comp_desc (fun Φ : F => (H Φ).obj.hom) Φ, ← Category.assoc, ha',
      Category.assoc, ha]
  have hb'g : b' ≫ (H Φ).obj.hom = s ≫ g := by
    rw [← Sigma.ι_comp_desc (fun Φ : F => (H Φ).obj.hom) Φ, ← Category.assoc, hb',
      Category.assoc, hb]
  have key : a' = b' := by
    refine eq_of_comap_homEquiv_id_eq i hi (E Φ) (s ≫ g) a' b' ha'g hb'g ?_
    have h₁ := Scheme.IdealSheafData.comap_sigmaGlue_pullbackMap πY (fun Φ : F => (H Φ).obj.hom)
      (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) (s ≫ g) Φ a' ha'g
    have h₂ := Scheme.IdealSheafData.comap_sigmaGlue_pullbackMap πY (fun Φ : F => (H Φ).obj.hom)
      (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) (s ≫ g) Φ b' hb'g
    have h₃ := Scheme.IdealSheafData.comap_pullbackMap_comap_pullbackMap πY
      (sigmaImmersedHilbertFamily i hi E) s a _ ha'.symm rfl ha
    have h₄ := Scheme.IdealSheafData.comap_pullbackMap_comap_pullbackMap πY
      (sigmaImmersedHilbertFamily i hi E) s b _ hb'.symm rfl hb
    rw [h] at h₃
    exact h₁.symm.trans (h₃.symm.trans (h₄.trans h₂))
  rw [← ha', ← hb', key]

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **Injectivity** (the injectivity half of the representability of the Hilbert functor of `Y` with
polynomials in `F`): two morphisms `a, b : T ⟶ ∐_Φ H Φ` over `Spec A` from a locally Noetherian
scheme `T` along which the glued universal family has the same pullback to `Y ×_{Spec A} T` are
equal. On the stratum `T_Φ` of the image of the pulled-back family both land in `H Φ`
(`range_comp_subset_range_sigmaι_of_fiberHilbertPolynomialAt_eq`), where they agree
(`comp_eq_comp_of_comap_sigmaImmersedHilbertFamily_eq`); morphisms out of `T` are determined on
the strata (`hom_ext_of_flatteningStratumι_of_relativeFlat`). -/
theorem eq_of_comap_sigmaImmersedHilbertFamily_eq {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) (a b : T ⟶ ∐ fun Φ : F => (H Φ).obj.left)
    (ha : a ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g)
    (hb : b ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g)
    (h : (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
          (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a (𝟙 _) (by simp) (by simp [ha])) =
      (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
          (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) b (𝟙 _) (by simp) (by simp [hb]))) :
    a = b := by
  obtain ⟨V, hVa⟩ : ∃ V, (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
      (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a (𝟙 _) (by simp) (by simp [ha])) = V :=
    ⟨_, rfl⟩
  have hVb := h.symm.trans hVa
  have hV : IsImmersedHilbertFamilyIn i hi F g V :=
    hVa ▸ (isImmersedHilbertFamilyIn_sigmaImmersedHilbertFamily i hi E).comap a ha
  have := hV.isClosedImmersion
  obtain ⟨W, hW⟩ : ∃ W, V.map (immersionBaseChange i hi g) = W := ⟨_, rfl⟩
  have hWflat : Flat (W.subschemeι ≫ pullback.snd (toSpec A ι) g) := hW ▸ hV.flat_map
  have hWF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (pullback (toSpec A ι) g)
      W.quotientModule :=
    W.affineLocallyFiniteType_quotientModule
  have hrel := (W.relativeFlat_quotientModule_iff_flat _).mpr hWflat
  have hWP : ∀ t, fiberHilbertPolynomialAt ι g W.quotientModule t ∈ F :=
    fun t => hW ▸ hV.fiberHilbertPolynomialAt_mem t
  have hP : ∀ t, fiberHilbertPolynomialAt ι g W.quotientModule t ∈
      Set.range (Subtype.val : F → ℚ[X]) :=
    fun t => ⟨⟨_, hWP t⟩, rfl⟩
  refine hom_ext_of_flatteningStratumι_of_relativeFlat ι g n e hWF hrel
    (Subtype.val : F → ℚ[X]) Subtype.val_injective hP fun Φ => ?_
  have hz : ∀ z, fiberHilbertPolynomialAt ι g W.quotientModule
      (flatteningStratumι ι g n e hWF Φ z) = Φ := fun z => by
    have hz : flatteningStratumι ι g n e hWF Φ z ∈
        {t | fiberHilbertPolynomialAt ι g W.quotientModule t = Φ} := by
      rw [← range_flatteningStratumι ι g n e hWF Φ]
      exact ⟨z, rfl⟩
    exact hz
  refine comp_eq_comp_of_comap_sigmaImmersedHilbertFamily_eq i hi E g a b ha hb h
    (flatteningStratumι ι g n e hWF Φ) Φ
    (range_comp_subset_range_sigmaι_of_fiberHilbertPolynomialAt_eq i hi E g a ha
      (flatteningStratumι ι g n e hWF Φ) Φ fun z => ?_)
    (range_comp_subset_range_sigmaι_of_fiberHilbertPolynomialAt_eq i hi E g b hb
      (flatteningStratumι ι g n e hWF Φ) Φ fun z => ?_)
  · rw [hVa, hW]
    exact hz z
  · rw [hVb, hW]
    exact hz z

include e in
/-- **Surjectivity** (the surjectivity half of the representability): every point `V` of the
Hilbert functor of `Y` with polynomials in `F` at a locally Noetherian scheme `T` over `Spec A` is
the pullback of the glued universal family along some `a : T ⟶ ∐_Φ H Φ` over `Spec A`. -/
theorem exists_comap_sigmaImmersedHilbertFamily_eq {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData)
    (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    ∃ (a : T ⟶ ∐ fun Φ : F => (H Φ).obj.left)
      (ha : a ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g),
      (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY g πY
          (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a (𝟙 _) (by simp) (by simp [ha])) = V := by
  have := hV.isClosedImmersion
  obtain ⟨W, hW⟩ : ∃ W, V.map (immersionBaseChange i hi g) = W := ⟨_, rfl⟩
  have hWflat : Flat (W.subschemeι ≫ pullback.snd (toSpec A ι) g) := hW ▸ hV.flat_map
  have hWF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (pullback (toSpec A ι) g)
      W.quotientModule :=
    W.affineLocallyFiniteType_quotientModule
  have hrel := (W.relativeFlat_quotientModule_iff_flat _).mpr hWflat
  have hWP : ∀ t, fiberHilbertPolynomialAt ι g W.quotientModule t ∈ F :=
    fun t => hW ▸ hV.fiberHilbertPolynomialAt_mem t
  have hP : ∀ t, fiberHilbertPolynomialAt ι g W.quotientModule t ∈
      Set.range (Subtype.val : F → ℚ[X]) :=
    fun t => ⟨⟨_, hWP t⟩, rfl⟩
  have hopen : ∀ Φ : F, IsOpenImmersion (flatteningStratumι ι g n e hWF Φ) :=
    fun Φ => isOpenImmersion_flatteningStratumι_of_relativeFlat ι g n e hWF hrel Φ
  -- The restriction of `V` to the stratum of `Φ` is a point of `Hilb^Φ_Y`.
  have hVΦ : ∀ Φ : F, IsImmersedHilbertFamily i hi Φ (flatteningStratumι ι g n e hWF Φ ≫ g)
      (V.comap (pullback.map πY (flatteningStratumι ι g n e hWF Φ ≫ g) πY g (𝟙 Y)
        (flatteningStratumι ι g n e hWF Φ) (𝟙 _) (by simp) (by simp))) := fun Φ =>
    ⟨Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback @IsProper
        (Scheme.isPullback_pullbackMap_snd πY g _ (flatteningStratumι ι g n e hWF Φ) rfl) V
        hV.isProper, by
      rw [← comap_baseChangeMap_map_immersionBaseChange i hi g _
        (flatteningStratumι ι g n e hWF Φ) rfl V, hW]
      exact isHilbertFamily_comap_flatteningStratumι ι W n e hWF Φ⟩
  choose b hb hbV using fun Φ : F =>
    exists_comap_homEquiv_id_eq i hi (E Φ) (flatteningStratumι ι g n e hWF Φ ≫ g) _ (hVΦ Φ)
  let a : T ⟶ ∐ fun Φ : F => (H Φ).obj.left :=
    (flatteningDecompositionIso ι g n e hWF hrel (Subtype.val : F → ℚ[X]) Subtype.val_injective
      hP).inv ≫ Sigma.desc fun Φ => b Φ ≫ Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ
  have hja : ∀ Φ : F, flatteningStratumι ι g n e hWF Φ ≫ a =
      b Φ ≫ Sigma.ι (fun Φ : F => (H Φ).obj.left) Φ := fun Φ => by
    simp only [a, flatteningStratumι_flatteningDecompositionIso_inv_assoc, Sigma.ι_comp_desc]
  have ha : a ≫ Sigma.desc (fun Φ : F => (H Φ).obj.hom) = g := by
    refine hom_ext_of_flatteningStratumι_of_relativeFlat ι g n e hWF hrel
      (Subtype.val : F → ℚ[X]) Subtype.val_injective hP fun Φ => ?_
    rw [← Category.assoc, hja, Category.assoc, Sigma.ι_comp_desc, hb]
  refine ⟨a, ha, ?_⟩
  refine Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq πY g
    (fun Φ : F => flatteningStratumι ι g n e hWF Φ)
    (exists_flatteningStratumι_apply_eq ι g n e hWF (Subtype.val : F → ℚ[X]) hP) fun Φ => ?_
  exact (Scheme.IdealSheafData.comap_pullbackMap_comap_pullbackMap πY _
      (flatteningStratumι ι g n e hWF Φ) a _ (hja Φ) rfl ha).trans
    ((Scheme.IdealSheafData.comap_sigmaGlue_pullbackMap πY (fun Φ : F => (H Φ).obj.hom)
      (fun Φ => ((E Φ).homEquiv (𝟙 (H Φ))).1) _ Φ (b Φ) (hb Φ)).trans (hbV Φ))

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
include E e in
/-- **The disjoint union of the pieces represents the Hilbert functor of `Y` with Hilbert
polynomials in `F`** (Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33, and §1, p. 4): for a
preimmersion `i : Y ⟶ P^n_A` over `Spec A`, `ι ≃ Fin (n + 1)` and representations `E Φ` of the
Hilbert functors `Hilb^Φ_Y` by `H Φ` for `Φ ∈ F`, the disjoint union `∐_{Φ ∈ F} H Φ` represents
`locallyNoetherianImmersedHilbertFunctorIn i hi F` on locally Noetherian test schemes over `Spec A`.
A morphism `a` corresponds to the pullback of the glued universal family
`sigmaImmersedHilbertFamily E` along `Y ×_{Spec A} T ⟶ Y ×_{Spec A} ∐_Φ H Φ`. -/
def sigmaImmersedHilbertRepresentableBy :
    (locallyNoetherianImmersedHilbertFunctorIn i hi F).RepresentableBy
      (Scheme.LocallyNoetherianOver.sigma H) where
  homEquiv {T} := Equiv.ofBijective
    (fun a => ⟨(sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY T.obj.hom πY
        (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a.hom.left (𝟙 _) (by simp)
        ((Category.comp_id _).trans (Over.w a.hom).symm)),
      (isImmersedHilbertFamilyIn_sigmaImmersedHilbertFamily i hi E).comap a.hom.left
        (Over.w a.hom)⟩)
    ⟨fun a b hab => by
      have h := eq_of_comap_sigmaImmersedHilbertFamily_eq i hi E n e T.obj.hom a.hom.left
        b.hom.left (Over.w a.hom) (Over.w b.hom) (congrArg Subtype.val hab)
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact h,
    fun V => by
      obtain ⟨a, ha, haV⟩ := exists_comap_sigmaImmersedHilbertFamily_eq i hi E n e T.obj.hom V.1
        V.2
      exact ⟨ObjectProperty.homMk (Over.homMk a ha), Subtype.ext haV⟩⟩
  homEquiv_comp {T T'} f a := Subtype.ext (by
    change (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY T.obj.hom πY
        (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) (f.hom.left ≫ a.hom.left) (𝟙 _) _ _) =
      ((sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY T'.obj.hom πY
        (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a.hom.left (𝟙 _) _ _)).comap
          (pullback.map πY T.obj.hom πY T'.obj.hom (𝟙 Y) f.hom.left (𝟙 _) _ _)
    rw [← Scheme.IdealSheafData.comap_comp]
    congr 1
    apply pullback.hom_ext <;> simp [pullback.map])

/-- The representing equivalence sends `a : T ⟶ ∐_Φ H Φ` to the pullback of the glued universal
family along `Y ×_{Spec A} T ⟶ Y ×_{Spec A} ∐_Φ H Φ`. -/
theorem sigmaImmersedHilbertRepresentableBy_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ Scheme.LocallyNoetherianOver.sigma H) :
    ((sigmaImmersedHilbertRepresentableBy i hi E n e).homEquiv a).1 =
      (sigmaImmersedHilbertFamily i hi E).comap (pullback.map πY T.obj.hom πY
        (Sigma.desc fun Φ : F => (H Φ).obj.hom) (𝟙 Y) a.hom.left (𝟙 _) (by simp)
        ((Category.comp_id _).trans (Over.w a.hom).symm)) :=
  rfl

end Sigma

end Pieces

section Scheme

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {F : Set ℚ[X]} (r : F → ℕ)
  (hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ) {J : F → Type u}
  (φ : ∀ Φ : F, SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
    twistingSheaf A ι (r Φ : ℤ))
  {Y : Scheme.{u}} {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι)
  [IsImmersion i] (hi : i ≫ toSpec A ι = πY)

/-- **The disjoint union `H_F = ∐_{Φ ∈ F} H^Φ_Y` of the Hilbert schemes of an immersed `Y`**, as a
locally Noetherian test scheme over `Spec A`: the disjoint union of the Hilbert schemes
`H^Φ_Y = immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i` of
`HilbertScheme/Immersed/Representability`, `Φ ∈ F`, over `Spec A`. -/
abbrev sigmaImmersedHilbertSchemeOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  Scheme.LocallyNoetherianOver.sigma fun Φ : F =>
    immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i

/-- **The disjoint union `H_F = ∐_{Φ ∈ F} H^Φ_Y` of the Hilbert schemes of `Y`**, as a scheme. -/
abbrev sigmaImmersedHilbertScheme : Scheme.{u} :=
  (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.left

/-- **The universal family of `H_F`**: the closed subscheme `D_F ⊆ Y ×_{Spec A} H_F` glued from the
universal families `D^Φ = universalImmersedHilbertFamily … Φ …` of the Hilbert schemes `H^Φ_Y`
(`Scheme.IdealSheafData.sigmaGlue`). -/
def universalSigmaImmersedHilbertFamily :
    (pullback πY (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom).IdealSheafData :=
  Scheme.IdealSheafData.sigmaGlue πY
    (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
    fun Φ => universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi

/-- The universal family of `H_F` restricts to the universal family `D^Φ` of `H^Φ_Y` on
`Y ×_{Spec A} H^Φ_Y`. -/
theorem comap_universalSigmaImmersedHilbertFamily (Φ : F) :
    (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).comap (Scheme.pullbackSigmaι πY
        (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom) Φ) =
      universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi :=
  Scheme.IdealSheafData.comap_sigmaGlue πY
    (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
    (fun Φ => universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi) Φ

variable (hC : ∀ Φ : F, Scheme.Modules.Hom.imageIdealData (sectionPairing ι (r Φ) (φ Φ)) = i.ker)

include hC in
/-- The universal family of `H_F` is the family glued from the universal points of the
representations of the `Hilb^Φ_Y` (`sigmaImmersedHilbertFamily`, through
`universalImmersedHilbertPoint_coe`). -/
theorem universalSigmaImmersedHilbertFamily_eq_sigmaImmersedHilbertFamily :
    universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi =
      sigmaImmersedHilbertFamily i hi fun Φ : F =>
        locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi
          (hC Φ) := by
  refine (Scheme.IdealSheafData.eq_sigmaGlue_iff πY _ _ _).mpr fun Φ => ?_
  exact (comap_universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi Φ).trans
    (universalImmersedHilbertPoint_coe ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi (hC Φ)).symm

include hC in
/-- **The universal family of `H_F` is a point of the Hilbert functor of `Y` with Hilbert
polynomials in `F`**: it is proper and flat over `H_F`, and its image in
`P^n_A ×_{Spec A} H_F` has fibre Hilbert polynomial `Φ` over `H^Φ_Y`. -/
theorem isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily :
    IsImmersedHilbertFamilyIn i hi F (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom
      (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isImmersedHilbertFamilyIn_sigmaGlue i hi
    (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
    (fun Φ => universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi)
    (Subtype.val : F → ℚ[X]) (fun Φ => Φ.2)
    fun Φ => isImmersedHilbertFamily_universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i
      hi (hC Φ)

include hC in
/-- **The universal family of `H_F` is flat over `H_F`.** -/
theorem flat_universalSigmaImmersedHilbertFamily :
    Flat ((universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).subschemeι ≫
      pullback.snd πY (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom) :=
  (isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi hC).flat

include hC in
/-- **The universal family of `H_F` is proper over `H_F`.** -/
theorem isProper_universalSigmaImmersedHilbertFamily :
    IsProper ((universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).subschemeι ≫
      pullback.snd πY (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom) :=
  (isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi hC).isProper

include hC in
/-- **The universal family of `H_F` is surjective over `H_F` when `0 ∉ F`** (Nitsure,
arXiv:math/0504590v1, proof of Thm 6.8, p. 33, "Hence p : D → H is surjective"): every fibre of
its image has nonzero Hilbert polynomial, hence is nonempty
(`IsImmersedHilbertFamilyIn.surjective_of_zero_notMem`). -/
theorem surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem (h0 : (0 : ℚ[X]) ∉ F) :
    Surjective ((universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).subschemeι ≫
      pullback.snd πY (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom) :=
  (isImmersedHilbertFamilyIn_universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi
    hC).surjective_of_zero_notMem n e h0

include hC in
/-- **The disjoint union of the Hilbert schemes `H^Φ_Y`, `Φ ∈ F`, represents the Hilbert functor
of `Y` with Hilbert polynomials in `F`** (Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33,
"the finite disjoint union of the corresponding open subschemes Hilb^{Φ,L}_{X/S}", and §1, p. 4;
for `E = 𝒪_Y` and trivial bundles, on locally Noetherian test schemes): for a Noetherian ring
`A`, `ι ≃ Fin (n + 1)`, an immersion `i : Y ⟶ P^n_A` over `Spec A`, a set `F` of polynomials and,
for every `Φ ∈ F`, a natural `r Φ ≥ hilbertRegularityBound n Φ` and sections `φ Φ` of `𝒪(r Φ)`
whose section pairing cuts out the scheme-theoretic image `i.ker`, the functor
`locallyNoetherianImmersedHilbertFunctorIn i hi F` of closed subschemes `V ⊆ Y ×_{Spec A} T`
proper and flat over `T` whose images in `P^n_A ×_{Spec A} T` have all fibre Hilbert polynomials
in `F` is represented by `H_F = sigmaImmersedHilbertSchemeOver ι n e A r hr φ i`; a morphism
`a : T ⟶ H_F` corresponds to the pullback of the universal family
`universalSigmaImmersedHilbertFamily`
(`locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe`). -/
def locallyNoetherianImmersedHilbertFunctorInRepresentableBy [Finite ι] :
    (locallyNoetherianImmersedHilbertFunctorIn i hi F).RepresentableBy
      (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i) :=
  sigmaImmersedHilbertRepresentableBy i hi (fun Φ : F =>
    locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi
      (hC Φ)) n e

/-- The representing equivalence of `H_F` sends `a : T ⟶ H_F` to the pullback of the universal
family `D_F` along `Y ×_{Spec A} T ⟶ Y ×_{Spec A} H_F`. -/
theorem locallyNoetherianImmersedHilbertFunctorInRepresentableBy_homEquiv_coe [Finite ι]
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ sigmaImmersedHilbertSchemeOver ι n e A r hr φ i) :
    ((locallyNoetherianImmersedHilbertFunctorInRepresentableBy ι n e A r hr φ i hi hC).homEquiv
        a).1 =
      (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).comap (pullback.map πY T.obj.hom
        πY (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom (𝟙 Y) a.hom.left (𝟙 _)
        (by simp) ((Category.comp_id _).trans (Over.w a.hom).symm)) := by
  rw [universalSigmaImmersedHilbertFamily_eq_sigmaImmersedHilbertFamily ι n e A r hr φ i hi hC]
  rfl

include hC in
/-- **Points of `H_F` are determined by their families** (the injectivity field of the Hilbert
datum of the quotient construction, Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33): two
morphisms `a, b : T ⟶ H_F` over `Spec A` from a locally Noetherian scheme `T` along which the
universal family has the same pullback to `Y ×_{Spec A} T` are equal. -/
theorem eq_of_comap_universalSigmaImmersedHilbertFamily_eq [Finite ι] (T : Scheme.{u})
    [IsLocallyNoetherian T] (g : T ⟶ Spec (CommRingCat.of A))
    (a b : T ⟶ sigmaImmersedHilbertScheme ι n e A r hr φ i)
    (ha : a ≫ (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom = g)
    (hb : b ≫ (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom = g)
    (h : (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).comap (pullback.map πY g πY
          (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom (𝟙 Y) a (𝟙 _) (by simp)
          (by simp [ha])) =
      (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).comap (pullback.map πY g πY
          (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom (𝟙 Y) b (𝟙 _) (by simp)
          (by simp [hb]))) :
    a = b := by
  rw [universalSigmaImmersedHilbertFamily_eq_sigmaImmersedHilbertFamily ι n e A r hr φ i hi hC]
    at h
  exact eq_of_comap_sigmaImmersedHilbertFamily_eq i hi (fun Φ : F =>
    locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi
      (hC Φ)) n e g a b ha hb h

include hC in
/-- **Classifying morphisms to `H_F`**: every point `V` of the Hilbert functor of `Y` with Hilbert
polynomials in `F` at a locally Noetherian scheme `T` over `Spec A` is the pullback of the universal
family along some `a : T ⟶ H_F` over `Spec A` (Nitsure's `φ : X → H` with `φ^* D = R`,
arXiv:math/0504590v1, proof of Thm 6.8, p. 33). -/
theorem exists_comap_universalSigmaImmersedHilbertFamily_eq [Finite ι] {T : Scheme.{u}}
    [IsLocallyNoetherian T] (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback πY g).IdealSheafData) (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    ∃ (a : T ⟶ sigmaImmersedHilbertScheme ι n e A r hr φ i)
      (ha : a ≫ (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom = g),
      (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).comap (pullback.map πY g πY
          (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom (𝟙 Y) a (𝟙 _) (by simp)
          (by simp [ha])) = V := by
  rw [universalSigmaImmersedHilbertFamily_eq_sigmaImmersedHilbertFamily ι n e A r hr φ i hi hC]
  exact exists_comap_sigmaImmersedHilbertFamily_eq i hi (fun Φ : F =>
    locallyNoetherianImmersedHilbertFunctorRepresentableBy ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi
      (hC Φ)) n e g V hV

include hC in
/-- **The image of the universal family of `H_F`** in `P^n_A ×_{Spec A} H_F` is glued from the
images of the universal families of the `H^Φ_Y` (`map_sigmaGlue_immersionBaseChange`). -/
theorem map_universalSigmaImmersedHilbertFamily [Finite ι] :
    (universalSigmaImmersedHilbertFamily ι n e A r hr φ i hi).map
        (immersionBaseChange i hi (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom) =
      Scheme.IdealSheafData.sigmaGlue (toSpec A ι)
        (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
        fun Φ => (universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi).map
          (immersionBaseChange i hi
            (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom) :=
  map_sigmaGlue_immersionBaseChange i hi
    (fun Φ : F => (immersedHilbertSchemeOver ι n e A Φ (r Φ) (hr Φ) (φ Φ) i).obj.hom)
    (fun Φ => universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ) i hi)
    fun Φ => (isImmersedHilbertFamily_universalImmersedHilbertFamily ι n e A Φ (r Φ) (hr Φ) (φ Φ)
      i hi (hC Φ)).isProper

end Scheme

section Existence

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {Y : Scheme.{u}} {πY : Y ⟶ Spec (CommRingCat.of A)}
  (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (hi : i ≫ toSpec A ι = πY)

/-- **Existence of `H_F`** (Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33, with Thm 6.1,
p. 28, for each `Φ`): for a Noetherian ring `A`, an immersion `i : Y ⟶ P^n_A` over `Spec A` and
any set `F` of polynomials, there are naturals `r Φ ≥ hilbertRegularityBound n Φ` and sections
`φ Φ` of `𝒪(r Φ)` cutting out the scheme-theoretic image `i.ker`, for all `Φ ∈ F`, and then
`H_F = sigmaImmersedHilbertSchemeOver ι n e A r hr φ i` represents the Hilbert functor of `Y` with
Hilbert polynomials in `F` on locally Noetherian test schemes. One bound `m` of
`exists_sectionPairing_imageIdealData_eq ι n e i.ker` serves every `Φ`:
`r Φ = max (hilbertRegularityBound n Φ) m`. -/
theorem exists_sigmaImmersedHilbertScheme_representableBy [Finite ι] (F : Set ℚ[X]) :
    ∃ (r : F → ℕ) (hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ) (J : F → Type u)
      (φ : ∀ Φ : F, SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
        twistingSheaf A ι (r Φ : ℤ)),
      (∀ Φ : F, Scheme.Modules.Hom.imageIdealData (sectionPairing ι (r Φ) (φ Φ)) = i.ker) ∧
        Nonempty ((locallyNoetherianImmersedHilbertFunctorIn i hi F).RepresentableBy
          (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i)) := by
  obtain ⟨m, hm⟩ := exists_sectionPairing_imageIdealData_eq ι n e i.ker
  let r : F → ℕ := fun Φ => max (hilbertRegularityBound n Φ).toNat m.toNat
  have hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ := fun Φ =>
    (Int.self_le_toNat _).trans (by exact_mod_cast le_max_left _ _)
  have hmr : ∀ Φ : F, m ≤ (r Φ : ℤ) := fun Φ =>
    (Int.self_le_toNat m).trans (by exact_mod_cast le_max_right _ _)
  choose J φ hC using fun Φ : F => hm (r Φ) (hmr Φ)
  exact ⟨r, hr, J, φ, hC,
    ⟨locallyNoetherianImmersedHilbertFunctorInRepresentableBy ι n e A r hr φ i hi hC⟩⟩

end Existence

end ProjectiveSpace

end AlgebraicGeometry
