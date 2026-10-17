/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.LocalBase
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Localization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The structure sheaf after arbitrary base change of a proper flat geometrically integral morphism

Let `S` be locally Noetherian and `f : X ⟶ S` proper and flat with geometrically
integral fibres. For every `g : T ⟶ S`, with `φ = pullback.snd f g`, the original
structure map `φ.c : O_T ⟶ φ_* O_{X ×_S T}` is an isomorphism, and `φ.app V` is
bijective for every open `V` of `T` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Ex. 3.11, p. 25, in the geometrically integral case).

The proof localizes at points of the test scheme. For `t : T` over `s : S`, the
pullback of `X ×_S T` to `Spec O_{T,t}` is a pullback of `X ×_S Spec O_{S,s}` along
`Spec (g.stalkMap t)`, so the local-base theorem over the local Noetherian ring
`O_{S,s}` makes its structure map bijective. Mathlib's flat base change of sections
along the flat map `T.fromSpecStalk t` gives a pushout square of rings over each
affine open `V` containing `t`; localization at the maximal ideals of `Γ(T, V)` then
gives bijectivity of `φ.app V`. Affine opens form a basis, so `φ.c` is an
isomorphism of sheaves.

Finite presentation is not a hypothesis; the test scheme `T` is arbitrary.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X S T : Scheme.{u}} (f : X ⟶ S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- At a local ring of the test scheme: the base change of `X ×_S T` to `Spec O_{T,t}`
has bijective structure map on global functions. -/
theorem bijective_appTop_pullback_fromSpecStalk_of_isProper_of_flat_of_geometricallyIntegral
    (g : T ⟶ S) (t : T) :
    Function.Bijective (pullback.snd (pullback.snd f g) (T.fromSpecStalk t)).appTop := by
  let s := g t
  let ιs := S.fromSpecStalk s
  let R := S.presheaf.stalk s
  let fs : pullback f ιs ⟶ Spec (CommRingCat.of R) := pullback.snd f ιs
  have : IsProper fs := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have : Flat fs := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  have : GeometricallyIntegral fs :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance
  let φ := pullback.snd f g
  let ιt := T.fromSpecStalk t
  let a := pullback.fst φ ιt
  let q := pullback.snd φ ιt
  have hL : IsPullback a q φ ιt := IsPullback.of_hasPullback φ ιt
  have hR : IsPullback (pullback.fst f g) φ f g := IsPullback.of_hasPullback f g
  have heq : ιt ≫ g = Spec.map (g.stalkMap t) ≫ ιs :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk g).symm
  have hO : IsPullback (a ≫ pullback.fst f g) q f (Spec.map (g.stalkMap t) ≫ ιs) := by
    rw [← heq]
    exact hL.paste_horiz hR
  have hR2 : IsPullback (pullback.fst f ιs) fs f ιs := IsPullback.of_hasPullback f ιs
  have hsq := IsPullback.of_right' hO hR2
  exact Scheme.Cohomology.bijective_appTop_of_isPullback_of_proper_geometricallyIntegral_closedFibre
    (f := fs) (g.stalkMap t).hom hsq

/-- On every affine open `V` of the test scheme, the structure map
`Γ(T, V) → Γ(X ×_S T, φ⁻¹ V)` is bijective. -/
theorem bijective_app_pullback_snd_of_isAffineOpen_of_isProper_of_flat_of_geometricallyIntegral
    (g : T ⟶ S) {V : T.Opens} (hV : IsAffineOpen V) :
    Function.Bijective ((pullback.snd f g).app V) := by
  classical
  let φ := pullback.snd f g
  have : IsProper φ := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  let A := Γ(T, V)
  let C := Γ(pullback f g, φ ⁻¹ᵁ V)
  let := (φ.app V).hom.toAlgebra
  change Function.Bijective (Algebra.linearMap A C)
  refine bijective_of_localized_maximal (Algebra.linearMap A C) (fun P _ => ?_)
  let y : PrimeSpectrum A := ⟨P, inferInstance⟩
  let t : V := hV.isoSpec.inv y
  have hty : hV.primeIdealOf t = y := by
    change hV.isoSpec.hom (hV.isoSpec.inv y) = y
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  let ιt := T.fromSpecStalk t.1
  have hιV : ιt ⁻¹ᵁ V = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem ιt (by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact t.2)
  have hUST : (⊤ : (Spec (T.presheaf.stalk t.1)).Opens) ≤ ιt ⁻¹ᵁ V := hιV.ge
  have H : IsPullback (pullback.fst φ ιt) (pullback.snd φ ιt) φ ιt :=
    IsPullback.of_hasPullback φ ιt
  have hUY : (⊤ : (pullback φ ιt).Opens) =
      pullback.fst φ ιt ⁻¹ᵁ (φ ⁻¹ᵁ V) ⊓ pullback.snd φ ιt ⁻¹ᵁ ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, hιV]
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST le_rfl hUY hV
    (isAffineOpen_top _) (φ.isCompact_preimage hV.isCompact)
    (φ.isQuasiSeparated_preimage hV.isQuasiSeparated)
  have hPO := (isIso_pushoutSection_iff H hUST le_rfl hUY).mp hiso
  rw [Scheme.Hom.appLE_eq_app] at hPO
  have hB := bijective_appTop_pullback_fromSpecStalk_of_isProper_of_flat_of_geometricallyIntegral
    f g t.1
  have hψ' : Function.Bijective
      ((pullback.snd φ ιt).appLE ⊤ ⊤ (by rw [Scheme.Hom.preimage_top])) := by
    rw [show (pullback.snd φ ιt).appLE ⊤ ⊤ _ = (pullback.snd φ ιt).appTop from
      Scheme.Hom.appLE_eq_app _]
    exact hB
  have hι : ιt.appLE V ⊤ hUST =
      T.presheaf.germ V t.1 t.2 ≫ (Scheme.ΓSpecIso (T.presheaf.stalk t.1)).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app t.2, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    have h1 : ((homOfLE le_top).op ≫ (homOfLE hUST).op :
        (op ⊤ : (Spec (T.presheaf.stalk t.1)).Opensᵒᵖ) ⟶ op ⊤) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]
  have hP : letI := (ιt.appLE V ⊤ hUST).hom.toAlgebra
      IsLocalization.AtPrime Γ(Spec (T.presheaf.stalk t.1), ⊤) P := by
    rw [hι]
    have hloc := hV.isLocalization_stalk t
    rw [hty] at hloc
    exact (IsLocalization.isLocalization_iff_of_ringEquiv P.primeCompl
      (Scheme.ΓSpecIso (T.presheaf.stalk t.1)).symm.commRingCatIsoToRingEquiv).mp hloc
  exact CommRingCat.bijective_localizedModuleMap_of_isPushout hPO P hP hψ'

/-- **Universal O-connectedness.** For a proper flat morphism with geometrically
integral fibres over a locally Noetherian base, the original structure map
`O_T ⟶ φ_* O_{X ×_S T}` of `φ = pullback.snd f g` is an isomorphism for every
`g : T ⟶ S`. -/
theorem isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral (g : T ⟶ S) :
    IsIso (pullback.snd f g).c := by
  let φ := pullback.snd f g
  let F : T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} φ.base).obj
      (pullback f g).sheaf := ⟨φ.c⟩
  have hF : IsIso F := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : T.affineOpens => (U : T.Opens))
      ?_ ?_
    · rw [Subtype.range_coe]
      exact T.isBasis_affineOpens
    · intro U
      rw [ConcreteCategory.isIso_iff_bijective]
      exact bijective_app_pullback_snd_of_isAffineOpen_of_isProper_of_flat_of_geometricallyIntegral
        f g U.2
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map F))

/-- **Universal O-connectedness, sections form.** For every open `V` of every test scheme
`T`, the structure map `Γ(T, V) → Γ(X ×_S T, φ⁻¹ V)` is bijective. -/
theorem bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral
    (g : T ⟶ S) (V : T.Opens) :
    Function.Bijective ((pullback.snd f g).app V) := by
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral f g
  exact ConcreteCategory.bijective_of_isIso ((pullback.snd f g).c.app (op V))

end AlgebraicGeometry
