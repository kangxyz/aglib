/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericRadicialEtale
public import Aglib.AlgebraicGeometry.FunctionField.Map

/-! # The actual affine-scheme generic radicial--etale factorization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteGenericFactorization

universe u

/-- Over a nonempty affine open of an integral Noetherian affine target, an
actual finite map from a reduced affine scheme factors as a finite surjective
radicial map followed by a finite etale map. The composite is the literal
original pullback projection, not merely an isomorphic algebraic model. -/
theorem exists_affine_open_finite_radicial_etale_factorization
    {Y X : Scheme.{u}} [IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    [IsAffine X] [IsIntegral X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f] :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ (B : Scheme.{u}) (r : pullback f U.ι ⟶ B) (g : B ⟶ U.toScheme),
        IsFinite r ∧ Surjective r ∧ UniversallyInjective r ∧
        IsFinite g ∧ Etale g ∧ r ≫ g = pullback.snd f U.ι := by
  let R := Γ(X, ⊤)
  let A := Γ(Y, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let p := Spec.map f.appTop
  have hp : p = Y.isoSpec.inv ≫ f ≫ X.isoSpec.hom := by
    apply (cancel_mono X.isoSpec.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      (Scheme.isoSpec_inv_naturality f)
  have : IsFinite p := by rw [hp]; infer_instance
  have : Module.Finite R A := (IsFinite.SpecMap_iff f.appTop).mp inferInstance
  obtain ⟨C, hC, hr, hsurj, hcomp, V, hVa, hV, het, hrad⟩ :=
    exists_subalgebra_affine_open_etale_radicial R A
  let a := Spec.map (CommRingCat.ofHom C.val.toRingHom)
  let b := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have : IsFinite a := hr
  have : Surjective a := hsurj
  have : Module.Finite R C := hC
  have : IsFinite b := (IsFinite.SpecMap_iff _).mpr hC
  have hab : a ≫ b = p := hcomp
  let Z := b ⁻¹ᵁ V
  let q := a ∣_ Z
  let t := b ∣_ V
  have : IsFinite q := inferInstanceAs (IsFinite (a ∣_ Z))
  have : UniversallyInjective q := hrad
  have : Surjective q := by
    let H := isPullback_morphismRestrict a Z
    have : Surjective (H.isoPullback.hom ≫ pullback.fst Z.ι a) := inferInstance
    simpa only [IsPullback.isoPullback_hom_fst] using this
  have : IsFinite t := inferInstanceAs (IsFinite (b ∣_ V))
  have : Etale t := het
  have Hlit : IsPullback (a ⁻¹ᵁ Z).ι (q ≫ t) p V.ι := by
    simpa only [hab] using
      (isPullback_morphismRestrict a Z).flip.paste_vert
        (isPullback_morphismRestrict b V).flip
  let U := X.isoSpec.hom ⁻¹ᵁ V
  let e : U.toScheme ≅ V.toScheme := asIso (X.isoSpec.hom ∣_ V)
  have he : e.inv ≫ U.ι = V.ι ≫ X.isoSpec.inv := by
    apply (cancel_mono X.isoSpec.hom).mp
    rw [Category.assoc, ← morphismRestrict_ι]
    simp only [e, asIso_inv, IsIso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have H : IsPullback ((a ⁻¹ᵁ Z).ι ≫ Y.isoSpec.inv)
      ((q ≫ t) ≫ e.inv) f U.ι :=
    Hlit.of_iso (Iso.refl _) Y.isoSpec.symm e.symm X.isoSpec.symm
      (by simp) (by simp) (by exact Scheme.isoSpec_inv_naturality f) he.symm
  let r := H.isoPullback.inv ≫ q
  let g := t ≫ e.inv
  have : IsFinite r := inferInstance
  have : Surjective r := inferInstance
  have : UniversallyInjective r :=
    MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance
  have : IsFinite g := inferInstance
  have : Etale g := inferInstance
  refine ⟨U, hVa.preimage X.isoSpec.hom, ?_, Z, r, g,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · change X.isoSpec.hom (genericPoint X) ∈ V
    rw [map_genericPoint_of_isDominant X X.isoSpec.hom]
    exact hV
  · simpa only [r, g, Category.assoc] using H.isoPullback_inv_snd

end AlgebraicGeometry.Scheme.FiniteGenericFactorization
