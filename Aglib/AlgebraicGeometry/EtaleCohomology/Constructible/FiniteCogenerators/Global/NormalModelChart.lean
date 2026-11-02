/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.FieldNormalization
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Original normal generic models globalize through relative normalization

An integral normal model over an open subscheme is an actual open chart of the
normalization of its original generic field point over the whole base. Native
universal and smooth-base-change comparisons preserve the original structural
and generic triangles. The whole normalization can be infinite over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

/-- The original factorization through a monomorphism identifies its actual
pullback source with the original source. -/
def factorPullbackIso {K U X : Scheme.{u}} (p : K ⟶ U) (j : U ⟶ X) [Mono j] :
    K ≅ pullback (p ≫ j) j := by
  let e := (asIso (pullback.fst (p ≫ j) j)).symm
  have hhom : pullback.lift (𝟙 K) p (by simp) = e.hom := by
    apply (cancel_mono (pullback.fst (p ≫ j) j)).mp
    exact (pullback.lift_fst _ _ _).trans e.hom_inv_id.symm
  exact {
    hom := pullback.lift (𝟙 K) p (by simp)
    inv := e.inv
    hom_inv_id := pullback.lift_fst _ _ _
    inv_hom_id := by rw [hhom]; exact e.inv_hom_id }

@[reassoc]
theorem factorPullbackIso_hom_fst {K U X : Scheme.{u}}
    (p : K ⟶ U) (j : U ⟶ X) [Mono j] :
    (factorPullbackIso p j).hom ≫ pullback.fst (p ≫ j) j = 𝟙 K := by
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem factorPullbackIso_hom_snd {K U X : Scheme.{u}}
    (p : K ⟶ U) (j : U ⟶ X) [Mono j] :
    (factorPullbackIso p j).hom ≫ pullback.snd (p ≫ j) j = p := by
  exact pullback.lift_snd _ _ _

section NormalIntegral

variable {T U X : Scheme.{u}} [IsIntegral T]
  [∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)]
  (g : T ⟶ U) [IsIntegralHom g]

/-- An integral normal scheme is the relative normalization of its original
generic field point over the supplied base. Finiteness is not asserted. -/
def normalGenericIntegralFactorIso :
    (T.fromSpecStalk (genericPoint T) ≫ g).normalization ≅ T := by
  let η := T.fromSpecStalk (genericPoint T)
  let p := η ≫ g
  have : IsIso (p.normalizationDesc η g rfl) :=
    Scheme.Hom.normalizationDesc_isIso p η g rfl
  exact asIso (p.normalizationDesc η g rfl)

@[reassoc]
theorem normalGenericIntegralFactorIso_hom_over :
    (normalGenericIntegralFactorIso g).hom ≫ g =
      (T.fromSpecStalk (genericPoint T) ≫ g).fromNormalization := by
  exact Scheme.Hom.normalizationDesc_comp _ _ _ rfl

@[reassoc]
theorem normalGenericIntegralFactorIso_generic :
    (T.fromSpecStalk (genericPoint T) ≫ g).toNormalization ≫
        (normalGenericIntegralFactorIso g).hom = T.fromSpecStalk (genericPoint T) := by
  exact Scheme.Hom.toNormalization_normalizationDesc _ _ _ rfl

/-- The original affine normal integral factor occurs as an actual open chart
of the whole-base relative normalization. -/
def normalGenericOpenChart (j : U ⟶ X) [IsOpenImmersion j] :
    T ⟶ ((T.fromSpecStalk (genericPoint T) ≫ g) ≫ j).normalization :=
  let p := T.fromSpecStalk (genericPoint T) ≫ g
  let e := factorPullbackIso p j
  (normalGenericIntegralFactorIso g).inv ≫
    (Scheme.Hom.normalizationSourceIso e p (pullback.snd (p ≫ j) j)
      (factorPullbackIso_hom_snd p j)).hom ≫
    (p ≫ j).normalizationPullback j ≫ pullback.fst (p ≫ j).fromNormalization j

instance normalGenericOpenChart_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] :
    IsOpenImmersion (normalGenericOpenChart g j) := by
  dsimp [normalGenericOpenChart]
  infer_instance

/-- The original source generic point maps into the whole-base normalization
through exactly the supplied chart. -/
@[reassoc]
theorem normalGenericOpenChart_generic (j : U ⟶ X) [IsOpenImmersion j] :
    T.fromSpecStalk (genericPoint T) ≫ normalGenericOpenChart g j =
      ((T.fromSpecStalk (genericPoint T) ≫ g) ≫ j).toNormalization := by
  let η := T.fromSpecStalk (genericPoint T)
  let p := η ≫ g
  let f := p ≫ j
  let e := factorPullbackIso p j
  let eN := Scheme.Hom.normalizationSourceIso e p (pullback.snd f j)
    (factorPullbackIso_hom_snd p j)
  let n := f.normalizationPullback j
  let q := pullback.fst f.fromNormalization j
  have hη : η ≫ (normalGenericIntegralFactorIso g).inv = p.toNormalization := by
    apply (cancel_mono (normalGenericIntegralFactorIso g).hom).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => η ≫ k) (Iso.inv_hom_id _)).trans
        ((Category.comp_id _).trans (normalGenericIntegralFactorIso_generic g).symm))
  have heN : p.toNormalization ≫ eN.hom =
      e.hom ≫ (pullback.snd f j).toNormalization :=
    Scheme.Hom.normalizationSourceIso_hom_generic e p (pullback.snd f j)
      (factorPullbackIso_hom_snd p j)
  have hn : (pullback.snd f j).toNormalization ≫ n ≫ q =
      pullback.fst f j ≫ f.toNormalization :=
    Scheme.Hom.toNormalization_normalizationPullback_fst f j
  let t := (normalGenericIntegralFactorIso g).inv
  let r := (pullback.snd f j).toNormalization
  let s := pullback.fst f j
  change η ≫ (t ≫ (eN.hom ≫ (n ≫ q))) = _
  exact (Category.assoc η t (eN.hom ≫ (n ≫ q))).symm.trans
    ((congrArg (fun k => k ≫ (eN.hom ≫ (n ≫ q))) hη).trans
      ((Category.assoc p.toNormalization eN.hom (n ≫ q)).symm.trans
        ((congrArg (fun k => k ≫ (n ≫ q)) heN).trans
          ((Category.assoc e.hom r (n ≫ q)).trans
            ((congrArg (fun k => e.hom ≫ k) hn).trans
              ((Category.assoc e.hom s f.toNormalization).symm.trans
                ((congrArg (fun k => k ≫ f.toNormalization)
                  (factorPullbackIso_hom_fst p j)).trans
                    (Category.id_comp f.toNormalization))))))))

/-- The whole original structural triangle of the chart. -/
@[reassoc]
theorem normalGenericOpenChart_over (j : U ⟶ X) [IsOpenImmersion j] :
    normalGenericOpenChart g j ≫
        ((T.fromSpecStalk (genericPoint T) ≫ g) ≫ j).fromNormalization = g ≫ j := by
  let p := T.fromSpecStalk (genericPoint T) ≫ g
  let f := p ≫ j
  let e := factorPullbackIso p j
  let eN := Scheme.Hom.normalizationSourceIso e p (pullback.snd f j)
    (factorPullbackIso_hom_snd p j)
  let E := normalGenericIntegralFactorIso g
  let n := f.normalizationPullback j
  let q := pullback.fst f.fromNormalization j
  let s := pullback.snd f.fromNormalization j
  let r := (pullback.snd f j).fromNormalization
  have hq : q ≫ f.fromNormalization = s ≫ j := pullback.condition
  have hn : n ≫ s = r := Scheme.Hom.normalizationPullback_snd f j
  have heN : eN.hom ≫ r = p.fromNormalization :=
    Scheme.Hom.normalizationSourceIso_hom_over e p (pullback.snd f j)
      (factorPullbackIso_hom_snd p j)
  have hE : E.hom ≫ g = p.fromNormalization := normalGenericIntegralFactorIso_hom_over g
  have htail : (n ≫ q) ≫ f.fromNormalization = r ≫ j :=
    (Category.assoc n q f.fromNormalization).trans
      ((congrArg (fun k => n ≫ k) hq).trans
        ((Category.assoc n s j).symm.trans (congrArg (fun k => k ≫ j) hn)))
  have htail' : (eN.hom ≫ (n ≫ q)) ≫ f.fromNormalization = p.fromNormalization ≫ j :=
    (Category.assoc eN.hom (n ≫ q) f.fromNormalization).trans
      ((congrArg (fun k => eN.hom ≫ k) htail).trans
        ((Category.assoc eN.hom r j).symm.trans (congrArg (fun k => k ≫ j) heN)))
  have hEinv : E.inv ≫ p.fromNormalization = g :=
    (congrArg (fun k => E.inv ≫ k) hE.symm).trans
      ((Category.assoc E.inv E.hom g).symm.trans
        ((congrArg (fun k => k ≫ g) E.inv_hom_id).trans (Category.id_comp g)))
  change (E.inv ≫ (eN.hom ≫ (n ≫ q))) ≫ f.fromNormalization = g ≫ j
  exact (Category.assoc E.inv (eN.hom ≫ (n ≫ q)) f.fromNormalization).trans
    ((congrArg (fun k => E.inv ≫ k) htail').trans
      ((Category.assoc E.inv p.fromNormalization j).symm.trans
        (congrArg (fun k => k ≫ j) hEinv)))

end NormalIntegral
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
