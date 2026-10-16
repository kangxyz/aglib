/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.Algebra.Category.FGModuleCat.Localization.EssentialSurjectivity

/-!
# Finite modules modulo localization torsion

For a Noetherian commutative ring, localization identifies the Serre quotient by
localization-torsion modules with finite modules over the localized ring. Fractions use the
actual scalar morphism r • 𝟙 M.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/GTheory/FiniteModules/Localization/Quotient.lean`.
SHA-256: `e676735cc68f032a2b9041a8b29c1f429e7b9a5eba81e2cd0b840dcf213ae14c`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat.FiniteLocalization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

omit [IsNoetherianRing R] in
/-- The localized scalar identity has the original scalar multiple of the identity linear map. -/
lemma localized_smul_id (M : FGModuleCat.{u} R) (r : R) :
    ((functor S).map (((r : R) • (𝟙 M)))).hom.hom =
      r • (LinearMap.id : M.obj.localizedModule S →ₗ[Localization S] M.obj.localizedModule S) := by
  change IsLocalizedModule.mapExtendScalars S _ _ (Localization S)
    (r • (LinearMap.id : M →ₗ[R] M)) = _
  rw [map_smul]
  congr 1
  ext x
  exact LinearMap.congr_fun (IsLocalizedModule.map_id S (M.obj.localizedModuleMkLinearMap S)) x

/-- Multiplication by a localization denominator becomes an isomorphism. -/
instance isIso_map_smul_id (M : FGModuleCat.{u} R) (s : S) :
    IsIso ((functor S).map (((s : R) • (𝟙 M)))) := by
  have : IsIso (((functor S).map (((s : R) • (𝟙 M)))).hom) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (((functor S).map (((s : R) • (𝟙 M)))).hom.hom)
    rw [localized_smul_id]
    change Function.Bijective (fun x : M.obj.localizedModule S ↦ (s : R) • x)
    have h := IsLocalizedModule.map_units (M.obj.localizedModuleMkLinearMap S) s
    rw [Module.End.isUnit_iff] at h
    exact h
  have : IsIso ((ModuleCat.isFG (Localization S)).ι.map
      ((functor S).map (((s : R) • (𝟙 M))))) := this
  exact (ModuleCat.isFG (Localization S)).fullyFaithfulι.isIso_of_isIso_map _

/-- A localization denominator times the identity has torsion kernel and cokernel. -/
lemma smul_id_mem_isoModSerre (M : FGModuleCat.{u} R) (s : S) :
    (torsion S).isoModSerre (((s : R) • (𝟙 M))) := (isoModSerre_iff S _).2 inferInstance

/-- A localized finite-module map is represented by one numerator and one scalar denominator. -/
lemma exists_denominator {M N : FGModuleCat.{u} R}
    (φ : (functor S).obj M ⟶ (functor S).obj N) :
    ∃ (g : M ⟶ N) (s : S), (functor S).map (((s : R) • (𝟙 M))) ≫ φ = (functor S).map g := by
  let : Module.FinitePresentation R M.obj := Module.finitePresentation_of_finite R M
  let φ' : M.obj.localizedModule S →ₗ[Localization S] N.obj.localizedModule S := φ.hom.hom
  obtain ⟨⟨g, s⟩, h⟩ := IsLocalizedModule.surj S
    (IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S) (Localization S)) φ'
  refine ⟨FGModuleCat.ofHom g, s, ?_⟩
  apply FGModuleCat.hom_ext
  ext x
  change M.obj.localizedModule S at x
  change φ' (((functor S).map (((s : R) • (𝟙 M)))).hom.hom x) = _
  rw [localized_smul_id]
  change φ' ((s : R) • x) =
    IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S) (Localization S) g x
  rw [φ'.map_smul_of_tower]
  exact LinearMap.congr_fun h x

/-- The actual localization functor inverts the Serre denominators. -/
lemma inverts : (torsion S).isoModSerre.IsInvertedBy (functor S) :=
  fun _ _ f hf ↦ (isoModSerre_iff S f).1 hf

/-- The functor on the actual constructed Serre quotient, induced by scalar localization. -/
def quotientFunctor : (torsion S).isoModSerre.Localization ⥤ FGModuleCat.{u} (Localization S) :=
  Localization.Construction.lift (functor S) (inverts S)

/-- The quotient comparison agrees with localization on the nose. -/
theorem quotientFunctor_fac : (torsion S).isoModSerre.Q ⋙ quotientFunctor S = functor S :=
  Localization.Construction.fac (functor S) (inverts S)

/-- The quotient comparison sends each original quotient arrow to its actual localized arrow. -/
@[simp] theorem quotientFunctor_map_Q {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (quotientFunctor S).map ((torsion S).isoModSerre.Q.map f) = (functor S).map f := by
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom (quotientFunctor_fac S) f

/-- Scalar denominators give fullness on the actual finite-module Serre quotient. -/
instance quotientFunctor_full : (quotientFunctor S).Full := by
  let Q := (torsion S).isoModSerre.Q
  have : Q.EssSurj := Localization.essSurj Q (torsion S).isoModSerre
  apply Functor.full_of_comp_essSurj (quotientFunctor S) Q
  intro M N φ
  change (functor S).obj M ⟶ (functor S).obj N at φ
  obtain ⟨g, s, hs⟩ := exists_denominator S φ
  have : IsIso (Q.map (((s : R) • (𝟙 M)))) :=
    Localization.inverts Q (torsion S).isoModSerre _ (smul_id_mem_isoModSerre S M s)
  refine ⟨inv (Q.map (((s : R) • (𝟙 M)))) ≫ Q.map g, ?_⟩
  apply (cancel_epi ((functor S).map (((s : R) • (𝟙 M))))).mp
  rw [Functor.map_comp, Functor.map_inv]
  simp only [Q, quotientFunctor_map_Q, IsIso.hom_inv_id_assoc]
  exact hs.symm

/-- Equality after localization is witnessed by a scalar denominator. -/
lemma exists_denominator_equal {M N : FGModuleCat.{u} R} (f g : M ⟶ N)
    (h : (functor S).map f = (functor S).map g) :
    ∃ s : S, ((s : R) • (𝟙 M)) ≫ f = ((s : R) • (𝟙 M)) ≫ g := by
  let : Module.FinitePresentation R M.obj := Module.finitePresentation_of_finite R M
  have h' : IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S) (Localization S) f.hom.hom =
    IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S) (Localization S) g.hom.hom :=
    congrArg (fun k ↦ k.hom.hom) h
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) h'
  refine ⟨s, ?_⟩
  apply FGModuleCat.hom_ext
  ext x
  change f.hom.hom ((s : R) • x) = g.hom.hom ((s : R) • x)
  simpa only [map_smul, Submonoid.smul_def, LinearMap.smul_apply] using LinearMap.congr_fun hs x

/-- Scalar cancellation gives faithfulness on the actual finite-module Serre quotient. -/
instance quotientFunctor_faithful : (quotientFunctor S).Faithful := by
  let Q := (torsion S).isoModSerre.Q
  apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions Q (torsion S).isoModSerre
    (quotientFunctor S)
  intro M N f g h
  simp only [Q, quotientFunctor_map_Q] at h
  obtain ⟨s, hs⟩ := exists_denominator_equal S f g h
  have : IsIso (Q.map (((s : R) • (𝟙 M)))) :=
    Localization.inverts Q (torsion S).isoModSerre _ (smul_id_mem_isoModSerre S M s)
  apply (cancel_epi (Q.map (((s : R) • (𝟙 M))))).mp
  simpa only [← Q.map_comp] using congrArg Q.map hs

/-- Finite generators give essential surjectivity of the quotient comparison. -/
instance quotientFunctor_essSurj : (quotientFunctor S).EssSurj where
  mem_essImage N := by
    obtain ⟨M, ⟨e⟩⟩ := (inferInstance : (functor S).EssSurj).mem_essImage N
    exact ⟨(torsion S).isoModSerre.Q.obj M, ⟨e⟩⟩

/-- The actual finite-module quotient comparison is an equivalence. -/
instance quotientFunctor_isEquivalence : (quotientFunctor S).IsEquivalence := {}

/-- Scalar localization of finite modules is the genuine Serre localization by torsion modules. -/
instance functor_isLocalization : (functor S).IsLocalization (torsion S).isoModSerre where
  inverts := inverts S
  isEquivalence := quotientFunctor_isEquivalence S

/-- The finite-module Serre quotient is equivalent to finite modules over the localized ring. -/
def quotientEquivalence : (torsion S).isoModSerre.Localization ≌ FGModuleCat.{u} (Localization S) :=
  (quotientFunctor S).asEquivalence

/-- The quotient equivalence is induced by the actual localization functor. -/
def quotientEquivalenceFactorsIso :
    (torsion S).isoModSerre.Q ⋙ (quotientEquivalence S).functor ≅ functor S :=
  eqToIso (quotientFunctor_fac S)

end ModuleCat.FiniteLocalization
