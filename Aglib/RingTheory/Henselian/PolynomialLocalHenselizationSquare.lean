/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFormal
public import Aglib.RingTheory.Henselian.PolynomialLocalFormalInclusion

/-!
# The actual henselization and formal variable square

Both composites are genuine local maps. Their restrictions agree on the
original polynomial localization, so the proved local universal property,
not a functoriality assumption, identifies them.
-/

@[expose] public section

noncomputable section

universe u

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Formal evaluation commutes with the actual lower-variable henselization map. -/
theorem toFormalSeries_comp_variableInclusion (n : ℕ) :
    (toFormalSeries R (n + 1)).comp (variableInclusion R n) =
      (PolynomialLocalRing.formalVariableInclusion R n).comp (toFormalSeries R n) := by
  let A := PolynomialLocalRing R n
  let B := PolynomialLocalRing.FormalSeries R (n + 1)
  let φ : A →ₐ[R] B := (PolynomialLocalRing.formalVariableInclusion R n).comp
    (PolynomialLocalRing.toFormalSeries R n)
  let f : Henselization A →ₐ[R] B :=
    (toFormalSeries R (n + 1)).comp (variableInclusion R n)
  let g : Henselization A →ₐ[R] B :=
    (PolynomialLocalRing.formalVariableInclusion R n).comp (toFormalSeries R n)
  have hf : f.comp (IsScalarTower.toAlgHom R A (Henselization A)) = φ := by
    apply AlgHom.ext
    intro a
    have h₁ := AlgHom.congr_fun (variableInclusion_comp_of R n) a
    have h₂ := AlgHom.congr_fun (toFormalSeries_comp_of R (n + 1))
      (PolynomialLocalRing.variableInclusion R n a)
    have h₃ := AlgHom.congr_fun (PolynomialLocalRing.toFormalSeries_comp_variableInclusion R n) a
    change toFormalSeries R (n + 1)
      (variableInclusion R n (algebraMap A (Henselization A) a)) = φ a
    rw [show variableInclusion R n (algebraMap A (Henselization A) a) =
      algebraMap (PolynomialLocalRing R (n + 1)) (PolynomialLocalHenselization R (n + 1))
        (PolynomialLocalRing.variableInclusion R n a) from h₁]
    exact h₂.trans h₃
  have hg : g.comp (IsScalarTower.toAlgHom R A (Henselization A)) = φ := by
    apply AlgHom.ext
    intro a
    exact congrArg (PolynomialLocalRing.formalVariableInclusion R n)
      (AlgHom.congr_fun (toFormalSeries_comp_of R n) a)
  let : HenselianLocalRing B := PolynomialLocalRing.formalSeries_henselian R (n + 1)
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : IsLocalHom (algebraMap A B) := by
    change IsLocalHom ((PolynomialLocalRing.formalVariableInclusion R n).toRingHom.comp
      (PolynomialLocalRing.toFormalSeries R n).toRingHom)
    infer_instance
  let f' : Henselization A →ₐ[A] B :=
    { f.toRingHom with commutes' := fun a => AlgHom.congr_fun hf a }
  let g' : Henselization A →ₐ[A] B :=
    { g.toRingHom with commutes' := fun a => AlgHom.congr_fun hg a }
  have hf' : IsLocalHom f'.toRingHom := by
    change IsLocalHom ((toFormalSeries R (n + 1)).toRingHom.comp
      (variableInclusion R n).toRingHom)
    infer_instance
  have hg' : IsLocalHom g'.toRingHom := by
    change IsLocalHom ((PolynomialLocalRing.formalVariableInclusion R n).toRingHom.comp
      (toFormalSeries R n).toRingHom)
    infer_instance
  obtain ⟨h, _, hh⟩ := Henselization.existsUnique_local_algHom A B
  have he : f' = g' := (hh f' hf').trans (hh g' hg').symm
  apply AlgHom.ext
  intro x
  exact AlgHom.congr_fun he x

end PolynomialLocalHenselization
