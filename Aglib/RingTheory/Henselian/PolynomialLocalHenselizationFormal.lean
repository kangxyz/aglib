/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselization
public import Aglib.RingTheory.Henselian.PolynomialLocalFormal
public import Aglib.RingTheory.Henselian.Quadratic
public import Aglib.RingTheory.MvPowerSeries.AdicComplete
public import Aglib.RingTheory.AdicCompletion.NoetherianRing

/-!
# Formal evaluation of actual polynomial local henselizations

The target consists of power series over the completion of the original local
coefficient ring. Its Henselian structure is proved from actual mixed-adic
completeness, not assumed as an input. The resulting local algebra map extends
the original polynomial evaluation through the native localization.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The formal target is Henselian by its actual maximal-ideal completeness. -/
theorem formalSeries_henselian (n : ℕ) : HenselianLocalRing (FormalSeries R n) := by
  let : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing R (maximalIdeal R)
  let : IsAdicComplete (maximalIdeal (FormalSeries R n)) (FormalSeries R n) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (Fin n) (AdicCompletion (maximalIdeal R) R)
  exact HenselianLocalRing.of_isAdicComplete

end PolynomialLocalRing

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The genuine universal property supplies the unique local extension of formal evaluation. -/
theorem existsUnique_local_toFormalSeries (n : ℕ) :
    ∃! f : PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalRing.FormalSeries R n,
      IsLocalHom f.toRingHom ∧
        f.comp (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
          (PolynomialLocalHenselization R n)) = PolynomialLocalRing.toFormalSeries R n := by
  let : HenselianLocalRing (PolynomialLocalRing.FormalSeries R n) :=
    PolynomialLocalRing.formalSeries_henselian R n
  let A := PolynomialLocalRing R n
  let B := PolynomialLocalRing.FormalSeries R n
  let : Algebra A B := (PolynomialLocalRing.toFormalSeries R n).toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    (PolynomialLocalRing.toFormalSeries R n).commutes r |>.symm
  let : IsLocalHom (algebraMap A B) := PolynomialLocalRing.toFormalSeries_isLocalHom R n
  let h := Henselization.existsUnique_local_algHom A B
  let g : Henselization A →ₐ[A] B := h.choose
  have hg : IsLocalHom g.toRingHom := h.choose_spec.1
  refine ⟨g.restrictScalars R, ⟨hg, ?_⟩, ?_⟩
  · apply AlgHom.ext
    intro a
    exact g.commutes a
  · intro f hf
    let f' : Henselization A →ₐ[A] B :=
      { f.toRingHom with
        commutes' := fun a => AlgHom.congr_fun hf.2 a }
    have he : f' = g := h.choose_spec.2 f' hf.1
    apply AlgHom.ext
    intro x
    exact AlgHom.congr_fun he x

/-- The canonical local map from the actual polynomial henselization to formal series. -/
def toFormalSeries (n : ℕ) :
    PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalRing.FormalSeries R n :=
  (existsUnique_local_toFormalSeries R n).choose

instance toFormalSeries_isLocalHom (n : ℕ) : IsLocalHom (toFormalSeries R n).toRingHom :=
  (existsUnique_local_toFormalSeries R n).choose_spec.1.1

/-- Formal evaluation agrees literally with the original local polynomial evaluation. -/
theorem toFormalSeries_comp_of (n : ℕ) :
    (toFormalSeries R n).comp (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
      (PolynomialLocalHenselization R n)) = PolynomialLocalRing.toFormalSeries R n :=
  (existsUnique_local_toFormalSeries R n).choose_spec.1.2

end PolynomialLocalHenselization
