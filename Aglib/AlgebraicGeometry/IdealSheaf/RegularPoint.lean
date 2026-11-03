/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.ResiduePoint
public import Aglib.RingTheory.RegularLocalRing.RegularSequenceLocalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Regular pairs for the original point ideal on actual affine neighbourhoods

A two-dimensional regular stalk on a Noetherian affine open gives one native
principal neighbourhood whose actual section ring has a regular pair generating
the exact original residue-point ideal. The point survives in that neighbourhood,
so the ideal is proper. No closed-point or domain hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The exact point ideal has a proper regular pair on one original principal neighbourhood. -/
theorem exists_regularPair_basicOpen {X : Scheme.{u}}
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    [IsNoetherianRing Γ(X, U)] [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ ∃ a b : Γ(X, X.basicOpen f),
      Ideal.span {a, b} =
        (X.fromSpecResidueField x).ker.ideal (X.affineBasicOpen f) ∧
      Ideal.span {a, b} ≠ ⊤ ∧
      IsSMulRegular Γ(X, X.basicOpen f) a ∧
      IsSMulRegular (Γ(X, X.basicOpen f) ⧸ Ideal.span {a}) b := by
  let R := Γ(X, U)
  let p := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  let : p.IsPrime := (U.2.primeIdealOf ⟨x, hx⟩).isPrime
  let : Algebra R (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  let e_p : Localization.AtPrime p ≃ₐ[R] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (X.presheaf.stalk x)
  let : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularLocalRing.of_ringEquiv e_p.symm.toRingEquiv
  have hd : ringKrullDim (Localization.AtPrime p) = 2 :=
    e_p.toRingEquiv.ringKrullDim.trans hdim
  obtain ⟨f, hf, a₀, b₀, hgen₀, ha₀, hb₀⟩ :=
    IsRegularLocalRing.exists_regularPair_away p hd
  have hxf : x ∈ X.basicOpen f := by
    have hp : U.2.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hf
    rw [← U.2.fromSpec_preimage_basicOpen f] at hp
    have hp' : U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f :=
      (Scheme.Hom.mem_preimage (f := U.2.fromSpec)).mp hp
    rwa [U.2.fromSpec_primeIdealOf] at hp'
  let S := Γ(X, X.basicOpen f)
  let res : R →+* S := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra R S := res.toAlgebra
  let : IsLocalization.Away f S :=
    U.2.isLocalization_of_eq_basicOpen f (homOfLE (X.basicOpen_le f)) rfl
  let e_f : Localization.Away f ≃ₐ[R] S :=
    IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S
  let a : S := e_f a₀
  let b : S := e_f b₀
  have hmap : e_f.toRingHom.comp (algebraMap R (Localization.Away f)) = res :=
    e_f.toAlgHom.comp_algebraMap
  have hpair : (Ideal.span {a₀, b₀}).map e_f.toRingHom = Ideal.span {a, b} := by
    change (Ideal.span {a₀, b₀}).map e_f.toRingHom = Ideal.span {e_f a₀, e_f b₀}
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  have hgen : Ideal.span {a, b} = p.map res := by
    rw [← hpair, hgen₀, Ideal.map_map, hmap]
  have hcenter : Ideal.span {a, b} =
      (X.fromSpecResidueField x).ker.ideal (X.affineBasicOpen f) :=
    hgen.trans (fromSpecResidueField_ker_ideal_basicOpen x U hx f).symm
  have hproper : Ideal.span {a, b} ≠ ⊤ := by
    rw [hcenter, fromSpecResidueField_ker_ideal x (X.affineBasicOpen f) hxf]
    exact ((X.affineBasicOpen f).2.primeIdealOf ⟨x, hxf⟩).isPrime.ne_top
  have ha : IsSMulRegular S a := by
    apply (Equiv.isSMulRegular_congr (e := e_f.toEquiv) ?_).mp ha₀
    intro z
    change e_f (a₀ * z) = e_f a₀ * e_f z
    exact e_f.map_mul a₀ z
  have hsingle : Ideal.span {a} = (Ideal.span {a₀}).map e_f.toRingHom := by
    change Ideal.span {e_f a₀} = (Ideal.span {a₀}).map e_f.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  let e_quot : (Localization.Away f ⧸ Ideal.span {a₀}) ≃+* S ⧸ Ideal.span {a} :=
    Ideal.quotientEquiv (Ideal.span {a₀}) (Ideal.span {a}) e_f.toRingEquiv hsingle
  have hb : IsSMulRegular (S ⧸ Ideal.span {a}) b := by
    apply (Equiv.isSMulRegular_congr (e := e_quot.toEquiv) ?_).mp hb₀
    intro z
    have hsrc : b₀ • z = Ideal.Quotient.mk (Ideal.span {a₀}) b₀ * z := by
      simpa only [Ideal.Quotient.algebraMap_eq] using (Algebra.smul_def b₀ z)
    have htgt : b • e_quot z = Ideal.Quotient.mk (Ideal.span {a}) b * e_quot z := by
      simpa only [Ideal.Quotient.algebraMap_eq] using (Algebra.smul_def b (e_quot z))
    have hmk : e_quot (Ideal.Quotient.mk (Ideal.span {a₀}) b₀) =
        Ideal.Quotient.mk (Ideal.span {a}) b := by
      simpa only [AlgEquiv.coe_ringEquiv] using
        (Ideal.quotientEquiv_mk (Ideal.span {a₀}) (Ideal.span {a})
          e_f.toRingEquiv hsingle b₀)
    simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv] using
      (congrArg e_quot hsrc).trans
        ((e_quot.map_mul _ z).trans
          ((congrArg (fun t => t * e_quot z) hmk).trans htgt.symm))
  exact ⟨f, hxf, a, b, hcenter, hproper, ha, hb⟩

/-- On a locally Noetherian scheme, an actual affine neighbourhood inside any given open
has a proper regular pair for the original point ideal at a two-dimensional regular stalk. -/
theorem exists_regularPair_affineOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (W : X.Opens) (hxW : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧ ∃ a b : Γ(X, V),
      Ideal.span {a, b} = (X.fromSpecResidueField x).ker.ideal V ∧
      Ideal.span {a, b} ≠ ⊤ ∧ IsSMulRegular Γ(X, V) a ∧
      IsSMulRegular (Γ(X, V) ⧸ Ideal.span {a}) b := by
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let A : X.affineOpens := ⟨U, hU⟩
  let : IsNoetherianRing Γ(X, A) := IsLocallyNoetherian.component_noetherian A
  obtain ⟨f, hxf, a, b, hcenter, hproper, ha, hb⟩ :=
    exists_regularPair_basicOpen A x hxU hdim
  exact ⟨X.affineBasicOpen f, hxf, (X.basicOpen_le f).trans hUW,
    a, b, hcenter, hproper, ha, hb⟩

end AlgebraicGeometry.Scheme
