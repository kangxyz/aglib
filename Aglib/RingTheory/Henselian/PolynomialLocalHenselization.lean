/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Aglib.RingTheory.Henselian.HenselizationUniversal

/-!
# The actual inclusion between polynomial local henselizations

These are henselizations of native polynomial localizations. The lower variables
map by `i ↦ Equiv.swap 0 (Fin.last n) i.succ`, as required by `finLastEquiv`.
The inclusion is constructed by the proved local universal property and is
characterized by its literal restriction to the original local polynomial ring.
-/

@[expose] public section

noncomputable section

universe u

/-- The actual henselization of the polynomial local ring at the origin. -/
abbrev PolynomialLocalHenselization (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  Henselization (PolynomialLocalRing R n)

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

instance algebra (n : ℕ) : Algebra R (PolynomialLocalHenselization R n) :=
  Algebra.compHom (PolynomialLocalHenselization R n) (algebraMap R (PolynomialLocalRing R n))

instance isScalarTower (n : ℕ) :
    IsScalarTower R (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The original lower local polynomial ring maps to the higher henselization. -/
def localInclusion (n : ℕ) :
    PolynomialLocalRing R n →ₐ[R] PolynomialLocalHenselization R (n + 1) :=
  (IsScalarTower.toAlgHom R (PolynomialLocalRing R (n + 1))
    (PolynomialLocalHenselization R (n + 1))).comp (PolynomialLocalRing.variableInclusion R n)

instance localInclusion_isLocalHom (n : ℕ) : IsLocalHom (localInclusion R n).toRingHom := by
  change IsLocalHom ((algebraMap (PolynomialLocalRing R (n + 1))
    (PolynomialLocalHenselization R (n + 1))).comp
      (PolynomialLocalRing.variableInclusion R n).toRingHom)
  infer_instance

/-- The genuine universal property supplies the unique local extension of the
actual lower-variable inclusion. -/
theorem existsUnique_local_variableInclusion (n : ℕ) :
    ∃! f : PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalHenselization R (n + 1),
      IsLocalHom f.toRingHom ∧
        f.comp (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
          (PolynomialLocalHenselization R n)) = localInclusion R n := by
  let A := PolynomialLocalRing R n
  let B := PolynomialLocalHenselization R (n + 1)
  let : Algebra A B := (localInclusion R n).toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    (localInclusion R n).commutes r |>.symm
  let : IsLocalHom (algebraMap A B) := localInclusion_isLocalHom R n
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

/-- The actual lower-to-higher henselization map in the `finLastEquiv` variable order. -/
def variableInclusion (n : ℕ) :
    PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalHenselization R (n + 1) :=
  (existsUnique_local_variableInclusion R n).choose

instance variableInclusion_isLocalHom (n : ℕ) : IsLocalHom (variableInclusion R n).toRingHom :=
  (existsUnique_local_variableInclusion R n).choose_spec.1.1

/-- The inclusion agrees with the original local polynomial map, literally as an algebra map. -/
theorem variableInclusion_comp_of (n : ℕ) :
    (variableInclusion R n).comp (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
      (PolynomialLocalHenselization R n)) = localInclusion R n :=
  (existsUnique_local_variableInclusion R n).choose_spec.1.2

end PolynomialLocalHenselization
