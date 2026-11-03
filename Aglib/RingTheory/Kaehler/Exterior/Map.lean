/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.ScalarExtension
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct


/-!
# RingTheory / Kaehler / Exterior / Map

Source: `PureDegreePTrace/Exterior.lean`.
Incoming SHA256: `a5fe71d53751d2c84aeb4ff8cdb6591ae4550c86faf6790a1186a0f9e0cba320`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open Polynomial TensorProduct


namespace KaehlerDifferential

section ExteriorConstruction

variable (Λ R S : Type*) [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]

/-- The actual Kähler map on native exterior powers, with its original source scalars. -/
def mapExterior (n : ℕ) :
    (⋀[R]^n (KaehlerDifferential Λ R)) →ₗ[R] (⋀[S]^n (KaehlerDifferential Λ S)) :=
  exteriorPower.mapAlgebra (S := S) n (map Λ Λ R S)

/-- The actual pulled-up exterior forms, retaining the original tensor product and scalar action. -/
def mapExteriorBaseChange (n : ℕ) :
    S ⊗[R] (⋀[R]^n (KaehlerDifferential Λ R)) →ₗ[S]
      (⋀[S]^n (KaehlerDifferential Λ S)) :=
  (mapExterior Λ R S n).liftBaseChange S

@[simp]
theorem mapExteriorBaseChange_tmul (n : ℕ) (s : S)
    (v : ⋀[R]^n (KaehlerDifferential Λ R)) :
    mapExteriorBaseChange Λ R S n (s ⊗ₜ[R] v) = s • mapExterior Λ R S n v :=
  LinearMap.liftBaseChange_tmul _ _ _ _

@[simp]
theorem mapExterior_ιMulti (n : ℕ) (v : Fin n → KaehlerDifferential Λ R) :
    mapExterior Λ R S n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => map Λ Λ R S (v i)) :=
  exteriorPower.mapAlgebra_ιMulti n (map Λ Λ R S) v

theorem mapExterior_snoc (n : ℕ) (v : Fin n → KaehlerDifferential Λ R)
    (ω : KaehlerDifferential Λ R) :
    mapExterior Λ R S (n + 1) (exteriorPower.ιMulti R (n + 1) (Fin.snoc v ω)) =
      exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (map Λ Λ R S ω)) := by
  rw [mapExterior_ιMulti]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Exterior differentials use the actual module localization, proved through tensor base change. -/
theorem mapExterior_isLocalizedModule (U : Submonoid R) [IsLocalization U S] (n : ℕ) :
    IsLocalizedModule U (mapExterior Λ R S n) := by
  let : IsLocalizedModule U (map Λ Λ R S) :=
    KaehlerDifferential.isLocalizedModule_map (R := Λ) (S := R) (T := S) U
  exact exteriorPower.isLocalizedModule_mapAlgebra U n (map Λ Λ R S)

variable {Λ R S}
variable {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [Algebra Λ T]
  [IsScalarTower R S T] [IsScalarTower Λ S T] [IsScalarTower Λ R T]

theorem exterior_map_tower_apply (η : KaehlerDifferential Λ R) :
    map Λ Λ S T (map Λ Λ R S η) = map Λ Λ R T η := by
  have he : ((map Λ Λ S T).restrictScalars R).comp (map Λ Λ R S) = map Λ Λ R T := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change map Λ Λ S T (map Λ Λ R S (D Λ R r)) = map Λ Λ R T (D Λ R r)
    simp only [map_D, ← IsScalarTower.algebraMap_apply R S T]
  exact LinearMap.congr_fun he η

theorem mapExterior_base_tower (n : ℕ) (v : Fin n → KaehlerDifferential Λ R) :
    mapExterior Λ S T n
      (exteriorPower.ιMulti S n (fun i => map Λ Λ R S (v i))) =
        exteriorPower.ιMulti T n (fun i => map Λ Λ R T (v i)) := by
  rw [mapExterior_ιMulti]
  congr 1
  funext i
  exact exterior_map_tower_apply (v i)

theorem mapExterior_snoc_tower (n : ℕ) (v : Fin n → KaehlerDifferential Λ R)
    (ω : KaehlerDifferential Λ S) :
    mapExterior Λ S T (n + 1)
      (exteriorPower.ιMulti S (n + 1) (Fin.snoc (fun i => map Λ Λ R S (v i)) ω)) =
        exteriorPower.ιMulti T (n + 1)
          (Fin.snoc (fun i => map Λ Λ R T (v i)) (map Λ Λ S T ω)) := by
  rw [mapExterior_snoc]
  congr 1
  congr 1
  funext i
  exact exterior_map_tower_apply (v i)

end ExteriorConstruction

section ExteriorMaps

variable (Λ R S T : Type*) [CommRing Λ] [CommRing R] [CommRing S] [CommRing T]
  [Algebra Λ R] [Algebra Λ S] [Algebra Λ T]
  [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower Λ R S] [IsScalarTower Λ S T] [IsScalarTower Λ R T]
  [IsScalarTower R S T]

/-- Whole-element functoriality of the original exterior Kähler maps. -/
theorem mapExterior_tower (n : ℕ) :
    ((mapExterior Λ S T n).restrictScalars R).comp (mapExterior Λ R S n) =
      mapExterior Λ R T n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change mapExterior Λ S T n (mapExterior Λ R S n (exteriorPower.ιMulti R n v)) =
    mapExterior Λ R T n (exteriorPower.ιMulti R n v)
  simpa only [mapExterior_ιMulti] using
    (mapExterior_base_tower (Λ := Λ) (R := R) (S := S) (T := T) n v)

theorem mapExterior_tower_apply (n : ℕ)
    (ω : ⋀[R]^n (KaehlerDifferential Λ R)) :
    mapExterior Λ S T n (mapExterior Λ R S n ω) = mapExterior Λ R T n ω :=
  LinearMap.congr_fun (mapExterior_tower Λ R S T n) ω

end ExteriorMaps

section ExteriorIdentity

variable (Λ R : Type*) [CommRing Λ] [CommRing R] [Algebra Λ R]

/-- The original exterior map of the identity coefficient map is the identity. -/
theorem mapExterior_self (n : ℕ) : mapExterior Λ R R n = LinearMap.id := by
  have hm : map Λ Λ R R = (LinearMap.id : KaehlerDifferential Λ R →ₗ[R] _) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change map Λ Λ R R (D Λ R r) = D Λ R r
    simp only [map_D, Algebra.algebraMap_self, RingHom.id_apply]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change mapExterior Λ R R n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R n v
  rw [mapExterior_ιMulti, hm]
  rfl

end ExteriorIdentity

end KaehlerDifferential
