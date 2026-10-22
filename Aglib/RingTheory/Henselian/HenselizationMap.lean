/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationUniversal

/-!
# Henselization maps and equivalence transport

A local ring map induces a genuine map of the constructed henselizations, using
the proved universal property with its actual induced algebra action. Uniqueness
proves the identity and composition laws. In particular, a ring equivalence of
local rings induces an equivalence of their actual henselizations, compatible
with the original ring maps.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Henselization

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The proved local universal property for an explicit original ring map. -/
theorem existsUnique_local_ringHom {T : Type v} [CommRing T] [HenselianLocalRing T]
    (f : R →+* T) [IsLocalHom f] :
    ∃! g : Henselization R →+* T,
      IsLocalHom g ∧ g.comp (algebraMap R (Henselization R)) = f := by
  let : Algebra R T := f.toAlgebra
  let : IsLocalHom (algebraMap R T) := ‹IsLocalHom f›
  obtain ⟨g, hg, huniq⟩ := existsUnique_local_algHom R T
  refine ⟨g.toRingHom, ⟨hg, ?_⟩, ?_⟩
  · exact g.comp_algebraMap
  · intro h hh
    let h' : Henselization R →ₐ[R] T :=
      { h with commutes' := fun r => RingHom.congr_fun hh.2 r }
    exact congrArg AlgHom.toRingHom (huniq h' hh.1)

/-- Local maps out of the actual henselization agree when their original maps agree. -/
theorem local_ringHom_ext {T : Type v} [CommRing T] [HenselianLocalRing T]
    (f g : Henselization R →+* T) [IsLocalHom f] [IsLocalHom g]
    (h : f.comp (algebraMap R (Henselization R)) =
      g.comp (algebraMap R (Henselization R))) : f = g := by
  obtain ⟨a, ha, hu⟩ := existsUnique_local_ringHom
    (f.comp (algebraMap R (Henselization R)))
  exact (hu f ⟨inferInstance, rfl⟩).trans (hu g ⟨inferInstance, h.symm⟩).symm

variable {S : Type v} [CommRing S] [IsLocalRing S]

/-- The actual henselization map extending a local ring map. -/
def map (f : R →+* S) [IsLocalHom f] : Henselization R →+* Henselization S :=
  (existsUnique_local_ringHom ((algebraMap S (Henselization S)).comp f)).choose

instance map_isLocalHom (f : R →+* S) [IsLocalHom f] : IsLocalHom (map f) :=
  (existsUnique_local_ringHom ((algebraMap S (Henselization S)).comp f)).choose_spec.1.1

theorem map_comp_algebraMap (f : R →+* S) [IsLocalHom f] :
    (map f).comp (algebraMap R (Henselization R)) =
      (algebraMap S (Henselization S)).comp f :=
  (existsUnique_local_ringHom ((algebraMap S (Henselization S)).comp f)).choose_spec.1.2

@[simp] theorem map_algebraMap (f : R →+* S) [IsLocalHom f] (r : R) :
    map f (algebraMap R (Henselization R) r) = algebraMap S (Henselization S) (f r) :=
  RingHom.congr_fun (map_comp_algebraMap f) r

@[simp] theorem map_id : map (RingHom.id R) = RingHom.id (Henselization R) := by
  apply local_ringHom_ext
  ext r
  simp

theorem map_comp {T : Type w} [CommRing T] [IsLocalRing T]
    (f : R →+* S) (g : S →+* T) [IsLocalHom f] [IsLocalHom g] :
    (map g).comp (map f) = map (g.comp f) := by
  apply local_ringHom_ext
  ext r
  simp

local instance ringEquiv_toRingHom_isLocalHom (e : R ≃+* S) : IsLocalHom e.toRingHom :=
  ⟨fun _ h => (MulEquiv.isUnit_map e).mp h⟩

/-- Ring equivalences induce equivalences of the actual constructed henselizations. -/
def equivOfRingEquiv (e : R ≃+* S) : Henselization R ≃+* Henselization S :=
  { map e.toRingHom with
    invFun := map e.symm.toRingHom
    left_inv := fun x => by
      have h : (map e.symm.toRingHom).comp (map e.toRingHom) =
          RingHom.id (Henselization R) := by
        apply local_ringHom_ext
        ext r
        simp
      exact RingHom.congr_fun h x
    right_inv := fun x => by
      have h : (map e.toRingHom).comp (map e.symm.toRingHom) =
          RingHom.id (Henselization S) := by
        apply local_ringHom_ext
        ext s
        simp
      exact RingHom.congr_fun h x }

@[simp] theorem equivOfRingEquiv_algebraMap (e : R ≃+* S) (r : R) :
    equivOfRingEquiv e (algebraMap R (Henselization R) r) =
      algebraMap S (Henselization S) (e r) := map_algebraMap e.toRingHom r

end Henselization
