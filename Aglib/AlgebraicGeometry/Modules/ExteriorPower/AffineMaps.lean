/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine


/-!
# Actual affine exterior comparisons preserve arrows

Naturality is proved on the original exterior generators, not inferred from
an object isomorphism. No freeness or finiteness hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat R) (n : ℕ)

/-- The inverse original affine exterior comparison retains original wedges. -/
theorem exteriorTildeIso_inv_mk (r : R) (v : Fin n → M) :
    (exteriorTildeIso M n).inv.val.app (op (PrimeSpectrum.basicOpen r))
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) (PrimeSpectrum.basicOpen r)
        (exteriorPower.ιMulti R n v)) =
    (SheafOfModulesOfCommRing.exteriorPowerMk (Spec R).sheaf (tilde M) n).app
      (op (PrimeSpectrum.basicOpen r))
      (fun k => tilde.toOpen M (PrimeSpectrum.basicOpen r) (v k)) := by
  have h := congrArg ((exteriorTildeIso M n).inv.val.app (op (PrimeSpectrum.basicOpen r)))
    (exteriorTildeIso_hom_mk M n r v)
  exact h.symm.trans (ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op (PrimeSpectrum.basicOpen r)))
      (exteriorTildeIso M n).hom_inv_id) _)

/-- The same affine exterior comparison on original global wedges. -/
theorem exteriorTildeIso_hom_mk_top (v : Fin n → M) :
    (exteriorTildeIso M n).hom.val.app (op ⊤)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec R).sheaf (tilde M) n).app
        (op ⊤) (fun k => tilde.toOpen M ⊤ (v k))) =
    tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) ⊤ (exteriorPower.ιMulti R n v) := by
  have h := exteriorTildeIso_hom_mk M n 1 v
  rw [PrimeSpectrum.basicOpen_one] at h
  exact h

/-- The inverse affine exterior comparison on original global wedges. -/
theorem exteriorTildeIso_inv_mk_top (v : Fin n → M) :
    (exteriorTildeIso M n).inv.val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) ⊤ (exteriorPower.ιMulti R n v)) =
    (SheafOfModulesOfCommRing.exteriorPowerMk (Spec R).sheaf (tilde M) n).app
      (op ⊤) (fun k => tilde.toOpen M ⊤ (v k)) := by
  have h := exteriorTildeIso_inv_mk M n 1 v
  rw [PrimeSpectrum.basicOpen_one] at h
  exact h

/-- The actual affine exterior comparison preserves each original module arrow. -/
theorem exteriorTildeIso_naturality {N : ModuleCat R} (f : M ⟶ N) :
    (moduleExteriorPowerFunctor (Spec R) n).map ((tilde.functor R).map f) ≫
      (exteriorTildeIso N n).hom =
    (exteriorTildeIso M n).hom ≫
      (tilde.functor R).map (ModuleCat.ofHom (exteriorPower.map n f.hom)) := by
  apply (cancel_epi (exteriorTildeIso M n).inv).mp
  refine Eq.trans ?_ ((exteriorTildeIso M n).inv_hom_id_assoc
    ((tilde.functor R).map (ModuleCat.ofHom (exteriorPower.map n f.hom)))).symm
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change (exteriorTildeIso N n).hom.val.app (op ⊤)
    (((moduleExteriorPowerFunctor (Spec R) n).map ((tilde.functor R).map f)).val.app (op ⊤)
      ((exteriorTildeIso M n).inv.val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) ⊤ (exteriorPower.ιMulti R n v)))) =
    ((tilde.functor R).map (ModuleCat.ofHom (exteriorPower.map n f.hom))).val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) ⊤ (exteriorPower.ιMulti R n v))
  rw [exteriorTildeIso_inv_mk_top]
  refine (congrArg ((exteriorTildeIso N n).hom.val.app (op ⊤))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec R).sheaf
      ((tilde.functor R).map f) n (op ⊤) (fun k => tilde.toOpen M ⊤ (v k)))).trans ?_
  have hf (m : M) : ((tilde.functor R).map f).val.app (op ⊤) (tilde.toOpen M ⊤ m) =
      tilde.toOpen N ⊤ (f m) :=
    ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) m
  have hv : (fun k => ((tilde.functor R).map f).val.app (op ⊤)
      (tilde.toOpen M ⊤ (v k))) = (fun k => tilde.toOpen N ⊤ (f (v k))) :=
    funext (fun k => hf (v k))
  refine (congrArg (fun z => (exteriorTildeIso N n).hom.val.app (op ⊤)
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec R).sheaf (tilde N) n).app
      (op ⊤) z)) hv).trans ?_
  refine (exteriorTildeIso_hom_mk_top N n (fun i => f (v i))).trans ?_
  have hg := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (exteriorPower.map n f.hom)) ⊤)
    (exteriorPower.ιMulti R n v)
  exact (hg.trans (congrArg (tilde.toOpen (ModuleCat.of R (⋀[R]^n N)) ⊤)
    (exteriorPower.map_apply_ιMulti f.hom v))).symm

end AlgebraicGeometry.Scheme.Modules
