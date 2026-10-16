/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting

/-!
# Local lifting from finite locally free sheaves

An epimorphism onto a finite locally free sheaf splits on actual open
neighborhoods. Morphisms from such a sheaf lift locally through epimorphisms
and factor locally through an exact short complex. The maps and equations
use the actual module-sheaf restriction functor; no global projectivity is assumed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalLifting.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `846a1081555e08cca1ae5b6ab50a9a307d8883a1e7228860e5e009c56ab7364f`.
Selected declaration ranges: 41–67, 70–82, 87–100.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

theorem exists_local_section {E P : X.Modules} (q : E ⟶ P) [Epi q]
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X P] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj E,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map q = 𝟙 _ := by
  have hs : (ShortComplex.kernelSequence q).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact q
      epi_g := inferInstanceAs (Epi q) }
  obtain ⟨U, hxU, ⟨s⟩⟩ := @AlgebraicGeometry.Scheme.Modules.exists_local_splitting X
    (ShortComplex.kernelSequence q) hs
    (inferInstanceAs (AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X P)) x
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U
  let σ := e.inv.app P ≫ F.map s.s ≫ e.hom.app E
  refine ⟨U, hxU, σ, ?_⟩
  have he := e.hom.naturality q
  have hs' : s.s ≫ q.over U = 𝟙 _ := s.s_g
  change e.inv.app P ≫ F.map s.s ≫ e.hom.app E ≫
    (Scheme.Modules.restrictFunctor U.ι).map q = 𝟙 _
  rw [← he]
  change e.inv.app P ≫ F.map s.s ≫ F.map (q.over U) ≫ e.hom.app P = 𝟙 _
  rw [← Functor.map_comp_assoc, hs']
  change e.inv.app P ≫ F.map (𝟙 (P.over U)) ≫ e.hom.app P = 𝟙 _
  rw [F.map_id]
  erw [Category.id_comp]
  exact e.inv_hom_id_app P

theorem exists_local_lift {E N P : X.Modules} (p : E ⟶ N) [Epi p]
    (f : P ⟶ N) [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X P] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj E,
        l ≫ (Scheme.Modules.restrictFunctor U.ι).map p =
          (Scheme.Modules.restrictFunctor U.ι).map f := by
  obtain ⟨U, hxU, s, hs⟩ := exists_local_section (pullback.snd p f) x
  let R := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hxU, s ≫ R.map (pullback.fst p f), ?_⟩
  change (s ≫ R.map (pullback.fst p f)) ≫ R.map p = R.map f
  rw [Category.assoc, ← R.map_comp, pullback.condition, R.map_comp, ← Category.assoc, hs]
  simp

theorem exists_local_factor_of_exact {S : ShortComplex X.Modules} (hS : S.Exact)
    {P : X.Modules} [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X P]
    (f : P ⟶ S.X₂) (hf : f ≫ S.g = 0) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj P ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₁,
        l ≫ (Scheme.Modules.restrictFunctor U.ι).map S.f =
          (Scheme.Modules.restrictFunctor U.ι).map f := by
  let := hS.epi_toCycles
  obtain ⟨U, hxU, l, hl⟩ := exists_local_lift S.toCycles (S.liftCycles f hf) x
  let R := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hxU, l, ?_⟩
  change l ≫ R.map S.f = R.map f
  rw [← S.toCycles_i, R.map_comp, ← Category.assoc, hl, ← R.map_comp, S.liftCycles_i]

end AlgebraicGeometry.Scheme.Modules
