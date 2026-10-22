/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.Noetherian
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FixedBaseLimit

/-!
# Henselian finite-etale lifting from proper finitely presented approximants

An actual inverse-limit presentation by proper finitely presented schemes over
the same henselian local ring supplies essential surjectivity. The approximation
is an explicit hypothesis here; this leaf does not construct it or assert the
unconditional arbitrary-proper comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lift original closed-fibre covers through specified actual proper FP stages
without any Noetherian condition on the henselian local base. -/
theorem properHenselian_baseChange_essSurj_of_properFPLimit
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {s t} (g : s ⟶ t), IsAffineHom (D.map g)]
    (a : D ⟶ (Functor.const I).obj (Spec (.of R)))
    [∀ s, IsProper (a.app s)] [∀ s, LocallyOfFinitePresentation (a.app s)]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ Spec (.of R))
    (hp : ∀ s, c.π.app s ≫ a.app s = p) :
    (baseChange (pullback.fst p (LocalRing.residueSpecMap R))).EssSurj := by
  have (s : I) : CompactSpace (pullback (a.app s) (LocalRing.residueSpecMap R) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (a.app s) (LocalRing.residueSpecMap R))
  have (s : I) : QuasiSeparatedSpace
      (pullback (a.app s) (LocalRing.residueSpecMap R) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd (a.app s) (LocalRing.residueSpecMap R))
  exact LimitDescent.baseChange_essSurj_of_fixedBaseLimit D (LocalRing.residueSpecMap R)
    a c hc p hp (fun s ↦ properHenselian_baseChange_essSurj_of_finitePresentation (a.app s))

end AlgebraicGeometry.Scheme.FiniteEtale
