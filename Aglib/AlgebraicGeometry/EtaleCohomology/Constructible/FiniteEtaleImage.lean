/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison

/-! # Finite étale direct image of original constructible abelian sheaves

On a qcqs source, an original constructible abelian sheaf has a positive
annihilator and an actual constructible ZMod-module lift. Finite étale direct
image of that genuine module sheaf, the positive-modulus comparison and the
original underlying-direct-image isomorphism give constructibility of the
original abelian direct image. Finite-type modules over arbitrary coefficient
rings are not silently identified with finite abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Finite étale direct image preserves original finite-abelian
constructibility when the source is qcqs. -/
theorem isConstructible_finiteEtaleDirectImage
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : S ⟶ X) [IsFinite f] [Etale f]
    {F : AbelianSheaf.{u, u + 1} S} (hF : IsConstructible F) :
    IsConstructible ((directImage f).obj F) := by
  obtain ⟨n, hn, M, hM, ⟨e⟩⟩ := Modules.exists_constructible_zmodSheaf F hF
  let N := (Modules.moduleDirectImage (ZMod n) f).obj M
  have hN : Modules.IsConstructible N := Modules.isConstructible_finiteEtaleDirectImage f hM
  have hU : IsConstructible ((Modules.moduleUnderlying (ZMod n) X).obj N) :=
    (Modules.isConstructible_zmod_iff n hn N).mp hN
  exact (isConstructible_iff_of_iso
    ((Modules.moduleDirectImageUnderlyingIso (ZMod n) f).app M ≪≫
      (directImage f).mapIso e)).mp hU

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
