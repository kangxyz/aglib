/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.FiniteGeneration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.Bounded

/-! # Finite generation of original constructible abelian sheaves

On a qcqs scheme, a constructible sheaf has a finite actual constructible
stratum cover. Each original restriction is finite locally constant on a
qcqs stratum, hence ordinarily finitely presentable. The original inverse
images preserve the supplied filtered colimit and are jointly faithful.
Thus some original cocone leg is epimorphic. This is finite generation,
not yet finite presentation of the original constructible coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A filtered presentation of a genuine constructible coefficient on a qcqs
scheme contains an epimorphic original stage. No constructibility of its
stages and no finite presentability of its original apex are assumed. -/
theorem exists_epi_of_isColimit_of_isConstructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ AbelianSheaf.{u, u + 1} X} {c : Cocone D}
    (hc : IsColimit c) (hF : IsConstructible c.pt) :
    ∃ i, Epi (c.ι.app i) := by
  let t := finiteLocallyClosedCover c.pt hF
  have : Finite t.index := t.finite_index
  have (k : t.index) : IsImmersion (t.inclusion k) := t.immersion k
  have (k : t.index) : CompactSpace (t.stratum k) := t.compact_stratum k
  have (k : t.index) : QuasiSeparatedSpace (t.stratum k) := t.quasiSeparated_stratum k
  have (k : t.index) : IsFinitelyPresentable.{u + 1}
      ((inverseImage (t.inclusion k)).obj c.pt) :=
    isFinitelyPresentable_of_isFiniteLocallyConstant _ (t.locally_constant k)
  exact JointlyFaithful.exists_epi_of_isColimit
    (fun k => inverseImage (t.inclusion k))
    (jointlyFaithful_immersionInverseImages t.stratum t.inclusion t.covers) hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
