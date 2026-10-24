/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.LocalStructure
public import Aglib.AlgebraicGeometry.Grassmannian.Flat
public import Aglib.AlgebraicGeometry.Grassmannian.PluckerClosedImmersion

/-!
# `Gr(E, k) ⟶ S` is proper, smooth, flat and separated

For a module sheaf `E` on a scheme `S` that is finite locally free of constant rank `n`
(`SheafHasRank E n`), the structure morphism of the Grassmannian bundle
`Gr(E, k) = grassmannianBundle E k n h` of rank-`k` locally free quotients is proper
(`isProper_grassmannianBundle_hom`), smooth (`smooth_grassmannianBundle_hom`), hence flat
(`flat_grassmannianBundle_hom`), and separated (`isSeparated_grassmannianBundle_hom`).

Each property is local on the target, and over a trivializing chart `Spec R ⟶ S` of `E` the
Grassmannian bundle is `Gr(R^n, k) = schemeOver R k n`
(`grassmannianBundle_hom_of_isZariskiLocalAtTarget`, from `grassmannianBundlePullbackIso`). For
`schemeOver R k n ⟶ Spec R` smoothness is `Grassmannian/Flat` (polynomial charts) and properness
and separatedness are `Grassmannian/PluckerClosedImmersion` (the Plücker closed immersion into
projective space).

Sources: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1,
Exercise (2), pp. 5–6 (`Grass(E, d)` is locally `Grass(r, d)`), and the construction of the
Grassmannian in §1: `Grass(r, d)` is smooth and separated (p. 8) and proper (pp. 8–9; the
projective embedding is on p. 9); Stacks Project,
Tag 089T (proof of Lemma 27.22.1: the charts are affine spaces). Stacks, Section 27.22 (Tag 089R)
states neither smoothness nor properness of the Grassmannian. Premise: `BaseChangeMkQFormula`, as
in the rest of the family.

Consumer: the linear-system representability of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 3.13, pp. 25–26, used in the proof of Thm 4.8, p. 30 (Picard plan,
"Representability", step 5: `R ⟶ Z` is proper and flat).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Grassmannian

variable {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- `Gr(E, k) ⟶ S` is proper. -/
theorem isProper_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    IsProper (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @IsProper)
    (fun _ ↦ inferInstance) h

/-- `Gr(E, k) ⟶ S` is separated. -/
theorem isSeparated_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    IsSeparated (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @IsSeparated)
    (fun _ ↦ inferInstance) h

/-- `Gr(E, k) ⟶ S` is smooth. -/
theorem smooth_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    Smooth (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @Smooth)
    (fun _ ↦ inferInstance) h

/-- `Gr(E, k) ⟶ S` is flat. -/
theorem flat_grassmannianBundle_hom (h : Scheme.Modules.SheafHasRank E n) :
    Flat (grassmannianBundle E k n h).hom :=
  grassmannianBundle_hom_of_isZariskiLocalAtTarget E k n (P := @Flat)
    (fun _ ↦ inferInstance) h

end AlgebraicGeometry.Grassmannian
