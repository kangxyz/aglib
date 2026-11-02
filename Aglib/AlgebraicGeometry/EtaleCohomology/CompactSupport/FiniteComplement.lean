/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Localization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteClosedSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology

/-!
# Compactly supported cohomology with a finite closed complement

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion with complementary
image. If `H^r(X, i_* i^* G)` vanishes for all `r > 0`, then the original counit map
`H^r_c(U, j^* G) → H^r(X, G)` is bijective for `r ≥ 2` and surjective for `r = 1`.

This applies when `Z = pointScheme X D` is the literal coproduct of the residue-field spectra
of a finite set `D` of closed points of `X` with separably closed residue fields, and
`i = FiniteClosedSupport.inclusion X D`: the finite direct-image comparison
`Finite.finiteCohomologyDirectImageAddEquiv` and `FiniteClosedSupport.subsingleton_H` give
`H^r(X, i_* M) = 0` for every abelian sheaf `M` on `pointScheme X D` and every `r > 0`
(Milne, *Lectures on Étale Cohomology* v2.21, proof of Prop. 14.5, p. 92). Hence
`H^r_c(U, j^* G) ≅ H^r(X, G)` for `r ≥ 2`, and

`0 → H^0_c(U, j^* G) → H^0(X, G) → H^0(pointScheme X D, i^* G) → H^1_c(U, j^* G) → H^1(X, G) → 0`

is exact. The middle maps are the original unit and connecting maps, transported through the
finite direct-image comparison. No finiteness, torsion or constructibility condition on `G` is
imposed; the Ext universes of `X` and of the point scheme are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport

attribute [local instance] hasSheafifyLarge

section Vanishing

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (G : AbelianSheaf.{u, u + 1} X)
  (hvan : ∀ r, 0 < r →
    Subsingleton (Sheaf.H.{w} ((directImage i).obj ((inverseImage i).obj G)) r))

include hcomp hvan

/-- The counit map is surjective in positive degree when the closed part is acyclic. -/
theorem counitMap_surjective_of_subsingleton (r : ℕ) (hr : 0 < r) :
    Function.Surjective (counitMap j G r) := by
  intro y
  have : Subsingleton (Sheaf.H.{w} ((inverseImage i ⋙ directImage i).obj G) r) := hvan r hr
  exact (exact_counitMap_unitMap j i hcomp G r y).mp (Subsingleton.elim _ _)

/-- The counit map is injective in degree at least two when the closed part is acyclic. -/
theorem counitMap_injective_of_subsingleton (r : ℕ) (hr : 2 ≤ r) :
    Function.Injective (counitMap j G r) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have := hvan q (by omega)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_localizationδ_counitMap j i hcomp G q (q + 1) rfl x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- The counit map is bijective in degree at least two when the closed part is acyclic. -/
theorem counitMap_bijective_of_subsingleton (r : ℕ) (hr : 2 ≤ r) :
    Function.Bijective (counitMap j G r) :=
  ⟨counitMap_injective_of_subsingleton j i hcomp G hvan r hr,
    counitMap_surjective_of_subsingleton j i hcomp G hvan r (by omega)⟩

end Vanishing

open Curves.FiniteClosedSupport

/-- The open image is the complement of the literal finite support. -/
theorem range_eq_compl_range_inclusion {U X : Scheme.{u}} (D : Set X) (j : U ⟶ X)
    (hD : Set.range j = Dᶜ) : Set.range j = (Set.range (inclusion X D))ᶜ := by
  rw [range_inclusion, hD]

section FiniteSupport

variable {X : Scheme.{u}} (D : Set X) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include hfin hclosed hsep in
/-- Every finite direct image from the separably closed finite point scheme is acyclic in
positive degree. -/
theorem subsingleton_H_directImage_inclusion_of_sepClosed
    (M : AbelianSheaf.{u, u + 1} (pointScheme X D)) (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w} ((directImage (inclusion X D)).obj M) r) := by
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pointScheme X D)) := HasExt.standard _
  let : Subsingleton (Sheaf.H.{u + 2} M r) :=
    Curves.FiniteClosedSupport.subsingleton_H X D hfin hsep M r hr
  exact (Finite.finiteCohomologyDirectImageAddEquiv.{u, u + 2, w}
    (inclusion X D) M r).injective.subsingleton

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (G : AbelianSheaf.{u, u + 1} X)

include hD hfin hclosed hsep

/-- With a finite separably closed closed complement, the original counit map
`H^r_c(U, j^* G) → H^r(X, G)` is bijective for `r ≥ 2`. -/
theorem counitMap_bijective_of_finite_of_sepClosed (r : ℕ) (hr : 2 ≤ r) :
    Function.Bijective (counitMap j G r) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  exact counitMap_bijective_of_subsingleton j (inclusion X D)
    (range_eq_compl_range_inclusion D j hD) G
    (fun q hq => subsingleton_H_directImage_inclusion_of_sepClosed D hfin hclosed hsep _ q hq)
    r hr

/-- With a finite separably closed closed complement, the original counit map
`H^1_c(U, j^* G) → H^1(X, G)` is surjective. -/
theorem counitMap_one_surjective_of_finite_of_sepClosed :
    Function.Surjective (counitMap j G 1) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  exact counitMap_surjective_of_subsingleton j (inclusion X D)
    (range_eq_compl_range_inclusion D j hD) G
    (fun q hq => subsingleton_H_directImage_inclusion_of_sepClosed D hfin hclosed hsep _ q hq)
    1 one_pos

omit hsep in
/-- With a finite closed complement, the counit map is injective in degree zero. -/
theorem counitMap_zero_injective_of_finite : Function.Injective (counitMap j G 0) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  exact counitMap_zero_injective j (inclusion X D) (range_eq_compl_range_inclusion D j hD) G

/-- The isomorphism `H^r_c(U, j^* G) ≃+ H^r(X, G)` for `r ≥ 2`, given by the original
counit map. -/
def counitAddEquiv (r : ℕ) (hr : 2 ≤ r) : H j ((inverseImage j).obj G) r ≃+ Sheaf.H.{w} G r :=
  AddEquiv.ofBijective (counitMap j G r)
    (counitMap_bijective_of_finite_of_sepClosed D hfin hclosed hsep j hD G r hr)

theorem counitAddEquiv_apply (r : ℕ) (hr : 2 ≤ r) (x : H j ((inverseImage j).obj G) r) :
    counitAddEquiv D hfin hclosed hsep j hD G r hr x = counitMap j G r x :=
  rfl

end FiniteSupport

section LowDegree

variable {X : Scheme.{u}} (D : Set X) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme X D))]
  (G : AbelianSheaf.{u, u + 1} X)

/-- The map `H^r(X, G) → H^r(pointScheme X D, i^* G)`: the original unit
`G ⟶ i_* i^* G` on cohomology followed by the finite direct-image comparison. -/
def pointRestriction (r : ℕ) :
    Sheaf.H.{w} G r →+ Sheaf.H.{w'} ((inverseImage (inclusion X D)).obj G) r :=
  letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  (Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
      ((inverseImage (inclusion X D)).obj G) r).toAddMonoidHom.comp
    (Sheaf.H.map ((inverseImageAdjunction (inclusion X D)).unit.app G) r)

theorem pointRestriction_apply (r : ℕ) (x : Sheaf.H.{w} G r) :
    letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
    pointRestriction D hfin hclosed G r x =
      Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
        ((inverseImage (inclusion X D)).obj G) r
        (Sheaf.H.map ((inverseImageAdjunction (inclusion X D)).unit.app G) r x) :=
  rfl

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)

/-- The connecting map `H^{n₀}(pointScheme X D, i^* G) → H^{n₁}_c(U, j^* G)`: the inverse
finite direct-image comparison followed by the original connecting map. -/
def pointBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w'} ((inverseImage (inclusion X D)).obj G) n₀ →+
      H j ((inverseImage j).obj G) n₁ :=
  letI : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  (localizationδ j (inclusion X D) (range_eq_compl_range_inclusion D j hD) G n₀ n₁ h).comp
    (Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
      ((inverseImage (inclusion X D)).obj G) n₀).symm.toAddMonoidHom

theorem pointBoundary_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w'} ((inverseImage (inclusion X D)).obj G) n₀) :
    letI : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
    letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
    pointBoundary D hfin hclosed G j hD n₀ n₁ h x =
      localizationδ j (inclusion X D) (range_eq_compl_range_inclusion D j hD) G n₀ n₁ h
        ((Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
          ((inverseImage (inclusion X D)).obj G) n₀).symm x) :=
  rfl

include hD

/-- Exactness at `H^r(X, G)` with the point-scheme restriction. -/
theorem exact_counitMap_pointRestriction (r : ℕ) :
    Function.Exact (counitMap j G r) (pointRestriction D hfin hclosed G r) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  intro y
  rw [pointRestriction_apply, AddEquiv.map_eq_zero_iff]
  exact exact_counitMap_unitMap j (inclusion X D) (range_eq_compl_range_inclusion D j hD) G r y

/-- Exactness at `H^{n₀}(pointScheme X D, i^* G)`. -/
theorem exact_pointRestriction_pointBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (pointRestriction D hfin hclosed G n₀)
      (pointBoundary D hfin hclosed G j hD n₀ n₁ h) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  let e := Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
    ((inverseImage (inclusion X D)).obj G) n₀
  intro y
  rw [pointBoundary_apply, exact_unitMap_localizationδ j (inclusion X D)
    (range_eq_compl_range_inclusion D j hD) G n₀ n₁ h (e.symm y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [pointRestriction_apply]; exact (e.eq_symm_apply).mp hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [pointRestriction_apply]; exact (e.symm_apply_apply _).symm⟩

/-- Exactness at `H^{n₁}_c(U, j^* G)` with the point-scheme connecting map. -/
theorem exact_pointBoundary_counitMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (pointBoundary D hfin hclosed G j hD n₀ n₁ h) (counitMap j G n₁) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  let e := Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
    ((inverseImage (inclusion X D)).obj G) n₀
  intro y
  rw [exact_localizationδ_counitMap j (inclusion X D) (range_eq_compl_range_inclusion D j hD)
    G n₀ n₁ h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, by rw [pointBoundary_apply, e.symm_apply_apply]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, rfl⟩

end LowDegree

end AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport
