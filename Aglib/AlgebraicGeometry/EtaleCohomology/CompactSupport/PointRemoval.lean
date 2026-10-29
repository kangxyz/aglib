/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FiniteComplement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.FullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-!
# Removing finitely many points from an open subscheme

Let `jV : V ⟶ U` and `jU : U ⟶ X` be open immersions, so that `V` is an open subscheme of
`X` through `jV ≫ jU`. Suppose that `D = X − V` is a finite set of closed points of `X` with
separably closed residue fields, and let `i = FiniteClosedSupport.inclusion X D` be the
literal coproduct of their residue-field spectra. For an abelian sheaf `F` on `U`, the
original open-closed sequence on `X` for `jV ≫ jU` and `i`, applied to `j_{U!} F`, is the short
exact sequence

`0 → j_{V!}(F|_V) → j_{U!} F → i_* i^* (j_{U!} F) → 0`

(Milne, *Lectures on Étale Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94). Its first
term uses the restriction isomorphism `(jV ≫ jU)^* j_{U!} F ≅ jV^* F`, given by the original
composition of inverse images and the inverse of the original extension-by-zero unit
(Stacks, Tag 0F70); its first arrow is then the original counit for `jV ≫ jU`, and its second
arrow is the original unit for `i`. The third term is `i_* i^* (j_{U!} F)` for the finite
support `i` of `X − V`; its cohomology is identified by the finite direct-image comparison with
the cohomology of `i^* (j_{U!} F)` on the finite point scheme `pointScheme X D`, and it vanishes
in positive degrees. It is not further restricted here to the points of `U − V`. The resulting
long exact sequence is

`… → H^r_c(V, F|_V) → H^r_c(U, F) → H^r(X, i_* i^* j_{U!} F) → H^{r+1}_c(V, F|_V) → …`,

so `H^r_c(V, F|_V) → H^r_c(U, F)` is bijective for `r ≥ 2` and surjective for `r = 1`, and
`0 → H^0_c(V, F|_V) → H^0_c(U, F) → H^0(pointScheme X D, i^* j_{U!} F) → H^1_c(V, F|_V) →
H^1_c(U, F) → 0` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport

attribute [local instance] hasSheafifyLarge

open Curves.FiniteClosedSupport

variable {V U X : Scheme.{u}} (jV : V ⟶ U) (jU : U ⟶ X) [IsOpenImmersion jU]
  (F : AbelianSheaf.{u, u + 1} U)

/-- The restriction to `V` of the extension by zero of `F` is the restriction of `F`: the
original composition of inverse images followed by the inverse of the original unit. -/
def restrictionExtensionIso :
    (inverseImage (jV ≫ jU)).obj ((etaleLowerShriek jU).obj F) ≅ (inverseImage jV).obj F :=
  (inverseImageComp jU jV).app ((etaleLowerShriek jU).obj F) ≪≫
    (inverseImage jV).mapIso ((etaleLowerShriekInverseImageIso jU).app F)

variable [IsOpenImmersion jV]

/-- The map `j_{V!}(F|_V) ⟶ j_{U!} F`: the restriction isomorphism followed by the original
counit of the extension by zero along `jV ≫ jU`. -/
def extensionMap :
    (etaleLowerShriek (jV ≫ jU)).obj ((inverseImage jV).obj F) ⟶ (etaleLowerShriek jU).obj F :=
  (etaleLowerShriek (jV ≫ jU)).map (restrictionExtensionIso jV jU F).inv ≫
    (etaleLowerShriekAdjunction (jV ≫ jU)).counit.app ((etaleLowerShriek jU).obj F)

variable (D : Set X) (hD : Set.range (jV ≫ jU) = Dᶜ) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))

/-- The short complex `j_{V!}(F|_V) ⟶ j_{U!} F ⟶ i_* i^* (j_{U!} F)` on `X`. -/
def pointRemovalShortComplex : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  ShortComplex.mk (extensionMap jV jU F)
    ((inverseImageAdjunction (inclusion X D)).unit.app ((etaleLowerShriek jU).obj F)) (by
      let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
      rw [extensionMap, Category.assoc,
        localization_counit_comp_unit (jV ≫ jU) (inclusion X D)
          (range_eq_compl_range_inclusion D (jV ≫ jU) hD), comp_zero])

/-- The point-removal sequence is short exact: it is isomorphic to the original open-closed
localization sequence of `j_{U!} F` for `jV ≫ jU` and the finite support. -/
theorem pointRemoval_shortExact :
    (pointRemovalShortComplex jV jU F D hD hfin hclosed).ShortExact := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  refine ShortComplex.shortExact_of_iso ?_
    (abelianLocalization_shortExact (jV ≫ jU) (inclusion X D)
      (range_eq_compl_range_inclusion D (jV ≫ jU) hD) ((etaleLowerShriek jU).obj F))
  exact ShortComplex.isoMk
    ((etaleLowerShriek (jV ≫ jU)).mapIso (restrictionExtensionIso jV jU F))
    (Iso.refl _) (Iso.refl _)
    (by simp [pointRemovalShortComplex, abelianLocalizationShortComplex, extensionMap])
    (by simp [pointRemovalShortComplex, abelianLocalizationShortComplex])

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The map `H^r_c(V, F|_V) → H^r_c(U, F)` induced by `extensionMap`. -/
def extensionCohomologyMap (r : ℕ) :
    H (jV ≫ jU) ((inverseImage jV).obj F) r →+ H jU F r :=
  Sheaf.H.map (extensionMap jV jU F) r

/-- The connecting map `H^{n₀}(X, i_* i^* j_{U!} F) → H^{n₁}_c(V, F|_V)` of the point-removal
sequence. -/
def pointRemovalδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w} ((directImage (inclusion X D)).obj
        ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F))) n₀ →+
      H (jV ≫ jU) ((inverseImage jV).obj F) n₁ :=
  Sheaf.H.δ (pointRemoval_shortExact jV jU F D hD hfin hclosed) n₀ n₁ h

/-- The long exact sequence `H^{n₀}_c(V, F|_V) → H^{n₀}_c(U, F) → H^{n₀}(X, i_* i^* j_{U!} F)
→ H^{n₁}_c(V, F|_V) → H^{n₁}_c(U, F) → H^{n₁}(X, i_* i^* j_{U!} F)`. -/
abbrev pointRemovalSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  Sheaf.H.longSequence (pointRemoval_shortExact jV jU F D hD hfin hclosed) n₀ n₁ h

theorem pointRemovalSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (pointRemovalSequence jV jU F D hD hfin hclosed n₀ n₁ h).Exact :=
  Sheaf.H.longSequence_exact _ n₀ n₁ h

include hD hfin hclosed in
/-- Exactness at `H^r_c(U, F)`. -/
theorem exact_extensionCohomologyMap_unitMap (r : ℕ) :
    Function.Exact (extensionCohomologyMap jV jU F r)
      (Sheaf.H.map ((inverseImageAdjunction (inclusion X D)).unit.app
        ((etaleLowerShriek jU).obj F)) r) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (pointRemoval_shortExact jV jU F D hD hfin hclosed) r)

/-- Exactness at `H^{n₀}(X, i_* i^* j_{U!} F)`. -/
theorem exact_unitMap_pointRemovalδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (Sheaf.H.map ((inverseImageAdjunction (inclusion X D)).unit.app
        ((etaleLowerShriek jU).obj F)) n₀)
      (pointRemovalδ jV jU F D hD hfin hclosed n₀ n₁ h) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (pointRemoval_shortExact jV jU F D hD hfin hclosed) n₀ n₁ h)

/-- Exactness at `H^{n₁}_c(V, F|_V)`. -/
theorem exact_pointRemovalδ_extensionCohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (pointRemovalδ jV jU F D hD hfin hclosed n₀ n₁ h)
      (extensionCohomologyMap jV jU F n₁) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (pointRemoval_shortExact jV jU F D hD hfin hclosed) n₀ n₁ h)

include hD hfin hclosed in
/-- The extension map is injective in degree zero. -/
theorem extensionCohomologyMap_zero_injective :
    Function.Injective (extensionCohomologyMap jV jU F 0) := by
  have : Mono (extensionMap jV jU F) :=
    (pointRemoval_shortExact jV jU F D hD hfin hclosed).mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono _ _

variable (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))

include hfin hclosed hsep in
/-- The third term `i_* i^* (j_{U!} F)` is acyclic in positive degree. -/
theorem subsingleton_H_pointRemoval_third_of_sepClosed (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w} ((directImage (inclusion X D)).obj
      ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F))) r) :=
  subsingleton_H_directImage_inclusion_of_sepClosed D hfin hclosed hsep _ r hr

section Bijective

include hD hfin hclosed hsep

/-- `H^r_c(V, F|_V) → H^r_c(U, F)` is surjective in positive degree. -/
theorem extensionCohomologyMap_surjective_of_sepClosed (r : ℕ) (hr : 0 < r) :
    Function.Surjective (extensionCohomologyMap jV jU F r) := by
  intro y
  have : Subsingleton (Sheaf.H.{w} ((inverseImage (inclusion X D) ⋙
      directImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) r) :=
    subsingleton_H_pointRemoval_third_of_sepClosed jU F D hfin hclosed hsep r hr
  exact (exact_extensionCohomologyMap_unitMap jV jU F D hD hfin hclosed r y).mp
    (Subsingleton.elim _ _)

/-- `H^r_c(V, F|_V) → H^r_c(U, F)` is injective in degree at least two. -/
theorem extensionCohomologyMap_injective_of_sepClosed (r : ℕ) (hr : 2 ≤ r) :
    Function.Injective (extensionCohomologyMap jV jU F r) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have := subsingleton_H_pointRemoval_third_of_sepClosed jU F D hfin hclosed hsep q (by omega)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ :=
    (exact_pointRemovalδ_extensionCohomologyMap jV jU F D hD hfin hclosed q (q + 1) rfl x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- `H^r_c(V, F|_V) → H^r_c(U, F)` is bijective in degree at least two. -/
theorem extensionCohomologyMap_bijective_of_sepClosed (r : ℕ) (hr : 2 ≤ r) :
    Function.Bijective (extensionCohomologyMap jV jU F r) :=
  ⟨extensionCohomologyMap_injective_of_sepClosed jV jU F D hD hfin hclosed hsep r hr,
    extensionCohomologyMap_surjective_of_sepClosed jV jU F D hD hfin hclosed hsep r (by omega)⟩

/-- The isomorphism `H^r_c(V, F|_V) ≃+ H^r_c(U, F)` for `r ≥ 2`. -/
def extensionCohomologyAddEquiv (r : ℕ) (hr : 2 ≤ r) :
    H (jV ≫ jU) ((inverseImage jV).obj F) r ≃+ H jU F r :=
  AddEquiv.ofBijective (extensionCohomologyMap jV jU F r)
    (extensionCohomologyMap_bijective_of_sepClosed jV jU F D hD hfin hclosed hsep r hr)

theorem extensionCohomologyAddEquiv_apply (r : ℕ) (hr : 2 ≤ r)
    (x : H (jV ≫ jU) ((inverseImage jV).obj F) r) :
    extensionCohomologyAddEquiv jV jU F D hD hfin hclosed hsep r hr x =
      extensionCohomologyMap jV jU F r x :=
  rfl

end Bijective

section LowDegree

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme X D))]

/-- The connecting map `H^{n₀}(pointScheme X D, i^* j_{U!} F) → H^{n₁}_c(V, F|_V)`: the inverse
finite direct-image comparison followed by the original connecting map. -/
def pointRemovalBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w'} ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀ →+
      H (jV ≫ jU) ((inverseImage jV).obj F) n₁ :=
  letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  (pointRemovalδ jV jU F D hD hfin hclosed n₀ n₁ h).comp
    (Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
      ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀).symm.toAddMonoidHom

theorem pointRemovalBoundary_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w'} ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀) :
    letI : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
    pointRemovalBoundary jV jU F D hD hfin hclosed n₀ n₁ h x =
      pointRemovalδ jV jU F D hD hfin hclosed n₀ n₁ h
        ((Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
          ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀).symm x) :=
  rfl

include hD

/-- Exactness at `H^r_c(U, F)` with the point-scheme restriction of `j_{U!} F`. -/
theorem exact_extensionCohomologyMap_pointRestriction (r : ℕ) :
    Function.Exact (extensionCohomologyMap jV jU F r)
      (pointRestriction D hfin hclosed ((etaleLowerShriek jU).obj F) r) := by
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  intro y
  rw [pointRestriction_apply, AddEquiv.map_eq_zero_iff]
  exact exact_extensionCohomologyMap_unitMap jV jU F D hD hfin hclosed r y

/-- Exactness at `H^{n₀}(pointScheme X D, i^* j_{U!} F)`. -/
theorem exact_pointRestriction_pointRemovalBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (pointRestriction D hfin hclosed ((etaleLowerShriek jU).obj F) n₀)
      (pointRemovalBoundary jV jU F D hD hfin hclosed n₀ n₁ h) := by
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  let e := Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
    ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀
  intro y
  rw [pointRemovalBoundary_apply,
    exact_unitMap_pointRemovalδ jV jU F D hD hfin hclosed n₀ n₁ h (e.symm y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [pointRestriction_apply]; exact (e.eq_symm_apply).mp hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [pointRestriction_apply]; exact (e.symm_apply_apply _).symm⟩

/-- Exactness at `H^{n₁}_c(V, F|_V)` with the point-scheme connecting map. -/
theorem exact_pointRemovalBoundary_extensionCohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (pointRemovalBoundary jV jU F D hD hfin hclosed n₀ n₁ h)
      (extensionCohomologyMap jV jU F n₁) := by
  let : IsFinite (inclusion X D) := inclusion_isFinite X D hfin hclosed
  let e := Finite.finiteCohomologyDirectImageAddEquiv (inclusion X D)
    ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F)) n₀
  intro y
  rw [exact_pointRemovalδ_extensionCohomologyMap jV jU F D hD hfin hclosed n₀ n₁ h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, by rw [pointRemovalBoundary_apply, e.symm_apply_apply]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, rfl⟩

end LowDegree

end AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport
