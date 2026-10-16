/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Restriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness
public import Aglib.Algebra.Category.ModuleCat.Localization.Exactness
public import Aglib.AlgebraicGeometry.Cohomology.Cech.AffineDegreeOne
/-!
# Higher affine quasicoherent Cech exactness

For a finite principal cover of an arbitrary affine scheme and arbitrary
quasicoherent module-sheaf coefficients, `principalCech_exactAt_succ` proves
exactness in every positive degree of mathlib's original `cechComplexFunctor`.

The map `principalCechRestriction` uses actual restrictions to intersections
with a principal open. Every term is proved to be the corresponding module
localization. Restriction to a member contracts the actual complex, and
exactness is then detected on this finite principal cover. There are no
domain, noetherianity, or nontrivial-ring assumptions.

This is exactness of the actual Cech complex. The comparison with higher
right-derived global sections remains a separate theorem.

Reference: Stacks Project, [Tag 01X9](https://stacks.math.columbia.edu/tag/01X9).
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum CategoryTheory.Cech ModuleCat

namespace AlgebraicGeometry.Scheme.Modules.AffineCech

section
variable {R : CommRingCat.{u}} {ι : Type u}

/-- The actual principal-cover Cech complex, using mathlib's existing construction. -/
abbrev principalCechComplex (M : (Spec R).Modules) (f : ι → R) :=
  (cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens))).obj
    (modulesSpecToSheaf.obj M).obj

/-- An invertible cover coordinate gives exactness in every positive degree,
without a quasicoherence hypothesis on the coefficient sheaf. -/
lemma principalCech_exactAt_succ_of_isUnit (M : (Spec R).Modules)
    (f : ι → R) {i₀ : ι} (hi : IsUnit (f i₀)) (n : ℕ) :
    (principalCechComplex M f).ExactAt (n + 1) := by
  apply cechComplex_exactAt_succ_of_terminal_component
    (hT := isTerminalTop) (i₀ := i₀)
  apply homOfLE
  intro x _
  exact fun hx => x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hx hi)

/-- After geometric localization at any cover coordinate, the actual Cech
complex of the localized principal opens is exact in all positive degrees. -/
lemma principalCech_exactAt_succ_away (f : ι → R) (i₀ : ι)
    (S : CommRingCat.{u}) [Algebra R S] [IsLocalization.Away (f i₀) S]
    (M : (Spec S).Modules) (n : ℕ) :
    (principalCechComplex M (fun i => algebraMap R S (f i))).ExactAt (n + 1) :=
  principalCech_exactAt_succ_of_isUnit M _ (i₀ := i₀)
    (IsLocalization.Away.algebraMap_isUnit (f i₀)) n

end

lemma basicOpen_finset_prod {R : CommRingCat.{u}} {β : Type v}
    (s : Finset β) (f : β → R) :
    PrimeSpectrum.basicOpen (∏ i ∈ s, f i) = ⨅ i ∈ s, PrimeSpectrum.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, PrimeSpectrum.basicOpen_mul, ih, iInf_or, iInf_inf_eq]

lemma principal_product_eq {R : CommRingCat.{u}} {β : Type v} [Fintype β]
    (f : β → R) :
    (∏ᶜ fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens)) =
      PrimeSpectrum.basicOpen (∏ i, f i) := by
  rw [basicOpen_finset_prod]
  simp only [Finset.mem_univ, iInf_true]
  apply le_antisymm
  · exact le_iInf fun i => leOfHom (Limits.Pi.π _ i)
  · exact leOfHom (Limits.Pi.lift fun i => homOfLE (iInf_le _ i))

/-- The actual Cech cochain map obtained by restricting all sections to
intersections with the principal open `D(r)`. -/
def principalCechRestriction {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {ι : Type u} (f : ι → R) (r : R) :=
  (cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens))).map
    (restrictPresheaf (modulesSpecToSheaf.obj M).obj (PrimeSpectrum.basicOpen r))

/-- Every degree of the actual Cech restriction is localization at `r`
for a finite principal cover and quasicoherent coefficients. -/
lemma principalCechRestriction_isLocalized {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (f : ι → R) (r : R) (n : ℕ) :
    IsLocalizedModule.Away r ((principalCechRestriction M f r).f n).hom := by
  let : Fintype ι := Fintype.ofFinite ι
  change IsLocalizedModule.Away r
    (Limits.Pi.map (fun a : Fin (n + 1) → ι =>
      (restrictPresheaf (modulesSpecToSheaf.obj M).obj (PrimeSpectrum.basicOpen r)).app
        (op (∏ᶜ (fun i => (PrimeSpectrum.basicOpen (f (a i)) : (Spec R).Opens)))))).hom
  have h (a : Fin (n + 1) → ι) : IsLocalizedModule.Away r
      ((restrictPresheaf (modulesSpecToSheaf.obj M).obj (PrimeSpectrum.basicOpen r)).app
        (op (∏ᶜ (fun i => (PrimeSpectrum.basicOpen (f (a i)) : (Spec R).Opens))))).hom := by
    change IsLocalizedModule.Away r
      (Scheme.Modules.QuasiCoherent.AffineSections.restriction M
        (∏ᶜ (fun i => (PrimeSpectrum.basicOpen (f (a i)) : (Spec R).Opens))) r)
    rw [principal_product_eq]
    exact (Scheme.Modules.QuasiCoherent.AffineSections.clearsDenominators_iff_isLocalized
      M _ r).mp
      (Scheme.Modules.QuasiCoherent.AffineSections.clearsDenominators_basicOpen M _ r)
  let := h
  exact isLocalizedModule_piMap (.powers r) _

/-- The actual principal-cover Cech complex of a quasicoherent sheaf on an
affine scheme is exact in every positive degree. -/
theorem principalCech_exactAt_succ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (f : ι → R) (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤) (n : ℕ) :
    (principalCechComplex M f).ExactAt (n + 1) := by
  let S := (principalCechComplex M f).sc (n + 1)
  let T (r : Set.range f) :=
    ((cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens))).obj
      ((intersectFunctor (X := TopCat.of (Spec R)) (PrimeSpectrum.basicOpen r.val)).op ⋙
        (modulesSpecToSheaf.obj M).obj)).sc (n + 1)
  let q (r : Set.range f) : S ⟶ T r :=
    (HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
      (principalCechRestriction M f r.val)
  let : ∀ r, IsLocalizedModule.Away r.val (q r).τ₁.hom := fun r =>
    principalCechRestriction_isLocalized M f r.val _
  let : ∀ r, IsLocalizedModule.Away r.val (q r).τ₂.hom := fun r =>
    principalCechRestriction_isLocalized M f r.val _
  let : ∀ r, IsLocalizedModule.Away r.val (q r).τ₃.hom := fun r =>
    principalCechRestriction_isLocalized M f r.val _
  apply shortComplex_exact_of_isLocalized_span S (Set.range f)
    (iSup_basicOpen_eq_top_iff.mp hcover) T q
  intro r
  obtain ⟨i, hi⟩ := r.property
  have h := restrictedCech_exactAt_succ
    (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens)) (modulesSpecToSheaf.obj M).obj i n
  change ((cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens))).obj
    ((intersectFunctor (X := TopCat.of (Spec R)) (PrimeSpectrum.basicOpen r.val)).op ⋙
      (modulesSpecToSheaf.obj M).obj)).ExactAt (n + 1)
  simpa only [hi] using h

end AlgebraicGeometry.Scheme.Modules.AffineCech
