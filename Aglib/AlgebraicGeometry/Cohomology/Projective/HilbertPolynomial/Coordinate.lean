/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.TwistMultiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Bilinear

/-!
# Modules killed by a global twist section

A module `F` on actual polynomial projective space is killed by a global section `s` of
`O(a)` when `twistingTensorMultiply a d s` vanishes on `F` for every twist `d`. This class
is closed under subobjects, quotients and twists. Multiplication by `s` at twist zero,
`ν = s : F → O(a + 0) ⊗ F`, has kernel and cokernel killed by `s`. The cokernel step is local
on the coordinate charts, where `O(a)` has an original generator and `s` is its coefficient
times that generator. A module killed by every coordinate `Xᵢ` is zero, since `Xᵢ` is the
generator of `O(1)` on its own chart.

For a global section `s` of `O(1)`, `frameCoefficient R ι s i hV` is its frame coefficient
`s / Xᵢ` on a subopen `V` of the chart `D₊(Xᵢ)`: it commutes with restriction
(`frameCoefficient_eq_map`), is additive and linear over global functions, and is one for
`s = Xᵢ`. If multiplication by `s` vanishes on `F`, the frame coefficients kill the sections of
`F` (`frameCoefficient_smul_eq_zero`). Hence if every frame coefficient of `s` is a
nonzerodivisor on the sections of `M` over the chart subopens, multiplication by `s`,
`M ≅ O(0) ⊗ M → O(1 + 0) ⊗ M`, is a monomorphism
(`mono_twistingTensorMultiply_of_isSMulRegular`): its kernel is killed by `s`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The coordinate `Xᵢ` as a global section of `O(1)`. -/
def coordinateSection (i : ι) : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤) :=
  homogeneousSection R ι 1 (coordinatePower R ι 1 i)

/-- Multiplication by the global section `s` of `O(a)` vanishes on every twist of `F`. -/
def IsKilledByTwistSection (a : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) : Prop :=
  ∀ d : ℤ, (twistingTensorMultiply R ι a d s).app F = 0

variable {R ι}

namespace IsKilledByTwistSection

variable {a : ℤ} {s : (twistingSheaf R ι a).val.obj (op ⊤)}

/-- Subobjects of killed modules are killed. -/
theorem of_mono {K F : (ProjectiveSpace R ι).Modules} (j : K ⟶ F) [Mono j]
    (hF : IsKilledByTwistSection R ι a s F) : IsKilledByTwistSection R ι a s K := by
  intro d
  have hn := (twistingTensorMultiply R ι a d s).naturality j
  rw [hF d, comp_zero] at hn
  rw [← cancel_mono ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (a + d))).map j), zero_comp]
  exact hn.symm

/-- Quotients of killed modules are killed. -/
theorem of_epi {F C : (ProjectiveSpace R ι).Modules} (p : F ⟶ C) [Epi p]
    (hF : IsKilledByTwistSection R ι a s F) : IsKilledByTwistSection R ι a s C := by
  intro d
  have hn := (twistingTensorMultiply R ι a d s).naturality p
  rw [hF d, zero_comp] at hn
  rw [← cancel_epi ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι d)).map p), comp_zero]
  exact hn

/-- Twists of killed modules are killed. -/
theorem tensor {F : (ProjectiveSpace R ι).Modules} (hF : IsKilledByTwistSection R ι a s F)
    (e : ℤ) : IsKilledByTwistSection R ι a s
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).obj F) :=
  fun d => twistingTensorMultiply_app_tensor_eq_zero R ι a e d s F (hF e)

/-- If multiplication by `s` vanishes on `F` at twist `d = 0`, it vanishes at every twist,
so `F` is killed by `s`. Here `zero` refers to the twist degree, not to the module. -/
theorem of_zero {F : (ProjectiveSpace R ι).Modules}
    (hF : (twistingTensorMultiply R ι a 0 s).app F = 0) : IsKilledByTwistSection R ι a s F := by
  have h0 : IsKilledByTwistSection R ι a s
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι 0)).obj F) :=
    fun d => twistingTensorMultiply_app_tensor_eq_zero R ι a 0 d s F hF
  exact h0.of_mono ((twistingTensorZeroIso R ι).inv.app F)

/-- The kernel of multiplication by `s` at twist zero is killed by `s`. -/
theorem of_comp_eq_zero {K F : (ProjectiveSpace R ι).Modules} (j : K ⟶ F) [Mono j]
    (hj : j ≫ (twistingTensorZeroIso R ι).inv.app F ≫ (twistingTensorMultiply R ι a 0 s).app F
      = 0) : IsKilledByTwistSection R ι a s K := by
  apply of_zero
  have h1 := (twistingTensorMultiply R ι a 0 s).naturality j
  have h2 := (twistingTensorZeroIso R ι).inv.naturality j
  have h3 : (twistingTensorZeroIso R ι).inv.app K ≫ (twistingTensorMultiply R ι a 0 s).app K ≫
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + 0))).map j = 0 := by
    rw [← h1, ← Category.assoc, ← h2]
    simpa only [Functor.id_map, Category.assoc] using hj
  rw [← cancel_mono ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (a + 0))).map j), zero_comp]
  rw [← cancel_epi ((twistingTensorZeroIso R ι).inv.app K), comp_zero]
  exact h3

end IsKilledByTwistSection

variable (R ι) in
-- Frame coefficients of twist sections live in `Γ(ProjectiveSpace R ι, V)` only after
-- unfolding the module presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate `Xᵢ` has frame coefficient one on every subopen of its own chart. -/
theorem coordinateSection_coefficient (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hV : V ≤ coordinateOpen R ι i) :
    twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i hV
      ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
        (coordinateSection R ι i)) = 1 := by
  have hres : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
      (coordinateSection R ι i) = (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE hV).op
        ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map
          (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op (coordinateSection R ι i)) := by
    rw [← PresheafOfModules.map_comp_apply]
    exact (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.congr_map_apply (Subsingleton.elim _ _) _
  rw [hres, twistingSectionsEquiv_restrict R ι ((1 : ℕ) : ℤ) i hV le_rfl]
  rw [show twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i le_rfl
      ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE le_top).op (coordinateSection R ι i)) = 1
    from homogeneousSection_coordinatePower_local R ι 1 i, map_one]

variable (R ι) in
-- Frame coefficients of twist sections live in `Γ(ProjectiveSpace R ι, V)` only after
-- unfolding the module presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- A module on which every coordinate multiplication `O(-1) ⊗ F → O(0) ⊗ F` vanishes is zero. -/
theorem isZero_of_coordinate_eq_zero (F : (ProjectiveSpace R ι).Modules)
    (hF : ∀ i, (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) (-1)
      (coordinateSection R ι i)).app F = 0) :
    IsZero F := by
  have hsec (i : ι) (V : (ProjectiveSpace R ι).Opens) (hV : V ≤ coordinateOpen R ι i)
      (n : Γ(F, V)) : n = 0 := by
    let g := twistingGenerator R ι (-1) i hV
    let xV := (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
      (coordinateSection R ι i)
    have h1 : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (((1 : ℕ) : ℤ) + -1))
        F V (twistingSectionMul R ι ((1 : ℕ) : ℤ) (-1) V xV g) n = 0 := by
      rw [← twistingTensorMultiply_section, hF i]
      rfl
    have h0 : ((1 : ℕ) : ℤ) + -1 = 0 := by norm_num
    have h2 := moduleTensorSection_eqToHom_eq_zero R ι h0 F V _ n h1
    have hcoef : (twistingZeroIso R ι).hom.val.app (op V)
        ((eqToHom (congrArg (twistingSheaf R ι) h0)).val.app (op V)
          (twistingSectionMul R ι ((1 : ℕ) : ℤ) (-1) V xV g)) =
            (1 : Γ(ProjectiveSpace R ι, V)) := by
      change (twistingZeroToUnit R ι).val.app (op V) _ = (1 : Γ(ProjectiveSpace R ι, V))
      rw [twistingZeroToUnit_app R ι i hV, twistingSectionsEquiv_eqToHom R ι h0 i hV,
        twistingSectionsEquiv_mul, coordinateSection_coefficient R ι i hV,
        twistingSectionsEquiv_generator, one_mul]
    have h3 := congrArg (((twistingTensorZeroIso R ι).hom.app F).val.app (op V)) h2
    rw [twistingTensorZeroIso_hom_section, tensorLeftUnitIso_hom_section, map_zero, hcoef,
      one_smul] at h3
    exact h3
  rw [IsZero.iff_id_eq_zero]
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hV n
  rw [hsec i V hV n, map_zero, map_zero]

variable (R ι) in
-- Section types of twists and of `Γ` agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Twist multiplication is linear in its first factor. -/
theorem twistingSectionMul_smul_left (a b : ℤ) (V : (ProjectiveSpace R ι).Opens)
    (r : Γ(ProjectiveSpace R ι, V)) (x : (twistingSheaf R ι a).val.obj (op V))
    (y : (twistingSheaf R ι b).val.obj (op V)) :
    twistingSectionMul R ι a b V (r • x) y = r • twistingSectionMul R ι a b V x y :=
  LinearMap.congr_fun ((twistingSectionMulLinear R ι a b V).map_smul r x) y

variable (R ι) in
-- Section types of twists and of `Γ` agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of `O(e) ⊗ (O(d) ⊗ F)` are determined by nested original pure tensors over
the subopens of the standard coordinate charts. -/
theorem twistingTensor_nested_hom_ext (e d : ℤ) (F G : (ProjectiveSpace R ι).Modules)
    {f g : (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).obj
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) ⟶ G}
    (h : ∀ (k : ι) (W : (ProjectiveSpace R ι).Opens) (_ : W ≤ coordinateOpen R ι k)
      (l : Γ(twistingSheaf R ι e, W)) (t : Γ(twistingSheaf R ι d, W)) (n : Γ(F, W)),
      f.val.app (op W) (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι e) _ W l
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F W t n)) =
        g.val.app (op W) (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι e) _ W l
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F W t n))) :
    f = g := by
  apply moduleTensor_nested_hom_ext_of_line (twistingSheaf R ι e) (twistingSheaf R ι d) F
    (fun i => (coordinateOpen R ι i).toScheme) (fun i => (coordinateOpen R ι i).ι)
    (exists_coordinateOpen_mem R ι) (twistingRestrictUnitIso R ι e)
  intro U l t n
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨G.presheaf, G.isSheaf⟩
    (fun k => U ⊓ coordinateOpen R ι k) U (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, iSup_coordinateOpen_eq_top, inf_top_eq])
  intro k
  let ρ : U ⊓ coordinateOpen R ι k ⟶ U := homOfLE inf_le_left
  have hx := moduleTensorSection_restrict (twistingSheaf R ι e)
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) ρ l
    (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F U t n)
  rw [moduleTensorSection_restrict (twistingSheaf R ι d) F ρ t n] at hx
  have hx' : ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).obj
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)).val.map ρ.op
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι e) _ U l
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F U t n)) = _ := hx
  change G.val.map ρ.op (f.val.app (op U) _) = G.val.map ρ.op (g.val.app (op U) _)
  rw [← PresheafOfModules.naturality_apply f.val, ← PresheafOfModules.naturality_apply g.val, hx']
  exact h k _ inf_le_right _ _ _

namespace IsKilledByTwistSection

variable {a : ℤ} {s : (twistingSheaf R ι a).val.obj (op ⊤)}

-- Section types of twists and of `Γ` agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of multiplication by `s` at twist zero is killed by `s`. On a coordinate
chart, `s` is its frame coefficient `σ` times the generator, and `σ • t = s · t₀`. -/
theorem of_cokernel {F C : (ProjectiveSpace R ι).Modules}
    (p : (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + 0))).obj F ⟶ C)
    [Epi p] (hp : (twistingTensorMultiply R ι a 0 s).app F ≫ p = 0) :
    IsKilledByTwistSection R ι a s C := by
  intro d
  rw [← cancel_epi ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι d)).map p), comp_zero, (twistingTensorMultiply R ι a d s).naturality p]
  apply twistingTensor_nested_hom_ext R ι d (a + 0) F _
  intro k W hW l t n
  let sW := (twistingSheaf R ι a).val.map (homOfLE (le_top : W ≤ ⊤)).op s
  let σ := twistingSectionsEquiv R ι a k hW sW
  let t₀ := (twistingSectionsEquiv R ι 0 k hW).symm (twistingSectionsEquiv R ι (a + 0) k hW t)
  have hst : σ • t = twistingSectionMul R ι a 0 W sW t₀ := by
    apply (twistingSectionsEquiv R ι (a + 0) k hW).injective
    rw [LinearEquiv.map_smul, twistingSectionsEquiv_mul, LinearEquiv.apply_symm_apply,
      smul_eq_mul]
  have hsl : twistingSectionMul R ι a d W sW l =
      σ • twistingSectionMul R ι a d W (twistingGenerator R ι a k hW) l := by
    rw [← twistingSectionMul_smul_left, twistingSectionsEquiv_smul_generator]
  have hpt : p.app W (σ • moduleTensorSection (ProjectiveSpace R ι)
      (twistingSheaf R ι (a + 0)) F W t n) = 0 := by
    rw [← moduleTensorSection_smul_left, hst, ← twistingTensorMultiply_section]
    change ((twistingTensorMultiply R ι a 0 s).app F ≫ p).val.app (op W) _ = 0
    rw [hp]
    rfl
  change ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + d))).map p).app
      W (((twistingTensorMultiply R ι a d s).app _).val.app (op W)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) _ W l
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + 0)) F W t n))) = 0
  rw [twistingTensorMultiply_section, moduleTensorLeftFunctor_map_section]
  rw [show (twistingSheaf R ι a).val.map (homOfLE le_top).op s = sW from rfl, hsl,
    moduleTensorSection_smul_left, ← moduleTensorSection_smul_right, ← Hom.app_smul, hpt,
    moduleTensorSection_zero_right]

end IsKilledByTwistSection

/-! ### Frame coefficients and multiplication on the charts -/

section FrameCoefficient

variable (R ι)

-- Frame coefficients of twist sections live in `Γ(ProjectiveSpace R ι, V)` only after
-- unfolding the module presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- The frame coefficient `s / Xᵢ` of a global section `s` of `O(1)` on a subopen `V` of the
chart `D₊(Xᵢ)`. -/
def frameCoefficient (s : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i) :
    Γ(ProjectiveSpace R ι, V) :=
  twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i hV
    ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op s)

-- Frame coefficients live in `Γ(ProjectiveSpace R ι, V)` only after unfolding the module
-- presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- Frame coefficients commute with restriction to a smaller subopen of the chart. -/
theorem frameCoefficient_eq_map (s : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i) :
    frameCoefficient R ι s i hV =
      (ProjectiveSpace R ι).presheaf.map (homOfLE hV).op (frameCoefficient R ι s i le_rfl) := by
  have hres : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op s =
      (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE hV).op
        ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map
          (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op s) := by
    rw [← PresheafOfModules.map_comp_apply]
    exact (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.congr_map_apply (Subsingleton.elim _ _) _
  unfold frameCoefficient
  rw [hres, twistingSectionsEquiv_restrict R ι ((1 : ℕ) : ℤ) i hV le_rfl]

-- Frame coefficients live in `Γ(ProjectiveSpace R ι, V)` only after unfolding the module
-- presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- Frame coefficients are additive. -/
theorem frameCoefficient_add (s t : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i) :
    frameCoefficient R ι (s + t) i hV =
      frameCoefficient R ι s i hV + frameCoefficient R ι t i hV := by
  unfold frameCoefficient
  rw [map_add, map_add]

/-- The frame coefficient of `r • s`, for a global function `r`, is `r|_V` times that of `s`. -/
theorem frameCoefficient_smul (r : (ProjectiveSpace R ι).ringCatSheaf.obj.obj (op ⊤))
    (s : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i) :
    frameCoefficient R ι (r • s) i hV =
      (ProjectiveSpace R ι).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r *
        frameCoefficient R ι s i hV := by
  unfold frameCoefficient
  rw [PresheafOfModules.map_smul]
  exact (twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i hV).map_smul
    ((ProjectiveSpace R ι).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) _

/-- The coordinate `Xᵢ` has frame coefficient one on the subopens of its own chart. -/
theorem frameCoefficient_coordinateSection (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hV : V ≤ coordinateOpen R ι i) :
    frameCoefficient R ι (coordinateSection R ι i) i hV = 1 :=
  coordinateSection_coefficient R ι i hV

-- Frame coefficients of twist sections live in `Γ(ProjectiveSpace R ι, V)` only after
-- unfolding the module presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- If multiplication by `s : Γ(O(1))` vanishes on `F` at twist `-1`, the frame coefficient of
`s` on a subopen `V` of the chart `D₊(Xᵢ)` kills every section of `F` over `V`. -/
theorem frameCoefficient_smul_eq_zero (s : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules)
    (hF : (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) (-1) s).app F = 0) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i) (n : Γ(F, V)) :
    frameCoefficient R ι s i hV • n = 0 := by
  let g := twistingGenerator R ι (-1) i hV
  let sV := (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op s
  have h1 : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (((1 : ℕ) : ℤ) + -1))
      F V (twistingSectionMul R ι ((1 : ℕ) : ℤ) (-1) V sV g) n = 0 := by
    rw [← twistingTensorMultiply_section, hF]
    rfl
  have h0 : ((1 : ℕ) : ℤ) + -1 = 0 := by norm_num
  have h2 := moduleTensorSection_eqToHom_eq_zero R ι h0 F V _ n h1
  have hcoef : (twistingZeroIso R ι).hom.val.app (op V)
      ((eqToHom (congrArg (twistingSheaf R ι) h0)).val.app (op V)
        (twistingSectionMul R ι ((1 : ℕ) : ℤ) (-1) V sV g)) =
          twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i hV sV := by
    change (twistingZeroToUnit R ι).val.app (op V) _ = _
    rw [twistingZeroToUnit_app R ι i hV, twistingSectionsEquiv_eqToHom R ι h0 i hV,
      twistingSectionsEquiv_mul, twistingSectionsEquiv_generator, mul_one]
  have h3 := congrArg (((twistingTensorZeroIso R ι).hom.app F).val.app (op V)) h2
  rw [twistingTensorZeroIso_hom_section, tensorLeftUnitIso_hom_section, map_zero, hcoef] at h3
  exact h3

-- Module sections and their scalar ring `Γ(ProjectiveSpace R ι, V)` agree with the presheaf
-- of modules only after unfolding; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- **Multiplication by a section of `O(1)` is mono on the charts' regular locus**: if on every
subopen `V` of every chart `D₊(Xᵢ)` the frame coefficient of `s` is a nonzerodivisor on
`Γ(M, V)`, then multiplication by `s`, `M ≅ O(0) ⊗ M → O(1 + 0) ⊗ M`, is a monomorphism. -/
theorem mono_twistingTensorMultiply_of_isSMulRegular
    (s : (twistingSheaf R ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) (M : (ProjectiveSpace R ι).Modules)
    (hreg : ∀ (i : ι) (V : (ProjectiveSpace R ι).Opens) (hV : V ≤ coordinateOpen R ι i),
      IsSMulRegular Γ(M, V) (frameCoefficient R ι s i hV)) :
    Mono ((twistingTensorZeroIso R ι).inv.app M ≫
      (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) 0 s).app M) := by
  let f := (twistingTensorZeroIso R ι).inv.app M ≫
    (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) 0 s).app M
  apply Preadditive.mono_of_isZero_kernel
  have hK : IsKilledByTwistSection R ι ((1 : ℕ) : ℤ) s (kernel f) :=
    IsKilledByTwistSection.of_comp_eq_zero (kernel.ι f) (by
      rw [← Category.assoc]
      exact kernel.condition f)
  have hsec (i : ι) (V : (ProjectiveSpace R ι).Opens) (hV : V ≤ coordinateOpen R ι i)
      (n : Γ(kernel f, V)) : (kernel.ι f).val.app (op V) n = 0 := by
    have h := frameCoefficient_smul_eq_zero R ι s (kernel f) (hK (-1)) i hV n
    apply hreg i V hV
    change frameCoefficient R ι s i hV • (kernel.ι f).val.app (op V) n =
      frameCoefficient R ι s i hV • 0
    calc frameCoefficient R ι s i hV • (kernel.ι f).val.app (op V) n
        = (kernel.ι f).val.app (op V) (frameCoefficient R ι s i hV • n) :=
          (_root_.map_smul _ _ _).symm
      _ = 0 := by rw [h, map_zero]
      _ = frameCoefficient R ι s i hV • 0 := (smul_zero _).symm
  have hι : kernel.ι f = 0 := by
    apply hom_ext_of_coordinateSubopens R ι
    intro i V hV n
    rw [hsec i V hV n]
    rfl
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono (kernel.ι f), hι, comp_zero, zero_comp]

end FrameCoefficient

end AlgebraicGeometry.ProjectiveSpace
