/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Positive

/-!
# Faithfully flat augmented Amitsur exactness

The complex is the native augmented alternating coface complex of the native
Čech conerve of the original algebra unit, tensored with the original module.
The original augmentation is `m ↦ 1 ⊗ m`. Canonical tensor comparisons identify
its original cofaces recursively with unit insertions in their original order.
For a faithfully flat algebra it is exact in every augmented degree, and the
original unaugmented complex has zero homology in every positive degree.
-/
