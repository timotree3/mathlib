/-
Copyright (c) 2022 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import analysis.convex.star
import topology.homotopy.contractible

universes u v

variables {E : Type v} [topological_space E] [add_comm_group E] [topological_add_group E]
variables [module ℝ E] [has_continuous_smul ℝ E]

open_locale unit_interval continuous_map

open continuous_map

namespace star_convex

def straight_line_homotopy {X : set E} {x : E} (hXn : X.nonempty) (hX : star_convex ℝ x X)
  {Y : Type u} [topological_space Y] (f : C(Y, X)) :
  f.homotopy (continuous_map.const _ ⟨x, hX.mem hXn⟩) :=
{ to_fun := λ p, ⟨(p.1 : ℝ) • x + (σ p.1 : ℝ) • f p.2, hX (f p.2).2 (unit_interval.nonneg _)
    (unit_interval.nonneg _) (by simp)⟩,
  continuous_to_fun := by continuity,
  map_zero_left' := by simp,
  map_one_left' := by simp } .

def contractible_space {X : set E} {x : E} (hXn : X.nonempty) (hX : star_convex ℝ x X) :
  contractible_space X :=
{ hequiv_unit := ⟨{ to_fun := continuous_map.const X (),
  inv_fun := continuous_map.const unit ⟨x, hX.mem hXn⟩,
  left_inv := ⟨(straight_line_homotopy hXn hX (continuous_map.id X)).symm⟩,
  right_inv := ⟨(homotopy.refl (continuous_map.id unit)).cast (by ext) rfl⟩ }⟩ }

end star_convex

namespace convex

def straight_line_homotopy {X : set E} (hX : convex ℝ X) {Y : Type u} [topological_space Y]
  (f g : C(Y, X)) : f.homotopy g :=
{ to_fun := λ p, ⟨(p.1 : ℝ) • g p.2 + (σ p.1 : ℝ) • f p.2, hX (g p.2).2 (f p.2).2
    (unit_interval.nonneg _) (unit_interval.nonneg _) (by simp)⟩,
  continuous_to_fun := by continuity,
  map_zero_left' := by simp,
  map_one_left' := by simp } .

end convex

example {X : set E} (hX : convex ℝ X) (hXn : X.nonempty) (x : E) (hx : x ∈ X) {Y : Type u}
  [topological_space Y] (f : C(Y, X)) :
  star_convex.straight_line_homotopy hXn (hX.star_convex hx) f =
  convex.straight_line_homotopy hX _ _ := rfl
