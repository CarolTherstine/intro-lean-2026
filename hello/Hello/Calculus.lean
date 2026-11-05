/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Mathlib

@[expose] public section
namespace Hello.Calculus

open Filter Real Topology

/-! ## Limit -/

/- Limit of `2x` as `x → 3` is `6`. -/
example : Tendsto (fun x : ℝ => 2 * x) (𝓝 3) (𝓝 6) := by
  have h : Tendsto (fun x : ℝ => 2 * x) (𝓝 3) (𝓝 (2 * 3)) :=
    (continuous_const.mul continuous_id).tendsto 3
  norm_num at h; exact h

/-- Alternatively, using the ε-δ form. -/
theorem limit_two_mul_eps_delta :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - 3| < δ → |2 * x - 6| < ε := by
  intro ε hε; refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
  rw [show 2 * x - 6 = 2 * (x - 3) by ring, abs_mul]
  norm_num; linarith

/-! ## Derivative -/

/-- $\frac{d}{dx}\,x^3 = 3x^2$. -/
example (x : ℝ) : deriv (fun x : ℝ => x^3) x = 3 * x^2 := by
  simp

/-! ## Integral -/

/-- $\int_0^1 x^2\,dx = \frac{1}{3}$. -/
example : ∫ x in (0 : ℝ)..1, x^2 = 1 / 3 := by
  simp [integral_pow]
  norm_num
