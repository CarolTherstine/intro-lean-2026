/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Physlib.Units.WithDim.Basic
import Physlib.ClassicalMechanics.FreeParticle.Basic

namespace Hello.Physics

/-! ## Mechanics -/

open Dimension

/-!
Kinetic energy, `E_k = 1/2 * m * v ^ 2`.

In Physlib a dimensionful number is `WithDim d ℝ`, where `d` is its
dimension.  Multiplying two such values multiplies their dimensions, so the
type of the result is checked by Lean.
-/

/--
Kinetic energy of a mass `m` moving with speed `v`.
Its dimension is `M * (L / T) * (L / T)`.
-/
noncomputable def kineticEnergy
    (m : WithDim M𝓭 ℝ) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (L𝓭 * T𝓭⁻¹) * (L𝓭 * T𝓭⁻¹)) ℝ :=
  (1 / 2 : ℝ) • (m * v * v)

/-- The numerical value of the kinetic energy is `1/2 * m * v^2`. -/
theorem kineticEnergy_val (m : WithDim M𝓭 ℝ) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ) :
    (kineticEnergy m v).val = 1 / 2 * m.val * v.val^2 := by
  simp only [kineticEnergy, WithDim.real_smul_val,
    WithDim.withDim_hMul_val, smul_eq_mul]
  ring

/-! ## Newton's first law -/

open ClassicalMechanics

/--
A free particle obeying Newton's second law (`m * q'' = 0`)
has the same momentum at every time as it had at time `0`.
-/
theorem FreeParticle.linearMomentum_eq_initial
    (s : FreeParticle) (q : Time → ℝ)
    (h : ∀ t, s.NewtonsSecondLaw q t) (hq : ContDiff ℝ 2 q) (t : Time) :
    s.linearMomentum q t = s.linearMomentum q 0 := by
  obtain ⟨p, hp⟩ := s.linearMomentum_conserved q h hq
  rw [hp t, hp 0]

end Hello.Physics
