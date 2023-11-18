import Mathlib
set_option maxHeartbeats 0
open Quaternion Classical

--declare a Set Of Quaternions That Square To Negative 1
def soqtstn1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | -1 = q₀ * q₀}
def soqtstn1₁ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | ∃ (rx ry rz : ℝ), (q₀ = ⟨0, rx, ry, rz⟩ ∧ rx*rx + ry*ry + rz*rz = 1)}

lemma equalSets : soqtstn1₀ = soqtstn1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp [soqtstn1₀, soqtstn1₁]
  simp [Quaternion.ext_iff]
  constructor
  intros ha
  use x
  use y
  use z
  simp only [and_self, and_true]
  rcases ha with ⟨hSphere3,h0x,h0y,h0z⟩
  ring_nf at h0x
  ring_nf at h0y
  ring_nf at h0z
  simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0x
  simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0y
  simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0z
  have hr₀ : (¬ r = 0) → False := by
    intros hrn0
    let hrn0₂ := Iff.mpr iff_false_iff hrn0
    simp only [hrn0₂, false_or] at h0x
    simp only [hrn0₂, false_or] at h0y
    simp only [hrn0₂, false_or] at h0z
    simp_rw [h0x, h0y, h0z] at hSphere3
    simp only [mul_zero, sub_zero] at hSphere3
    have hrnn := mul_self_nonneg r
    rw [←hSphere3] at hrnn
    linarith
  have hr : r = 0 := by_contra hr₀
  constructor
  exact hr
  rw [hr] at hSphere3
  let hSphere4 := congrArg (λ (xk : ℝ) => -xk) hSphere3
  simp only [neg_neg, mul_zero, zero_sub, neg_sub] at hSphere4
  rw [hSphere4]
  ring_nf
  intros h₀
  ring_nf
  rcases h₀ with ⟨rx,ry,rz,hx⟩
  rcases hx with ⟨hx₀,hSphere⟩
  rcases hx₀ with ⟨hr,hrx,hry,hrz⟩
  simp_rw [hr]
  simp only [ne_eq, zero_pow', zero_sub, zero_mul, and_self, and_true]
  simp_rw [hrx,hry,hrz]
  let hSphere2 := congrArg (λ (xk : ℝ) => -xk) hSphere
  simp only [neg_add_rev] at hSphere2
  rw [←hSphere2]
  ring
