import HardSphereMeasure

/-!
# Proved solution

The substantive proof development is in the `lean/` directory.  This module
exposes the same declaration as `Challenge.lean` and connects it to the
machine-checked flat-coordinate theorem.
-/

namespace PalomarHS

open HsVirial

theorem main_result
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolumeFlat (k := k) (d := d) T := by
  exact hardSphere_nbc_volume_identity_flat hk

theorem signed_coefficient_sign
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    hardSphereBk (k := k) (d := d) =
      (-1 : ℝ) ^ (k - 1) * |hardSphereBk (k := k) (d := d)| := by
  let _ : NeZero k := ⟨by omega⟩
  have hfacpos : 0 < (k.factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos k)
  have habs :
      |hardSphereBk (k := k) (d := d)| =
        (k.factorial : ℝ)⁻¹ *
          ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
    unfold hardSphereBk
    rw [abs_mul, abs_inv, abs_of_pos hfacpos,
      abs_integral_hardSphereOmega_eq_integral_abs]
  calc
    hardSphereBk (k := k) (d := d) =
        (k.factorial : ℝ)⁻¹ *
          ∫ r : HardSphereConfiguration k d, hardSphereOmega r := rfl
    _ = (k.factorial : ℝ)⁻¹ *
          ((-1 : ℝ) ^ (k - 1) *
            ∫ r : HardSphereConfiguration k d, |hardSphereOmega r|) := by
      rw [integral_hardSphereOmega_eq_sign_mul_abs]
    _ = (-1 : ℝ) ^ (k - 1) *
          ((k.factorial : ℝ)⁻¹ *
            ∫ r : HardSphereConfiguration k d, |hardSphereOmega r|) := by
      ring
    _ = (-1 : ℝ) ^ (k - 1) *
          |hardSphereBk (k := k) (d := d)| := by
      rw [habs]

end PalomarHS
