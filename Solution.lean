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

end PalomarHS
