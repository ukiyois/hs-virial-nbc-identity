import Mathlib

/-!
# Advertised statement

This file is the deliberately small statement surface for the hard-sphere NBC
volume identity.  The definitions below are copied from the substantive proof
development so that the statement is independently readable; no proof theorem
from that development is imported here.
-/

namespace HsVirial

open Set
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def graphEdgeFinset (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ G.edgeSet)

def cycleEdgeFinset {G : SimpleGraph V} {v : V} (c : G.Walk v v) : Finset (Sym2 V) :=
  c.edges.toFinset

def IsGraphCycle (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ C = cycleEdgeFinset c

variable [LinearOrder (Sym2 V)]

def graphEdgeLE (a b : Sym2 V) : Prop :=
  @LE.le (Sym2 V)
    ((inferInstance : LinearOrder (Sym2 V)).toPartialOrder.toPreorder.toLE) a b

def IsGraphForest (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  (A : Set (Sym2 V)) ⊆ G.edgeSet ∧
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).IsAcyclic

def IsGraphCircuit (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  C ⊆ graphEdgeFinset G ∧
    ¬IsGraphForest G C ∧
      ∀ e ∈ C, IsGraphForest G (C.erase e)

def connectedEdgeSubsets (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  (graphEdgeFinset G).powerset.filter
    (fun A => (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected)

def activeEdge (x : Sym2 V → Bool) (e : Sym2 V) : Prop :=
  e ∈ graphEdgeFinset (completeGraph V) ∧ x e = true

noncomputable def activeEdgeFinset (x : Sym2 V → Bool) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (activeEdge x)

def overlapGraph (x : Sym2 V → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (activeEdgeFinset x : Set (Sym2 V))

def matroidParitySign : Nat -> Int
  | 0 => 1
  | n + 1 => -matroidParitySign n

noncomputable def bond (x : Sym2 V → Bool) (e : Sym2 V) : Int := by
  classical
  exact if activeEdge x e then -1 else 0

def completeConnectedEdgeSubsets : Finset (Finset (Sym2 V)) :=
  connectedEdgeSubsets (completeGraph V)

def mayerKernel (x : Sym2 V → Bool) : Int :=
  ∑ A ∈ completeConnectedEdgeSubsets,
    ∏ e ∈ A, bond x e

def IsGraphNBCandidate (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ (C : Finset (Sym2 V)),
    IsGraphCycle G C ∧
    e ∈ C ∧
    (∀ f ∈ C, graphEdgeLE f e) ∧
    ((C.erase e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ (A : Set (Sym2 V))

def IsGraphSpanning (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Reachable = G.Reachable

def IsGraphCircuitNBCandidate (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ C : Finset (Sym2 V),
    IsGraphCircuit G C ∧ e ∈ C ∧ (∀ f ∈ C, graphEdgeLE f e) ∧
      ((C.erase e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ (A : Set (Sym2 V))

def IsGraphCircuitNBCBad (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  ∃ e, IsGraphCircuitNBCandidate G A e

def IsExplicitNBCTree (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  IsGraphForest G A ∧
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected ∧
    ¬IsGraphCircuitNBCBad G A

noncomputable def treeUniverse : Finset (Finset (Sym2 V)) := by
  classical
  exact (graphEdgeFinset (completeGraph V)).powerset.filter
    (fun T : Finset (Sym2 V) =>
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree)

def nbcRegion {X : Type*} (active : X → Sym2 V → Bool)
    (T : Finset (Sym2 V)) : Set X :=
  {x | IsExplicitNBCTree (overlapGraph (active x)) T}

abbrev HSPosition (d : Nat) := EuclideanSpace ℝ (Fin d)

def hardSphereEdgeKey {k : Nat} (e : Sym2 (Fin k)) : Fin k ×ₗ Fin k :=
  toLex (e.inf, e.sup)

@[instance_reducible]
noncomputable def hardSphereEdgeLinearOrder (k : Nat) :
    LinearOrder (Sym2 (Fin k)) :=
  LinearOrder.lift' (hardSphereEdgeKey (k := k)) (by
    intro e f h
    apply Sym2.inf_eq_inf_and_sup_eq_sup.mp
    constructor
    · simpa [hardSphereEdgeKey] using
        congrArg (fun p : Fin k ×ₗ Fin k => (ofLex p).1) h
    · simpa [hardSphereEdgeKey] using
        congrArg (fun p : Fin k ×ₗ Fin k => (ofLex p).2) h)

noncomputable instance hardSphereEdgeOrder (k : Nat) :
    LinearOrder (Sym2 (Fin k)) := hardSphereEdgeLinearOrder k

abbrev HardSphereConfiguration (k d : Nat) :=
  Fin (k - 1) → HSPosition d

def hardSphereFreeIndex {k : Nat} [NeZero k]
    (i : Fin k) (hi : i ≠ 0) : Fin (k - 1) :=
  ⟨i.val - 1, by omega⟩

def hardSpherePosition {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) (i : Fin k) : HSPosition d :=
  if hi : i = 0 then 0 else r (hardSphereFreeIndex i hi)

def hardSphereActiveExact {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) : Sym2 (Fin k) → Bool :=
  Sym2.lift ⟨fun i j =>
    decide (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)), by
      intro i j
      change decide (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)) =
        decide (‖hardSpherePosition r j - hardSpherePosition r i‖ < (1 : ℝ))
      rw [norm_sub_rev]⟩

def hardSphereOmega {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) : ℝ :=
  (mayerKernel (hardSphereActiveExact r) : ℝ)

def hardSphereBk {k d : Nat} [NeZero k] : ℝ :=
  (k.factorial : ℝ)⁻¹ *
    ∫ r : HardSphereConfiguration k d, hardSphereOmega r

def hardSphereNBCVolume {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) : ℝ :=
  (volume : Measure (HardSphereConfiguration k d)).real
    (nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := d)) T)

def hardSphereIndexEquiv (k d : Nat) :
    Fin (k - 1) × Fin d ≃ Fin ((k - 1) * d) :=
  finProdFinEquiv

def hardSphereFlattenEquiv (k d : Nat) :
    HardSphereConfiguration k d ≃ᵐ
      EuclideanSpace ℝ (Fin ((k - 1) * d)) :=
  let e₁ := MeasurableEquiv.piCongrRight
    (fun _ : Fin (k - 1) =>
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
  let e₂ := (MeasurableEquiv.curry (Fin (k - 1)) (Fin d) ℝ).symm
  let e₃ := MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((k - 1) * d) => ℝ) (hardSphereIndexEquiv k d)
  let e₄ := MeasurableEquiv.toLp 2 (Fin ((k - 1) * d) → ℝ)
  e₁.trans (e₂.trans (e₃.trans e₄))

def hardSphereNBCVolumeFlat
    {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin ((k - 1) * d)))).real
    (hardSphereFlattenEquiv k d ''
      nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := d)) T)

end

end HsVirial

namespace PalomarHS

open HsVirial

/- The proof is supplied independently in `Solution.lean`. -/
theorem main_result
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolumeFlat (k := k) (d := d) T := by
  sorry

end PalomarHS
