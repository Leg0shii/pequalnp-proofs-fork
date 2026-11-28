import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18182

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]


open PEqualNP.Represents

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1,t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [
  (true, 0, 9),
  (true, 1, 10),
  (true, 2, 11),
  (true, 3, 12),
  (true, 4, 13),
  (true, 5, 14),
  (true, 6, 15),
  (true, 7, 16),
  (true, 8, 17),
  (true, 18, 19),
  (true, 27, 20),
  (true, 21, 22),
  (true, 29, 23),
  (true, 24, 25),
  (true, 31, 26),
  (true, 18, 21),
  (true, 33, 24),
  (true, 19, 22),
  (true, 35, 25),
  (true, 20, 23),
  (true, 37, 26),
  (false, 28, 30),
  (true, 28, 30),
  (false, 40, 32),
  (true, 39, 41),
  (false, 34, 36),
  (true, 34, 36),
  (false, 44, 38),
  (true, 43, 45),
  (true, 42, 46)]
def circuit : Circuit := ⟨codes.map asGate, 47⟩
def raw : List (BitVec 81) := [
  0x1ff,
  0x3fe00,
  0x7fc0000,
  0xff8000000,
  0x1ff000000000,
  0x3fe00000000000,
  0x7fc0000000000000,
  0xff8000000000000000,
  0x1ff000000000000000000,
  0x1008040201008040201,
  0x2010080402010080402,
  0x4020100804020100804,
  0x8040201008040201008,
  0x10080402010080402010,
  0x20100804020100804020,
  0x40201008040201008040,
  0x80402010080402010080,
  0x100804020100804020100]
def table : BitVec 81 := 0xffbfeffbfeffbfeffbfe

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

theorem fan : FanInTwo circuit := by
  intro g hg
  obtain ⟨ho,hl⟩ := mono g hg
  refine ⟨?_,hl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
  tauto

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem raw_spec : ∀ u v : Fin 9,
    (raw.map fun w => w.getLsbD (9 * u.val + v.val)) = oneEach u v := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem calculated : (circuit.gates.foldl hcsStep raw).getD circuit.output 0 = table := by
  decide +kernel

theorem rep_table (u v : Fin 9) : circuit.eval (oneEach u v) = table.getLsbD (9 * u.val + v.val) := by
  have hr : 9 * u.val + v.val < 81 := by have := u.isLt; have := v.isLt; omega
  have hbits := hcsFoldBits raw ⟨_, hr⟩ circuit.gates fan
  change (circuit.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (oneEach u v)).getD circuit.output false = _
  rw [← raw_spec u v, ← hbits, ← hcsGetDBit, calculated]

end PEqualNP.Outside.L_meta_18182

open PEqualNP.Outside.L_meta_18182 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_18182 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 9 => decide (u ≠ v)) 30 := by
  refine ⟨circuit, mono, by decide, ?_⟩
  intro u v
  rw [rep_table u v]
  revert u v
  decide +kernel
