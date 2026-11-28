import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18354_aux

def circ : Circuit := ⟨[⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [14, 6]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [11, 21]⟩, ⟨.or, [11, 21]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [20, 23]⟩, ⟨.and, [18, 22]⟩, ⟨.or, [26, 28]⟩, ⟨.and, [27, 24]⟩, ⟨.and, [29, 30]⟩, ⟨.and, [25, 31]⟩, ⟨.or, [25, 31]⟩, ⟨.and, [32, 33]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [34, 36]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 39]⟩], 40⟩

end PEqualNP.Outside.L_meta_18354_aux

open PEqualNP.Outside.L_meta_18354_aux

theorem PEqualNP.Outside.L_meta_18354 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => decide (5 ≤ (List.ofFn x).count true)) 32 := by
  refine ⟨circ, ?_, by decide, ?_⟩
  · intro g hg
    simp [circ, List.mem_cons, List.not_mem_nil] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
