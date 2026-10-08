import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteSyntax

/-! # 有限代表列的源内转置矩阵

有限代表列本身属于源。两次取坐标包络给出所有函数值的共同源内界，
有界统一化遂收集逐点有限赋值，且逐项保持原代表的实际求值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.matrix_l {ω κ K X R D b G : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hb : M.mem b ω) (hD : M.mem D X)
    (fg : Fn0_d b X G) (reps : ∀ i f, Rd_entry_d i f G → Fn0_d D X f) :
    ∃ B E V, M.mem B X ∧ M.mem E X ∧ M.mem V X ∧ M.IsFunctionSpace I E b B ∧ Fn0_d D E V ∧
      ∀ v t i f x, Rd_entry_d v t V → Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
  obtain ⟨c, code⟩ := source.code
  have hG := sc_finite_function_l hZF source.omega source.transitive code source.theory source.omega_mem
    (fun _ h => h) hb fg
  obtain ⟨C, hC, functions⟩ := source.theory.algebra.envelope_l hG
  obtain ⟨U, hU, union⟩ := source.theory.algebra.union C hC
  obtain ⟨B, hB, values⟩ := source.theory.algebra.envelope_l hU
  have bounded v f x (hf : M.mem f C) (hvx : Rd_entry_d v x f) : M.mem x B := by
    obtain ⟨p, pair, hp⟩ := hvx
    exact (values v x ⟨p, pair, (union p).mpr ⟨f, hf, hp⟩⟩).2
  obtain ⟨E, hE, space⟩ := source.finite_space_l hZF hB hb
  have column v (hv : M.mem v D) : ∃ t, M.mem t E ∧
      ∀ i f x, Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
    let ρ : Env M 3 := ⟨Fin.cases G (Fin.cases C (fun _ => v)), fun _ => v⟩
    let φ : BinarySchema 3 := { body := Formula.existsMem (.bound 3) (.conj
      (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 5) (.bound 1) .newest)) }
    have sat i x : φ.denote ρ i x ↔ ∃ f, M.mem f C ∧ Rd_entry_d i f G ∧ Rd_entry_d v x f := by
      simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
    obtain ⟨t, _, ft, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
      (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
      ρ (Fin.cases hG (Fin.cases hC (fun _ => source.transitive D hD v hv)))
      (source.transitive ω source.omega_mem b hb) hB (fun i hi => by
        obtain ⟨f, _, hif⟩ := fg.2.1 i hi
        obtain ⟨x, _, hvx⟩ := (reps i f hif).2.1 v hv
        exact ⟨x, bounded v f x (functions i f hif).2 hvx,
          (sat i x).mpr ⟨f, (functions i f hif).2, hif, hvx⟩⟩)
    have read i f x (hif : Rd_entry_d i f G) (hix : Rd_entry_d i x t) : Rd_entry_d v x f := by
      obtain ⟨f', _, hif', hvx⟩ := (sat i x).mp (select i x hix)
      exact (fn0_function_l (ZF.modelsKP hZF) fg).1.2 i f' f hif' hif ▸ hvx
    refine ⟨t, (space t).mpr (fn0_function_l (ZF.modelsKP hZF) ft), fun i f x hif => ⟨read i f x hif, ?_⟩⟩
    intro hvx
    obtain ⟨y, _, hiy⟩ := ft.2.1 i (fg.bound_l hif).1
    exact (fn0_function_l (ZF.modelsKP hZF) (reps i f hif)).1.2 v y x (read i f y hif hiy) hvx ▸ hiy
  let ρ : Env M 4 := ⟨Fin.cases G (Fin.cases C (Fin.cases B (fun _ => b))), fun _ => b⟩
  let φ : BinarySchema 4 := { body := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 4)
    (Formula.forallMem (.bound 6) (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
      (.iff (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 4) .newest (.bound 1)))))) }
  have sat v t : φ.denote ρ v t ↔ ∀ i, M.mem i b → ∀ f, M.mem f C → ∀ x, M.mem x B →
      Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨V, hV, fv, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    ρ (Fin.cases hG (Fin.cases hC (Fin.cases hB (fun _ => source.transitive ω source.omega_mem b hb))))
    hD hE (fun v hv => by
      obtain ⟨t, ht, point⟩ := column v hv
      exact ⟨t, ht, (sat v t).mpr fun i _ f _ x _ hif => point i f x hif⟩)
  refine ⟨B, E, V, hB, hE, hV, space, fv, fun v t i f x hvt hif => ?_⟩
  have point := (sat v t).mp (select v t hvt) i (fg.bound_l hif).1 f (functions i f hif).2 x
  have ft := fn0_of_function_l (ZF.modelsKP hZF) ((space t).mp (fv.bound_l hvt).2)
  exact ⟨fun hix => (point (ft.bound_l hix).2 hif).mp hix,
    fun hvx => (point (bounded v f x (functions i f hif).2 hvx) hif).mpr hvx⟩

end YesMetaZFC.SetTheory.LargeCardinal
