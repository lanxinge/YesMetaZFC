import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTrace
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTransport

/-! # 实际支撑迹沿所属源嵌入传输

测度关系、恒等代表与有界分离方程一同传输；完整有限列空间保证目标中
新出现的列也由同一方程判定，因此得到实际集合的像，而非仅逐点像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_trace_d.map_l {ω κ κ' L L' K K' X R Y S c d σ F F' m D D' E E' a a' f f' Z Z' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X) (hmω : M.mem m ω)
    (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hK : Rd_entry_d K K' σ)
    (hF : Rd_entry_d F F' σ) (hD : Rd_entry_d D D' σ) (hE : Rd_entry_d E E' σ)
    (ha : Rd_entry_d a a' σ) (hf : Rd_entry_d f f' σ) (hZ : Rd_entry_d Z Z' σ)
    (trace : Eb_trace_d ω κ L K X F m D E a f Z) : Eb_trace_d ω κ' L' K' Y F' m D' E' a' f' Z' := by
  obtain ⟨B, J, U, V, ι, T, hBX, hJX, hUX, hVX, hιX, hTX, kb, indices, range, rel, fb, fi, ids, seq, sub, spec⟩ := trace
  obtain ⟨B', hBY, hB⟩ := hσ.1.1.2.2 B hBX
  obtain ⟨J', hJY, hJ⟩ := hσ.1.1.2.2 J hJX
  obtain ⟨U', hUY, hU⟩ := hσ.1.1.2.2 U hUX
  obtain ⟨V', hVY, hV⟩ := hσ.1.1.2.2 V hVX
  obtain ⟨ι', hιY, hι⟩ := hσ.1.1.2.2 ι hιX
  obtain ⟨T', hTY, hT⟩ := hσ.1.1.2.2 T hTX
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  have mσ := hσ.natural_l hZF hω hX hY hm hn hωX m hmω
  have indices' := ep_indices_map_l hZF hω hX hY hm hn hσ theory hωX hL hJ indices
  have seq₀ : Fseq_space_d I ω L T := fun t => (seq t).trans (exists_congr fun n => and_congr_right fun _ =>
    ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  have seq' := hσ.sequences_l hZF hω hX hY hm hn theory hωX hL hT seq₀
  let φ : Formula 1 17 := .conj (rd_graph_m .range (.bound 5) (.bound 5) (.bound 5) (.bound 7))
    (.conj (rd_graph_m .mem (.bound 10) (.bound 10) (.bound 10) (.bound 6))
      (.conj (fn0_m (.bound 15) (.bound 10) (.bound 2))
        (.conj (fn0_m (.bound 16) (.bound 16) (.bound 4))
          (.conj (Formula.forallMem (.bound 16) (rd_entry0_m .newest .newest (.bound 5)))
            (.conj (Formula.subset .newest (.bound 1)) (Formula.forallMem (.bound 1)
              (.iff (.mem .newest (.bound 1)) (.conj (fn0_m (.bound 15) (.bound 12) .newest)
                (eb_edge_m (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9)
                  (.bound 8) (.bound 7) (.bound 6) .newest (.bound 5) (.bound 4) (.bound 3))))))))))
  have delta : φ.IsDelta0 := .conj (rd_graph_delta_l ..) (.conj (rd_graph_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.conj (fn0_delta_l ..) (eb_edge_delta_l ..)))))))))
  have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) delta
    ⟨Fin.cases Z (Fin.cases T (Fin.cases f (Fin.cases a (Fin.cases ι (Fin.cases F (Fin.cases V
      (Fin.cases U (Fin.cases K (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (Fin.cases ω
        (Fin.cases m (Fin.cases D (fun _ => E)))))))))))))))), fun _ => E⟩
    ⟨Fin.cases Z' (Fin.cases T' (Fin.cases f' (Fin.cases a' (Fin.cases ι' (Fin.cases F' (Fin.cases V'
      (Fin.cases U' (Fin.cases K' (Fin.cases J' (Fin.cases B' (Fin.cases L' (Fin.cases κ' (Fin.cases ω
        (Fin.cases m (Fin.cases D' (fun _ => E')))))))))))))))), fun _ => E'⟩
    (Fin.cases hZ (Fin.cases hT (Fin.cases hf (Fin.cases ha (Fin.cases hι (Fin.cases hF (Fin.cases hV
      (Fin.cases hU (Fin.cases hK (Fin.cases hJ (Fin.cases hB (Fin.cases hL (Fin.cases hκ (Fin.cases ωσ
        (Fin.cases mσ (Fin.cases hD (fun _ => hE)))))))))))))))))
  simp only [φ, Formula.satisfies_conj_iff, rd_graph_sat_l (ZF.modelsKP hZF), fn0_sat_l hZF.1,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, eb_edge_sat_l hZF.1] at tr
  obtain ⟨range', rel', fb', fi', ids', sub', spec'⟩ := tr.mp ⟨range, rel, fb, fi, ids, sub, spec⟩
  exact ⟨B', J', U', V', ι', T', hBY, hJY, hUY, hVY, hιY, hTY,
    (hσ.subset_l hZF hω hX hY hm hn hK hB).mp kb, indices', range', rel', fb', fi', ids',
    (fun t => (seq' t).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)), sub', spec'⟩

end YesMetaZFC.SetTheory.LargeCardinal
