import YesMetaZFC.Model.SetTheory.Internal.TypeEmbedding
import YesMetaZFC.Model.SetTheory.Internal.TypePoolBounded
import YesMetaZFC.Model.SetTheory.Internal.SourceSequences

/-! # 实际初等像中的完整类型查询域

名字域用有界原式运输；目标的内部有限函数闭性恢复全部新列。
结论识别完整查询域，不限于旧查询的逐点像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.type_full_l {ω θ X R Y S c d j n U U' D D' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (theory : Sc_theory_d I ω Y S) (hnω : M.mem n ω)
    (hUX : M.mem U X) (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j)
    (pool : Tt_pool_d I ω n U D) :
    ∃ N E N' E', Tn_names_d n U N ∧ Fseq_space_d I ω N E ∧ M.IsCartesianProduct I D ω E ∧
      Rd_entry_d N N' j ∧ Rd_entry_d E E' j ∧ Tn_names_d n U' N' ∧ Fseq_space_d I ω N' E' ∧ M.IsCartesianProduct I D' ω E' := by
  have trans := ZF.v_transitive_l I hZF hX
  have fixed := hj.natural_l hZF hω trans hY hm hn hωX
  have hw := hj.omega_l I hZF hω trans hY hm hn hωX
  obtain ⟨N, E, N', E', names, seq, prod, hN, hE, _⟩ :=
    hj.type_frame_l hZF hω hX hθ hωX hY hm hn hnω (fixed n hnω) hUX hU hD pool
  have names' := smap_delta_l I hZF hω trans hY hm hn hj (n := 3)
    (tn_names0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (tn_names0_delta_l ..)
    ⟨Fin.cases N (Fin.cases U (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases N' (Fin.cases U' (fun _ => n)), fun _ => n⟩ (Fin.cases hN (Fin.cases hU (fun _ => fixed n hnω)))
  simp only [tn_names0_sat_l (ZF.modelsKP hZF)] at names'
  have prod' := smap_delta_l I hZF hω trans hY hm hn hj (n := 3)
    (rd_graph_m .prod (.bound 2) (.bound 1) (.bound 2) .newest)
    (by simp -implicitDefEqProofs) (rd_graph_delta_l ..)
    ⟨Fin.cases D (Fin.cases E (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases D' (Fin.cases E' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hD (Fin.cases hE (fun _ => hw)))
  simp only [rd_graph_sat_l (ZF.modelsKP hZF)] at prod'
  have product : M.IsCartesianProduct I D' ω E' := fun p => (prod'.mp (fun p => (prod p).trans
    ⟨fun ⟨a, ha, b, hb, cp⟩ => ⟨a, b, ha, hb, cp⟩, fun ⟨a, b, ha, hb, cp⟩ => ⟨a, ha, b, hb, cp⟩⟩) p).trans
    ⟨fun ⟨a, b, ha, hb, cp⟩ => ⟨a, ha, b, hb, cp⟩, fun ⟨a, ha, b, hb, cp⟩ => ⟨a, b, ha, hb, cp⟩⟩
  exact ⟨N, E, N', E', names, seq, prod, hN, hE, names'.mp names,
    hj.sequences_l hZF hω trans hY hm hn theory hωX hN hE seq, product⟩

end YesMetaZFC.SetTheory.Internal
