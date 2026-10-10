import YesMetaZFC.Model.SetTheory.Internal.TypeMinusMatrix
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed

/-! # 前驱类型与实际初等像交换

限制代码的整张自然数矩阵属于源秩层，并由初等映射逐点固定。
有界逆像公式因此搬运全部目标查询，包括不在旧查询逐点像中的参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 只要求源为包含 ω 的极限秩层；不增加不可达性、选择或目标模型性前提。 -/
theorem Smap_d.type_minus_l {ω θ X R c Y S d j D t u D' t' u' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j) (hu : Rd_entry_d u u' j) :
    Tm_minus_d I ω D t u ↔ Tm_minus_d I ω D' t' u' := by
  obtain ⟨B, table⟩ := tm_table_exists_l I hZF hω
  have trans := ZF.v_transitive_l I hZF hX
  have hBX : M.mem B X := ZF.v_relation_mem_l I hZF hX hθ hωX (fun p hp => by
    obtain ⟨z, w, code⟩ := table.1.1 p hp
    have zw := table.1.2 z w ⟨p, code, hp⟩
    exact ⟨z, zw.1, w, zw.2, code⟩)
  have hωj := hj.omega_l I hZF hω trans hY hm hn hωX
  have hBj := hj.fixed_relation_l hZF hω trans hY hm hn hωj
    (hj.natural_l hZF hω trans hY hm hn hωX) hBX table.1
  let φ : Formula 1 5 := tm_cut0_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  let ρ : Env M 5 := ⟨Fin.cases u (Fin.cases t (Fin.cases D (Fin.cases B (fun _ => ω)))), fun _ => ω⟩
  let η : Env M 5 := ⟨Fin.cases u' (Fin.cases t' (Fin.cases D' (Fin.cases B (fun _ => ω)))), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω trans hY hm hn hj φ
    (tm_cut0_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) (tm_cut0_delta_l ..) ρ η
    (Fin.cases hu (Fin.cases ht (Fin.cases hD (Fin.cases hBj (fun _ => hωj)))))
  exact ((tm_cut0_sat_l (ZF.modelsKP hZF) ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest table).symm.trans tr).trans
    (tm_cut0_sat_l (ZF.modelsKP hZF) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest table)

end YesMetaZFC.SetTheory.Internal
