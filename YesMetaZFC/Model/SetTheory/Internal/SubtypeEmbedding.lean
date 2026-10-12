import YesMetaZFC.Model.SetTheory.Internal.SubtypeClosure
import YesMetaZFC.Model.SetTheory.Internal.TypeMinusEmbedding

/-! # 子类型闭包沿实际初等映射运输

先在实际源中构造整张限制代码矩阵；自然数及矩阵均被映射固定。
有界公式因而覆盖像查询域中的所有新名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.subtype_up_l {ω θ X R c Y S d j b v z N E D u N' E' D' u' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hb : M.mem b ω) (hv : M.mem v ω) (hz : M.mem z ω)
    (hN : Rd_entry_d N N' j) (hE : Rd_entry_d E E' j) (hD : Rd_entry_d D D' j) (hu : Rd_entry_d u u' j) :
    Ts_up_d I ω b v z N E D u ↔ Ts_up_d I ω b v z N' E' D' u' := by
  obtain ⟨B, table⟩ := tm_table_exists_l I hZF hω
  have trans := ZF.v_transitive_l I hZF hX
  have fixed := hj.natural_l hZF hω trans hY hm hn hωX
  have hωj := hj.omega_l I hZF hω trans hY hm hn hωX
  have hBj := hj.type_table_l hZF hω hX hθ hωX hY hm hn table
  let φ : Formula 1 9 := ts_up0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest
  let ρ : Env M 9 := ⟨Fin.cases u (Fin.cases D (Fin.cases E (Fin.cases N (Fin.cases B
    (Fin.cases z (Fin.cases v (Fin.cases b (fun _ => ω)))))))), fun _ => ω⟩
  let η : Env M 9 := ⟨Fin.cases u' (Fin.cases D' (Fin.cases E' (Fin.cases N' (Fin.cases B
    (Fin.cases z (Fin.cases v (Fin.cases b (fun _ => ω)))))))), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω trans hY hm hn hj φ
    (ts_up0_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl) (ts_up0_delta_l ..) ρ η
    (Fin.cases hu (Fin.cases hD (Fin.cases hE (Fin.cases hN (Fin.cases hBj
      (Fin.cases (fixed z hz) (Fin.cases (fixed v hv) (Fin.cases (fixed b hb) (fun _ => hωj)))))))))
  exact ((ts_up0_sat_l (ZF.modelsKP hZF) ρ (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest table).symm.trans tr).trans
    (ts_up0_sat_l (ZF.modelsKP hZF) η (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest table)

end YesMetaZFC.SetTheory.Internal
