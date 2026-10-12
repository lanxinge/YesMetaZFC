import YesMetaZFC.Model.SetTheory.Internal.TypeDropSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite

/-! # 原 dcp 与实际初等像交换

运输的是原查询重编码与逆像等式；两侧都按同一 dcp 定义读取。
所需源闭包仅为传递与配对，没有把像类型的投影作为额外不变量假定。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.type_dcp_l {ω c d X R Y S j n m D t v n' m' D' t' v' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (px : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (py : ∀ a b, M.mem a Y → M.mem b Y → ∃ p, M.mem p Y ∧ Pair_d M p a b)
    (hh : Rd_entry_d n n' j) (hk : Rd_entry_d m m' j) (hD : Rd_entry_d D D' j)
    (ht : Rd_entry_d t t' j) (hv : Rd_entry_d v v' j) :
    Td_dcp_d I n m D t v ↔ Td_dcp_d I n' m' D' t' v' := by
  have inside {x y} (h : Rd_entry_d x y j) := hj.1.1.input_mem_of_pairMember h
  have outside {x y} (h : Rd_entry_d x y j) := hj.1.1.output_mem_of_pairMember h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨v, inside hv⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨v', outside hv⟩⟩
  let ρ : Env (rt_model_l X nx) 5 := ⟨Fin.cases ⟨v, inside hv⟩ (Fin.cases ⟨t, inside ht⟩
    (Fin.cases ⟨D, inside hD⟩ (Fin.cases ⟨m, inside hk⟩ (fun _ => ⟨n, inside hh⟩)))), fun _ => ⟨v, inside hv⟩⟩
  let η : Env (rt_model_l Y ny) 5 := ⟨Fin.cases ⟨v', outside hv⟩ (Fin.cases ⟨t', outside ht⟩
    (Fin.cases ⟨D', outside hD⟩ (Fin.cases ⟨m', outside hk⟩ (fun _ => ⟨n', outside hh⟩)))), fun _ => ⟨v', outside hv⟩⟩
  let φ : Formula 1 5 := td_dcp_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny φ
    (by simp -implicitDefEqProofs [φ]) ρ η (Fin.cases hv (Fin.cases ht (Fin.cases hD (Fin.cases hk (fun _ => hh)))))
  exact (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nx px ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    (tr.trans (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hY ny py η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))

end YesMetaZFC.SetTheory.Internal
