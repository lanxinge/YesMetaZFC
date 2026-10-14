import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingCountable
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecord

/-! # 恢复图及原节点沿实际初等图搬运

函数性和精确定义域使用传递源中的绝对性；完整节点公式同时搬运三张
坐标图。原记录按配对逐项回拉，保持同一条目而不重新选取回答。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c d X R Y S j : M.Domain} (hw : M.IsOmega ω)
  (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
  (mx : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
  (my : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
  (h : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
include hZF hw xt yt mx my h

theorem Smap_d.tg_graph_l {n n' g g' : M.Domain}
    (hn : Rd_entry_d n n' j) (hg : Rd_entry_d g g' j) :
    Tg_graph_d I n g ↔ Tg_graph_d I n' g' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨n, h.1.1.input_mem_of_pairMember hn⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨n', h.1.1.output_mem_of_pairMember hn⟩⟩
  let v : Fin 2 → M.Domain := Fin.cases n (fun _ => g)
  let w : Fin 2 → M.Domain := Fin.cases n' (fun _ => g')
  have images : ∀ i, Rd_entry_d (v i) (w i) j := Fin.cases hn (Fin.cases hg (fun i => Fin.elim0 i))
  let ρ : Env (rt_model_l X nx) 2 := ⟨fun i => ⟨v i, h.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨n, h.1.1.input_mem_of_pairMember hn⟩⟩
  let η : Env (rt_model_l Y ny) 2 := ⟨fun i => ⟨w i, h.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨n', h.1.1.output_mem_of_pairMember hn⟩⟩
  obtain ⟨e, empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hw ⟨c, R, d, S, mx.empty_pred_l I empty, my.empty_pred_l I empty, h⟩ nx ny
    (tg_graph_m (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ η images
  exact (tg_graph_source_l xt nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ρ (.bound 0) (.bound 1)).symm.trans
    (tr.trans (tg_graph_source_l yt ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) η (.bound 0) (.bound 1)))

theorem Smap_d.tg_node_l {v w : Fin 5 → M.Domain} (images : ∀ i, Rd_entry_d (v i) (w i) j) :
    Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) ↔ Tg_node_d I (w 0) (w 1) (w 2) (w 3) (w 4) := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  let ρ : Env (rt_model_l X nx) 5 := ⟨fun i => ⟨v i, h.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let η : Env (rt_model_l Y ny) 5 := ⟨fun i => ⟨w i, h.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  obtain ⟨e, empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hw ⟨c, R, d, S, mx.empty_pred_l I empty, my.empty_pred_l I empty, h⟩ nx ny
    (tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) (by simp -implicitDefEqProofs) ρ η images
  exact (tg_node_source_l xt nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    (tr.trans (tg_node_source_l yt ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)))

theorem Smap_d.tuple_preimage_l {k} {p q : M.Domain} {v : Fin (k+1) → M.Domain}
    (hp : Rd_entry_d p q j) (code : Rt_tuple_d v q) :
    ∃ w : Fin (k+1) → M.Domain, Rt_tuple_d w p ∧ ∀ i, Rd_entry_d (w i) (v i) j := by
  induction k generalizing p q with
  | zero =>
    exact ⟨fun _ => p, rfl, Fin.cases (code ▸ hp) (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    obtain ⟨r, pair, tail⟩ := code
    obtain ⟨a, b, _, _, ab, ha, hb⟩ := h.kpair_preimage_l hZF hw xt yt mx my hp pair
    obtain ⟨w, cw, images⟩ := ih hb tail
    refine ⟨Fin.cases (motive := fun _ => M.Domain) a w, ?_, ?_⟩
    · exact ⟨b, ab, cw⟩
    · exact Fin.cases ha images


end YesMetaZFC.SetTheory.Internal
