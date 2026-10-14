import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnSequence
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordCoordinate
import YesMetaZFC.Model.SetTheory.Internal.TypeGameGraphUnion

/-! # 奇数返回三张坐标图的实际相容取并

从唯一的返回节点列投影长度和每张坐标图。相邻的一点扩张沿内部 ω 传播，
自动产生定义域恰为 ω 的并图，所有原有限坐标图都是它的精确限制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_return_union_d (ω N F : M.Domain) (a : Fin 3) (g : M.Domain) : Prop := Fn0_d ω N g ∧
  (∀ p, M.mem p g ↔ ∃ i r, ∃ v : Fin 5 → M.Domain, Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ M.mem p (v ([2,3,4].get a))) ∧
  ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → M.IsRestrictionOf I (v ([2,3,4].get a)) g (v 0)

theorem Tg_return_sequence_d.union_l {ω H π P N b D J F : M.Domain}
    (h : Tg_return_sequence_d hZF ω H π P N b D J F) (a : Fin 3) : ∃ g, Tg_return_union_d hZF ω N F a g := by
  obtain ⟨L, lf, ls⟩ := rt_coordinate_l hZF (0 : Fin 5) h.function h.codes
    (fun i r v hr code => (h.rows i r v hr code).choose_spec.choose_spec.2.2.1)
  obtain ⟨G, gf, gs⟩ := rt_coordinate_l hZF ([2,3,4].get a : Fin 5) h.function h.codes
    (fun i r v hr code => (h.rows i r v hr code).choose_spec.choose_spec.2.2.2.1 ([2,3,4].get a))
  have lv {i r} {v : Fin 5 → M.Domain} (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : Rd_entry_d i (v 0) L :=
    (ls i (v 0)).mpr ⟨r, hr, v, code, rfl⟩
  have gv {i r} {v : Fin 5 → M.Domain} (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : Rd_entry_d i (v ([2,3,4].get a)) G :=
    (gs i (v ([2,3,4].get a))).mpr ⟨r, hr, v, code, rfl⟩
  have data i (hi : M.mem i ω) : ∃ r, ∃ v : Fin 5 → M.Domain, Rd_entry_d i r F ∧ Rt_tuple_d v r := by
    obtain ⟨r, _, hr⟩ := h.function.2.1 i hi
    obtain ⟨v, code⟩ := h.codes i r hr
    exact ⟨r, v, hr, code⟩
  have finite i n g (hn : Rd_entry_d i n L) (hg : Rd_entry_d i g G) : Tg_graph_d I n g := by
    obtain ⟨r, v, hr, code⟩ := data i (lf.bound_l hn).1
    have en := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 i (v 0) n (lv hr code) hn
    have eg := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 i (v ([2,3,4].get a)) g (gv hr code) hg
    obtain ⟨_, _, _, _, _, _, node⟩ := h.rows i r v hr code
    exact en ▸ eg ▸ (Fin.cases node.1 (Fin.cases node.2.1 (Fin.cases node.2.2.1 (fun i => Fin.elim0 i))) a)
  have step i j n m (succ : M.SuccessorOf j i) (hn : Rd_entry_d i n L) (hm : Rd_entry_d j m L) : M.SuccessorOf m n := by
    obtain ⟨r, v, hr, code⟩ := data i (lf.bound_l hn).1
    obtain ⟨s, w, hs, pack⟩ := data j (lf.bound_l hm).1
    have en := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 i (v 0) n (lv hr code) hn
    have em := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 j (w 0) m (lv hs pack) hm
    exact en ▸ em ▸ (h.steps i j r s v w succ hr hs code pack).1
  have grow i j g k (succ : M.SuccessorOf j i) (hg : Rd_entry_d i g G) (hk : Rd_entry_d j k G) : M.MemberSubset g k := by
    obtain ⟨r, v, hr, code⟩ := data i (gf.bound_l hg).1
    obtain ⟨s, w, hs, pack⟩ := data j (gf.bound_l hk).1
    have eg := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 i (v ([2,3,4].get a)) g (gv hr code) hg
    have ek := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 j (w ([2,3,4].get a)) k (gv hs pack) hk
    exact eg ▸ ek ▸ (h.steps i j r s v w succ hr hs code pack).2 a
  obtain ⟨g, fn, union, cuts⟩ := tg_graph_union_l hZF h.omega h.transitive lf gf finite step grow
  refine ⟨g, fn, fun p => (union p).trans ⟨?_, ?_⟩, fun i r v hr code => cuts i (v 0) (v ([2,3,4].get a)) (lv hr code) (gv hr code)⟩
  · rintro ⟨i, g, hg, hp⟩
    obtain ⟨r, hr, v, code, eq⟩ := (gs i g).mp hg
    exact ⟨i, r, v, hr, code, eq.symm ▸ hp⟩
  · rintro ⟨i, r, v, hr, code, hp⟩
    exact ⟨i, v ([2,3,4].get a), gv hr code, hp⟩

end YesMetaZFC.SetTheory.LargeCardinal
