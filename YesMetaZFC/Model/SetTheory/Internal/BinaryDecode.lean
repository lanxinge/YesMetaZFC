import YesMetaZFC.SetTheory.Descriptive.Coding.RelationCode
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 弱传递见证中的二值解码

逐行合法性与实际解码图都由 Δ₀ 绝对性读取。传递载体包含全部背景实数时，
KP 的解码构造自动给出有限闭包句子；载体自身不必满足任何集合论。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} {Q : M.Domain} (ht : M.TransitiveSet Q)
  (hn : Nonempty {x // M.mem x Q}) (hE : Extensional M)
include ht hE

theorem rt_bc_valid_l (ω X E b : (rt_model_l Q hn).Domain) :
    Bc_valid_d ω X E b ↔ Bc_valid_d ω.val X.val E.val b.val := by
  let ρ : Env (rt_model_l Q hn) 4 := ⟨Fin.cases ω (Fin.cases X (Fin.cases E (fun _ => b))),fun _ => ω⟩
  exact (bc_valid_sat_l (rt_model_ext_l hE ht hn) ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).symm.trans
    ((rt_model_delta_l ht hn (bc_valid_delta_l ..) ρ).trans (bc_valid_sat_l hE _ _ _ _ _))

theorem rt_bc_graph_l (ω X E b r : (rt_model_l Q hn).Domain) :
    Bc_graph_d ω X E b r ↔ Bc_graph_d ω.val X.val E.val b.val r.val := by
  let ρ : Env (rt_model_l Q hn) 5 := ⟨Fin.cases ω (Fin.cases X (Fin.cases E (Fin.cases b (fun _ => r)))),fun _ => ω⟩
  exact (bc_graph_sat_l (rt_model_ext_l hE ht hn) ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    ((rt_model_delta_l ht hn (bc_graph_delta_l ..) ρ).trans (bc_graph_sat_l hE _ _ _ _ _ _))

omit hE in
theorem rt_bc_closed_l (hKP : M.Models KP) (ω X E : (rt_model_l Q hn).Domain)
    (cover : ∀ r, Fn0_d ω.val ω.val r → M.mem r Q) : Bc_closed_d ω X E := by
  intro b _ valid
  obtain ⟨r,graph⟩ := bc_decode_l hKP ((rt_bc_valid_l ht hn hKP.1 ω X E b).mp valid)
  let t : (rt_model_l Q hn).Domain := ⟨r,cover r graph.1⟩
  exact ⟨t,(rt_bc_graph_l ht hn hKP.1 ω X E b t).mpr graph⟩

end YesMetaZFC.SetTheory.Internal
