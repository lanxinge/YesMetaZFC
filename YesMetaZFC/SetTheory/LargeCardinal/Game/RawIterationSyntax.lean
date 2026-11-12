import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveSyntax
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationState
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax

/-! # 每条实际操作的原根临界点证书编码

量化同一操作列中的全部 payload，所属节点由原代码列定位，根图由原
映射列定位。完整相对根切片及其原生高度界同时进入对象语言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- X₀,R₀,γ₀,D₀,C₀,o,Q,G,E。
def tg_raw_critical_m {d} (p : Fin 9 → Term d) : Formula 1 d :=
  let e : Term d → Term (5+d) := fun t => t.rename (Fin.natAdd 5)
  let f : Term (5+d) → Term (8+(5+d)) := fun t => t.rename (Fin.natAdd 8)
  let v : Fin 5 → Term (5+d) := fun i => .bound (i.castAdd d)
  let u : Fin 8 → Term (8+(5+d)) := fun i => .bound (i.castAdd (5+d))
  rb_forall_m (n := 5) (.imp (.conj (rd_entry0_m (v 0) (v 1) (e (p 8)))
    (it_payload_m (v 1) (v 2) (v 3) (v 4)))
    (rb_exists_m (n := 8) (.conj (rd_entry0_m (f (v 0)) (u 0) (f (e (p 6))))
      (.conj (smdl_m (𝒞 := kpair_convention_l) (u 0) (u 1) (u 2))
      (.conj (it_map_m (f (e (p 7))) (f (e (p 5))) (f (v 0)) (u 4))
      (.conj (tg_root_slice_m (fun i => [f (e (p 0)),f (e (p 1)),f (e (p 2)),f (e (p 3)),f (e (p 4)),
        u 1,u 2,u 3,u 4,u 5,u 6,u 7].get i))
      (set[8+(5+d)] ⟪∀ x, ⌜rd_entry0_m⌝ₚ(x,⌜u 5⌝ₛ,⌜u 2⌝ₛ) →
        ⌜rd_entry0_m⌝ₚ(x,⌜f (v 2)⌝ₛ,⌜u 2⌝ₛ)⟫)))))))

@[simp] theorem tg_raw_critical_closed_l {d} (p : Fin 9 → Term d)
    (hp : ∀ i, (p i).freeSupport = []) : (tg_raw_critical_m p).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_critical_m,Definitional.Formula.FreeClosed,hp,Fin.forall_fin_succ]

theorem tg_raw_critical_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (p : Fin 9 → Term d) :
    Formula.satisfies ρ (tg_raw_critical_m p) ↔
      Tg_raw_critical_d I ((p 0).eval ρ) ((p 1).eval ρ) ((p 2).eval ρ) ((p 3).eval ρ)
        ((p 4).eval ρ) ((p 5).eval ρ) ((p 6).eval ρ) ((p 7).eval ρ) ((p 8).eval ρ) := by
  simp only [tg_raw_critical_m,rb_forall_sat_l,Formula.satisfies_imp_iff,Formula.satisfies_conj_iff,
    rb_exists_sat_l,rd_entry0_sat_l hE,it_payload_sat_l hE,smdl_sat_l I,it_map_sat_l hE,
    tg_root_slice_sat_l I hE,Formula.satisfies_forall_iff,Definitional.Term.eval_weaken,
    Definitional.Term.eval_rename,Env.reindex,Function.comp_def,
    Term.eval_bound,Fin.addCases_left,Fin.addCases_right,List.get]
  constructor
  · intro h i q κ L F entry payload
    obtain ⟨v,node,model,root,slice,lower⟩ := h (fun j => [i,q,κ,L,F].get j) ⟨entry,payload⟩
    exact ⟨v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,node,model,root,slice,lower⟩
  · intro h v hp
    obtain ⟨c,X,R,C,q,γ,V,t,node,model,root,slice,lower⟩ := h (v 0) (v 1) (v 2) (v 3) (v 4) hp.1 hp.2
    exact ⟨(fun i => [c,X,R,C,q,γ,V,t].get i),node,model,root,slice,lower⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原请求的完整一阶编码

二十四项参数依次给定固定原根、当前模型及五项原树框架；四十六项记录
保留原控制程序。根切片和档案中的选定共同图均作为实际对象量化。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- Ω,S₀,X₀,R₀,γ₀,D₀,C₀,A₀,X,R,w,η,C,χ,z,k,D,r,q,o,n,Q,G,Λ。
def tg_raw_request_m {d} (r : Fin 24 → Term d) (v : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ⌜tg_context_data_m⌝ₚ(⌜r 10⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 11⌝ₛ,⌜r 12⌝ₛ) ∧
  ⌜rf_record_m (𝒞 := kpair_convention_l) tg_issued0_m⌝ₚ(⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 12⌝ₛ,⌜r 17⌝ₛ) ∧
  ⌜rf_tuple_m (𝒞 := kpair_convention_l) (r 8) (r 9) v⌝ₚ(⌜r 17⌝ₛ) ∧
  ⌜v 0⌝ₛ = ⌜r 10⌝ₛ ∧ ⌜Formula.isOmega⌝ₚ(⌜r 0⌝ₛ) ∧
  ⌜rr_layer_m⌝ₚ(⌜r 0⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 10⌝ₛ,⌜r 14⌝ₛ) ∧ ⌜r 15⌝ₛ ∈ ⌜r 0⌝ₛ ∧
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 15⌝ₛ,⌜v 19⌝ₛ,⌜r 14⌝ₛ) ∧
  ⌜Formula.isSequenceOfLength kpair_convention_l⌝ₚ(⌜r 16⌝ₛ,⌜r 15⌝ₛ) ∧
  ⌜fun D o n Q G Λ => tg_raw_archive_links_m (fun i => [D,o,n,Q,G,Λ].get i)⌝ₚ
    (⌜r 16⌝ₛ,⌜r 19⌝ₛ,⌜r 20⌝ₛ,⌜r 21⌝ₛ,⌜r 22⌝ₛ,⌜r 23⌝ₛ) ∧
  ⌜it_map_m⌝ₚ(⌜r 22⌝ₛ,⌜r 19⌝ₛ,⌜r 20⌝ₛ,⌜r 18⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜r 1⌝ₛ,⌜v 7⌝ₛ,⌜r 18⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜r 7⌝ₛ,⌜v 6⌝ₛ,⌜r 18⌝ₛ) ∧
  ⌜fun Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D N S χ w C c e a b z h => tg_raw_archive_views_m
    (fun i => [Ω,S₀,X₀,R₀,γ₀,D₀,C₀,p,D,N,S,χ,w,C,c,e,a,b,z,h].get i)⌝ₚ
      (⌜r 0⌝ₛ,⌜r 1⌝ₛ,⌜r 2⌝ₛ,⌜r 3⌝ₛ,⌜r 4⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 18⌝ₛ,⌜r 16⌝ₛ,
        ⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 13⌝ₛ,⌜r 10⌝ₛ,⌜r 12⌝ₛ,⌜v 4⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜r 14⌝ₛ,⌜v 20⌝ₛ) ∧
  ⌜rr_ord_m⌝ₚ(⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 13⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜r 13⌝ₛ,⌜v 24⌝ₛ,⌜r 9⌝ₛ) ∧
  (∃ γ V t,
    ⌜fun X₀ R₀ γ₀ D₀ C₀ X R C q γ V t => tg_root_slice_m
      (fun i => [X₀,R₀,γ₀,D₀,C₀,X,R,C,q,γ,V,t].get i)⌝ₚ
      (⌜r 2⌝ₛ,⌜r 3⌝ₛ,⌜r 4⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 12⌝ₛ,⌜r 18⌝ₛ,γ,V,t) ∧
    ⌜rd_entry0_m⌝ₚ(⌜r 10⌝ₛ,V,⌜r 9⌝ₛ) ∧
    (∀ x, ⌜rd_entry0_m⌝ₚ(x,γ,⌜r 9⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,⌜v 24⌝ₛ,⌜r 9⌝ₛ)))⟫

@[simp] theorem tg_raw_request_closed_l {d} (r : Fin 24 → Term d) (v : Fin 46 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_raw_request_m r v).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_request_m,Definitional.Formula.FreeClosed,hr,hv,Fin.forall_fin_succ,
    rf_record_closed_l _ tg_issued0_closed_l _ _ _ _ (hr 8) (hr 9) (hr 12) (hr 17)]

theorem tg_raw_request_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (r : Fin 24 → Term d) (v : Fin 46 → Term d) : Formula.satisfies ρ (tg_raw_request_m r v) ↔
      Tg_raw_request_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ) ((r 17).eval ρ) ((r 18).eval ρ)
        ⟨(r 19).eval ρ,(r 20).eval ρ,(r 21).eval ρ,(r 22).eval ρ,(r 23).eval ρ⟩
        (fun i => (v i).eval ρ) := by
  simp only [tg_raw_request_m,Formula.satisfies_conj_iff,tg_context_data_sat_l (kp_pair_l hKP),
    rf_record_sat_l (kp_pair_l hKP) _ _ tg_issued0_closed_l,rf_tuple_sat_l (kp_pair_l hKP),
    Formula.satisfies_extensionalEq_iff_eq hKP.1,Formula.satisfies_isOmega_iff,
    rr_layer_sat_l (kp_pair_l hKP) hKP.1,Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),Formula.satisfies_isSequenceOfLength_iff (kp_pair_l hKP) hKP.1,
    tg_raw_archive_links_sat_l (kp_pair_l hKP) hKP.1,it_map_sat_l hKP.1,rd_entry0_sat_l hKP.1,
    tg_raw_archive_views_sat_l hKP,rr_ord_sat_l (kp_pair_l hKP),Formula.satisfies_exists_iff,
    tg_root_slice_sat_l (kp_pair_l hKP) hKP.1,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,List.get]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q⟩,
    fun h => ⟨h.context,h.record,h.values,h.omega,h.external_omega,h.numbers,h.finite,h.index,
      h.sequence,h.links,h.origin,h.name,h.alphabet,h.views,h.ordinal,h.below,h.slice⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原迭代六十六项状态的完整对象语言

二十项头部与四十六项控制记录保持原有坐标。原树、实际请求、原对局
和沿根切片保存的临界界均进入同一状态公式，供响应关系及内部递归使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 固定参数：ω,c₀,o,X₀,R₀,γ₀,D₀,C₀,S₀,A₀,A。
-- 头部：X,R,w,z,η,C,m,n,T,Q,G,E,Λ,D,χ,c,q,r,k,f。
def tg_raw_iteration_m {d} (g : Fin 11 → Term d) (v : Fin 20 → Term d)
    (a : Fin 46 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜v 7⌝ₛ ∈ ⌜g 0⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜v 6⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜it_tree_m⌝ₚ(⌜g 0⌝ₛ,⌜g 1⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ) ∧
    ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜v 12⌝ₛ) ∧
    (∀ i L, ⌜rd_entry0_m⌝ₚ(i,L,⌜v 12⌝ₛ) ↔
      (∃ p κ F, ⌜rd_entry0_m⌝ₚ(i,p,⌜v 11⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p,κ,L,F))) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 7⌝ₛ,⌜v 15⌝ₛ,⌜v 9⌝ₛ) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 15⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜g 2⌝ₛ,⌜g 1⌝ₛ,⌜v 9⌝ₛ)⟫)
  (.conj (tg_raw_request_m (fun i =>
    [g 0,g 8,g 3,g 4,g 5,g 6,g 7,g 9,v 0,v 1,v 2,v 4,v 5,v 14,v 3,v 18,v 13,v 17,v 16,
      g 2,v 7,v 9,v 10,v 12].get i) a)
    (.conj (tg_prefix_m (v 18) (g 10) (v 0) (v 1) (v 5) (a 4) (a 3) (a 20) (v 3) (v 16) (v 19))
      (tg_raw_critical_m (fun i => [g 3,g 4,g 5,g 6,g 7,g 2,v 9,v 10,v 11].get i))))

@[simp] theorem tg_raw_iteration_closed_l {d} (g : Fin 11 → Term d) (v : Fin 20 → Term d)
    (a : Fin 46 → Term d) (hg : ∀ i, (g i).freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (ha : ∀ i, (a i).freeSupport = []) :
    (tg_raw_iteration_m g v a).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_m,Definitional.Formula.FreeClosed,hg,hv,ha,Fin.forall_fin_succ]

theorem tg_raw_iteration_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d)
    (g : Fin 11 → Term d) (v : Fin 20 → Term d) (a : Fin 46 → Term d) :
    Formula.satisfies ρ (tg_raw_iteration_m g v a) ↔
      Tg_raw_iteration_d hZF ((g 0).eval ρ) ((g 1).eval ρ) ((g 2).eval ρ) ((g 3).eval ρ)
        ((g 4).eval ρ) ((g 5).eval ρ) ((g 6).eval ρ) ((g 7).eval ρ) ((g 8).eval ρ)
        ((g 9).eval ρ) ((g 10).eval ρ) (fun i => (v i).eval ρ) (fun i => (a i).eval ρ) := by
  simp only [tg_raw_iteration_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    KP.succ0_sat_l hZF.1,it_tree_sat_l hZF,Formula.satisfies_isFunction_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hZF.1,
    Formula.satisfies_exists_iff,it_payload_sat_l hZF.1,smdl_sat_l (kp_pair_l (ZF.modelsKP hZF)),
    tg_raw_request_sat_l (ZF.modelsKP hZF),tg_prefix_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    tg_raw_critical_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,Definitional.Term.eval_weaken,List.get]
  exact ⟨fun ⟨⟨a,b,c,d,e,f,g,h⟩,i,j,k⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k⟩,
    fun h => ⟨⟨h.finite,h.successor,h.tree,h.levels_function,h.levels,h.node,h.model,h.root_node⟩,
      h.request,h.play,h.critical⟩⟩

def tg_raw_iteration_code_m {d} (g : Fin 11 → Term d) (s : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun t => t.rename (Fin.natAdd 66)
  rb_exists_m (.conj (rt_tuple_m (fun i : Fin 66 => .bound (i.castAdd d)) (e s))
    (tg_raw_iteration_m (fun i => e (g i))
      (fun i => .bound ((i.castAdd 46).castAdd d)) (fun i => .bound ((Fin.natAdd 20 i).castAdd d))))

@[simp] theorem tg_raw_iteration_code_closed_l {d} (g : Fin 11 → Term d) (s : Term d)
    (hg : ∀ i, (g i).freeSupport = []) (hs : s.freeSupport = []) :
    (tg_raw_iteration_code_m g s).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_code_m,Definitional.Formula.FreeClosed,hg]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)

theorem tg_raw_iteration_code_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d)
    (g : Fin 11 → Term d) (s : Term d) : Formula.satisfies ρ (tg_raw_iteration_code_m g s) ↔
      Tg_raw_iteration_code_d hZF ((g 0).eval ρ) ((g 1).eval ρ) ((g 2).eval ρ) ((g 3).eval ρ)
        ((g 4).eval ρ) ((g 5).eval ρ) ((g 6).eval ρ) ((g 7).eval ρ) ((g 8).eval ρ)
        ((g 9).eval ρ) ((g 10).eval ρ) (s.eval ρ) := by
  simp only [tg_raw_iteration_code_m,Tg_raw_iteration_code_d,rb_exists_sat_l,
    Formula.satisfies_conj_iff,rt_tuple_sat_l hZF.1,tg_raw_iteration_sat_l hZF,rb_old_eval_l,
    Term.eval_bound,Fin.addCases_left]

end YesMetaZFC.SetTheory.LargeCardinal
