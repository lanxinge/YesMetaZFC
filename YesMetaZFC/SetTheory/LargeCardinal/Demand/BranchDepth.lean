import YesMetaZFC.SetTheory.LargeCardinal.Demand.IterationSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Demand.IterationStep
import YesMetaZFC.Model.SetTheory.ClassResponse
import YesMetaZFC.SetTheory.Descriptive.Demand.InputIteration
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameStage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail

/-! # 实际奇父边与深度更新的一阶表示 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def td_parent_old_m {d} (Ω : Term d) (v : Fin 19 → Term d) (k j : Term d)
    (s : Fin 73 → Term d) (w : Fin 75 → Term d) : Formula 1 d :=
  .conj (.mem (w 73) (v 12)) (.conj (rd_entry0_m (w 73) (w 74) (v 11))
    (.conj (rt_tuple_m (fun i : Fin 73 => w (i.castAdd 2)) (w 74)) (.conj (set[d] ⟪
      ⌜w 62⌝ₛ = ⌜k⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜s 70⌝ₛ,⌜w 70⌝ₛ) ∧
      (∀ p y, ⌜rd_entry0_m⌝ₚ(p,y,⌜s 71⌝ₛ) ↔
        ⌜td_depth_next_m⌝ₚ(⌜Ω⌝ₛ,⌜w 70⌝ₛ,⌜w 71⌝ₛ,⌜w 72⌝ₛ,⌜j⌝ₛ,p,y))⟫)
      (td_aux_growth_m (s 64) (s 65) j (fun i => w (i.castAdd 13)) (fun i => s (i.castAdd 11))))))

def td_parent_m {d} (Ω : Term d) (v : Fin 19 → Term d) (k G : Term d) (s : Fin 73 → Term d) : Formula 1 d :=
  let e : Term d → Term (75+(d+1)) := fun t => t.weaken.rename (Fin.natAdd 75)
  .existsE (.conj (it_map_m G.weaken k.weaken (v 6).weaken .newest)
    (.disj (.conj (Formula.extensionalEq k.weaken (v 5).weaken) (Formula.isEmpty (s 70).weaken))
      (rb_exists_m (td_parent_old_m (e Ω) (fun i => e (v i)) (e k)
        ((Term.newest : Term (d+1)).rename (Fin.natAdd 75)) (fun i => e (s i))
        (fun i => .bound (i.castAdd (d+1)))))))

@[simp] theorem td_parent_closed_l {d} (Ω : Term d) (v : Fin 19 → Term d) (k G : Term d) (s : Fin 73 → Term d)
    (hΩ : Ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (hk : k.freeSupport = []) (hG : G.freeSupport = []) (hs : ∀ i, (s i).freeSupport = []) :
    (td_parent_m Ω v k G s).FreeClosed := by
  simp -implicitDefEqProofs [td_parent_m,td_parent_old_m,Definitional.Formula.FreeClosed,hΩ,hv,hk,hG,hs]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

set_option maxRecDepth 2048 in
theorem td_parent_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (ρ : Env M d)
    (Ω : Term d) (v : Fin 19 → Term d) (k G : Term d) (s : Fin 73 → Term d) :
    Formula.satisfies ρ (td_parent_m Ω v k G s) ↔
      Td_parent_d I (Ω.eval ρ) (fun i => (v i).eval ρ) (k.eval ρ) (G.eval ρ)
        (Td_archive_row_d.from_values_d (fun i => (s i).eval ρ)) := by
  simp only [td_parent_m,td_parent_old_m,Td_parent_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,it_map_sat_l hE,Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Formula.satisfies_isEmpty_iff,rb_exists_sat_l,
    Formula.satisfies_mem_iff,rd_entry0_sat_l hE,rt_tuple_sat_l hE,KP.succ0_sat_l hE,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,td_depth_next_sat_l hE,
    td_aux_growth_sat_l I hE,
    rb_old_eval_l,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound,
    Fin.addCases_left,Td_archive_row_d.from_values_d]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w,hl,entry,tuple,⟨index,depth,table⟩,growth⟩
    let old := Td_archive_row_d.from_values_d (fun i : Fin 73 => w (i.castAdd 2))
    exact ⟨w 73,w 74,old,hl,entry,by simpa only [old,Td_archive_row_d.values_from_l] using tuple,
      index,depth,table,growth⟩
  · rintro ⟨l,r,old,hl,entry,tuple,index,depth,table,growth⟩
    let w : Fin 75 → M.Domain := Fin.addCases (m := 73) (n := 2) old.values_d (fun i => [l,r].get i)
    refine ⟨w,hl,entry,tuple,⟨?_,?_,?_⟩,?_⟩
    · exact index
    · exact depth
    · exact table
    · have eq : (fun i : Fin 62 => w (i.castAdd 13)) = old.v := by
        funext i
        change w ((i.castAdd 11).castAdd 2) = old.v i
        simp only [w,Fin.addCases_left,Td_archive_row_d.values_d]
      exact eq.symm ▸ growth

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整原回合后继的可定义响应关系 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def td_run_input_body_m {d} (x J : Term d) (w : Fin 19 → Term d) (a b : Fin 47 → Term d)
    (u : Fin 51 → Term d) : Formula 1 d :=
  .conj (rb_conj_m (fun i : Fin 47 => rd_entry0_m (a i) (u (i.castAdd 4)) J))
  (.conj (rb_conj_m (fun i : Fin 19 => Formula.extensionalEq (b (i.castAdd 28)) (u ((i.castAdd 28).castAdd 4))))
  (.conj (rd_entry0_m x (u 50) (w 3))
    (rr_truth_m (𝒞 := kpair_convention_l) td_digit0_m (w 0) (w 1)
      (td_digit_values_d (fun i => u (i.castAdd 4)) b (u 47) (u 48) (u 49) (u 50)))))

def td_run_input_m {d} (x J : Term d) (w : Fin 19 → Term d) (a b : Fin 47 → Term d) : Formula 1 d :=
  let e : Term d → Term (51+d) := fun t => t.rename (Fin.natAdd 51)
  rb_exists_m (td_run_input_body_m (e x) (e J) (fun i => e (w i)) (fun i => e (a i)) (fun i => e (b i))
    (fun i => .bound (i.castAdd d)))

@[simp] theorem td_run_input_closed_l {d} (x J : Term d) (w : Fin 19 → Term d) (a b : Fin 47 → Term d)
    (hx : x.freeSupport = []) (hj : J.freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (ha : ∀ i, (a i).freeSupport = []) (hb : ∀ i, (b i).freeSupport = []) :
    (td_run_input_m x J w a b).FreeClosed := by
  simp -implicitDefEqProofs [td_run_input_m,td_run_input_body_m,Definitional.Formula.FreeClosed,hx,hj,hw,ha,hb]
  apply rr_truth_closed_l td_digit0_m td_digit0_closed_l <;>
    simp [hw,hb,td_digit_values_d,Fin.forall_fin_succ]

theorem td_run_input_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (x J : Term d) (w : Fin 19 → Term d) (a b : Fin 47 → Term d) :
    Formula.satisfies ρ (td_run_input_m x J w a b) ↔
      ∃ u : Fin 47 → M.Domain, (∀ i, Rd_entry_d ((a i).eval ρ) (u i) (J.eval ρ)) ∧
        (∀ i : Fin 19, (b (i.castAdd 28)).eval ρ = u (i.castAdd 28)) ∧
        ∃ h t y z, Rd_entry_d (x.eval ρ) z ((w 3).eval ρ) ∧
          Rr_truth_d (kp_pair_l hKP) ((w 0).eval ρ) ((w 1).eval ρ) td_digit0_m
            (td_digit_values_d u (fun i => (b i).eval ρ) h t y z) := by
  simp only [td_run_input_m,td_run_input_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,rb_conj_sat_l,
    rd_entry0_sat_l hKP.1,Formula.satisfies_extensionalEq_iff_eq hKP.1,
    rr_truth_sat_l (kp_pair_l hKP) _ td_digit0_m td_digit0_closed_l,td_digit_values_map_l,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,points,head,xz,move⟩
    exact ⟨fun i => u (i.castAdd 4),points,head,u 47,u 48,u 49,u 50,xz,move⟩
  · rintro ⟨u,points,head,h,t,y,z,xz,move⟩
    let v : Fin 51 → M.Domain := Fin.addCases (m := 47) (n := 4) u (fun i => [h,t,y,z].get i)
    refine ⟨v,?_,?_,xz,move⟩
    · simpa only [v,Fin.addCases_left] using points
    · simpa only [v,Fin.addCases_left] using head

private def td_step_tail_m {d} (Ω : Term d) (v w : Fin 19 → Term d) (k G : Term d) : Formula 1 d :=
  let e : Term d → Term (74+d) := fun t => t.rename (Fin.natAdd 74)
  let s : Fin 73 → Term (74+d) := fun i => .bound ((i.castAdd 1).castAdd d)
  let r : Term (74+d) := .bound ((73 : Fin 74).castAdd d)
  rb_exists_m (.conj (Formula.extensionalEq (s 62) (e (v 6))) (.conj (rt_tuple_m s r)
    (.conj (td_parent_m (e Ω) (fun i => e (v i)) (e k) (e G) s)
      (set[74+d] ⟪∀ i t, ⌜rd_entry0_m⌝ₚ(i,t,⌜e (w 11)⌝ₛ) ↔
        ⌜rd_entry0_m⌝ₚ(i,t,⌜e (v 11)⌝ₛ) ∨ i = ⌜e (v 12)⌝ₛ ∧ t = ⌜r⌝ₛ⟫))))

@[simp] private theorem td_step_tail_closed_l {d} (Ω : Term d) (v w : Fin 19 → Term d) (k G : Term d)
    (hΩ : Ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (hk : k.freeSupport = []) (hG : G.freeSupport = []) : (td_step_tail_m Ω v w k G).FreeClosed := by
  simp -implicitDefEqProofs [td_step_tail_m,Definitional.Formula.FreeClosed,hΩ,hv,hw,hk,hG]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

set_option maxRecDepth 2048 in
private theorem td_step_tail_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (ρ : Env M d)
    (Ω : Term d) (v w : Fin 19 → Term d) (k G : Term d) :
    Formula.satisfies ρ (td_step_tail_m Ω v w k G) ↔
      ∃ s : Td_archive_row_d M.Domain, ∃ r,
        s.i = (v 6).eval ρ ∧ Rt_tuple_d s.values_d r ∧
        Td_parent_d I (Ω.eval ρ) (fun i => (v i).eval ρ) (k.eval ρ) (G.eval ρ) s ∧
        (∀ i t, Rd_entry_d i t ((w 11).eval ρ) ↔ Rd_entry_d i t ((v 11).eval ρ) ∨ i = (v 12).eval ρ ∧ t = r) := by
  simp only [td_step_tail_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,rt_tuple_sat_l hE,td_parent_sat_l I hE,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hE,
    Formula.satisfies_disj_iff,Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨v,index,tuple,parent,append⟩
    refine ⟨Td_archive_row_d.from_values_d (fun i : Fin 73 => v (i.castAdd 1)),v 73,index,?_,parent,append⟩
    simpa only [Td_archive_row_d.values_from_l] using tuple
  · rintro ⟨s,r,index,tuple,parent,append⟩
    let u : Fin 74 → M.Domain := Fin.addCases (m := 73) (n := 1) s.values_d (fun _ => r)
    refine ⟨u,index,tuple,?_,append⟩
    simpa only [u,Fin.addCases_left,Td_archive_row_d.from_values_l] using parent

private def td_run_step_body_m {d} (g : Fin 10 → Term d) (x : Term d) (v w : Fin 19 → Term d)
    (a b : Fin 47 → Term d) (e : Fin 6 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜it_tree_m⌝ₚ(⌜g 0⌝ₛ,⌜g 1⌝ₛ,⌜w 5⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ) ∧
    ⌜it_extension_m⌝ₚ(⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜e 0⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,
      ⌜w 5⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ) ∧
    ⌜it_extension_m⌝ₚ(⌜w 5⌝ₛ,⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ,
      ⌜w 6⌝ₛ,⌜w 7⌝ₛ,⌜w 8⌝ₛ,⌜w 9⌝ₛ,⌜w 10⌝ₛ) ∧
    ⌜it_map_m⌝ₚ(⌜w 9⌝ₛ,⌜v 5⌝ₛ,⌜w 5⌝ₛ,⌜e 5⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(⌜w 12⌝ₛ,⌜v 12⌝ₛ)⟫)
  (.conj (td_run_input_m x (e 5) w a b) (td_step_tail_m (g 0) v w (e 0) (e 3)))

def td_run_step_m {d} (g : Fin 10 → Term d) (x : Term d) (v w : Fin 19 → Term d)
    (a b : Fin 47 → Term d) : Formula 1 d :=
  let e : Term d → Term (6+d) := fun t => t.rename (Fin.natAdd 6)
  .conj (ic_round_m (g 0) (td_copy_frame_d v) (td_copy_frame_d w))
    (rb_exists_m (td_run_step_body_m (fun i => e (g i)) (e x) (fun i => e (v i)) (fun i => e (w i))
      (fun i => e (a i)) (fun i => e (b i)) (fun i => .bound (i.castAdd d))))

@[simp] theorem td_run_step_closed_l {d} (g : Fin 10 → Term d) (x : Term d) (v w : Fin 19 → Term d)
    (a b : Fin 47 → Term d) (hg : ∀ i, (g i).freeSupport = []) (hx : x.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (ha : ∀ i, (a i).freeSupport = []) (hb : ∀ i, (b i).freeSupport = []) :
    (td_run_step_m g x v w a b).FreeClosed := by
  simp -implicitDefEqProofs [td_run_step_m,td_run_step_body_m,Definitional.Formula.FreeClosed,
    td_copy_frame_d,hg,hx,hv,hw,ha,hb]

theorem td_run_step_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (g : Fin 10 → Term d) (x : Term d)
    (v w : Fin 19 → Term d) (a b : Fin 47 → Term d) :
    Formula.satisfies ρ (td_run_step_m g x v w a b) ↔
      Td_run_step_d hZF (fun i => (g i).eval ρ) (x.eval ρ) (fun i => (v i).eval ρ)
        (fun i => (w i).eval ρ) (fun i => (a i).eval ρ) (fun i => (b i).eval ρ) := by
  simp only [td_run_step_m,Td_run_step_d,Formula.satisfies_conj_iff,ic_round_sat_l hZF]
  apply and_congr_right; intro _
  simp only [td_run_step_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    it_tree_sat_l hZF,it_extension_sat_l hZF.1,it_map_sat_l hZF.1,KP.succ0_sat_l hZF.1,
    td_run_input_sat_l (ZF.modelsKP hZF),td_step_tail_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  exact ⟨fun ⟨e,⟨a,b,c,d,f⟩,g,h⟩ => ⟨e 0,e 1,e 2,e 3,e 4,e 5,a,b,c,d,f,g,h⟩,
    fun ⟨k,T,Q,G,E,J,a,b,c,d,e,f,g⟩ => ⟨fun i => [k,T,Q,G,E,J].get i,⟨a,b,c,d,e⟩,f,g⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部原输入共用的一张内部响应表

总性由两种实际回合产生，状态及边关系均有完整对象公式。
反射闭包和模型内集合选择固定响应表，不选择外部自然数序列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Td_edge_d (g : Fin 10 → M.Domain) (x s t : M.Domain) : Prop :=
  ∃ v w : Fin 66 → M.Domain, Rt_tuple_d v s ∧ Rt_tuple_d w t ∧
    Td_run_step_d hZF g x (fun i => v (i.castAdd 47)) (fun i => w (i.castAdd 47))
      (fun i => v (Fin.natAdd 19 i)) (fun i => w (Fin.natAdd 19 i))

def td_edge_m {d} (g : Fin 10 → Term d) (x s t : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun z => z.rename (Fin.natAdd 66)
  let f : Term (66+d) → Term (66+(66+d)) := fun z => z.rename (Fin.natAdd 66)
  let v : Fin 66 → Term (66+(66+d)) := fun i => f (.bound (i.castAdd d))
  let w : Fin 66 → Term (66+(66+d)) := fun i => .bound (i.castAdd (66+d))
  rb_exists_m (n := 66) (rb_exists_m (n := 66) (.conj (rt_tuple_m v (f (e s)))
    (.conj (rt_tuple_m w (f (e t))) (td_run_step_m (fun i => f (e (g i))) (f (e x))
      (fun i => v (i.castAdd 47)) (fun i => w (i.castAdd 47))
      (fun i => v (Fin.natAdd 19 i)) (fun i => w (Fin.natAdd 19 i))))))

@[simp] theorem td_edge_closed_l {d} (g : Fin 10 → Term d) (x s t : Term d)
    (hg : ∀ i, (g i).freeSupport = []) (hx : x.freeSupport = [])
    (hs : s.freeSupport = []) (ht : t.freeSupport = []) : (td_edge_m g x s t).FreeClosed := by
  simp -implicitDefEqProofs [td_edge_m,Definitional.Formula.FreeClosed,hg,hx]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using ht)⟩

theorem td_edge_sat_l {d} (ρ : Env M d) (g : Fin 10 → Term d) (x s t : Term d) :
    Formula.satisfies ρ (td_edge_m g x s t) ↔ Td_edge_d hZF (fun i => (g i).eval ρ) (x.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [td_edge_m,Td_edge_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,td_run_step_sat_l hZF,Definitional.Term.eval_rename,
    Env.reindex,Function.comp_def,Term.eval_bound,Fin.addCases_left,Fin.addCases_right]

theorem Td_edge_d.read_l {g : Fin 10 → M.Domain} {x s t : M.Domain} {v w : Fin 66 → M.Domain}
    (h : Td_edge_d hZF g x s t) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Td_run_step_d hZF g x (fun i => v (i.castAdd 47)) (fun i => w (i.castAdd 47))
      (fun i => v (Fin.natAdd 19 i)) (fun i => w (Fin.natAdd 19 i)) := by
  obtain ⟨a,b,pa,pb,next⟩ := h
  exact rt_tuple_inj_l pa ps ▸ rt_tuple_inj_l pb pt ▸ next

structure Td_choice_d (g : Fin 10 → M.Domain) (A r X D K : M.Domain) : Prop where
  initial : Td_state_code_d hZF g r
  member : M.mem r X
  product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) D X A
  function : Fn0_d D X K
  step : ∀ s x t p, Td_state_code_d hZF g s →
    (kp_pair_l (ZF.modelsKP hZF)).Codes p s x → Rd_entry_d p t K →
      Td_state_code_d hZF g t ∧ Td_edge_d hZF g x s t

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZ)

theorem Td_state_code_d.advance_l {g : Fin 10 → M.Domain} {wr zr x s : M.Domain}
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (numbers : Rr_layer_d I (g 0) (g 3) (g 4) wr zr)
    (h : Td_state_code_d hZ g s) (hx : M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4)) :
    ∃ t, Td_state_code_d hZ g t ∧ Td_edge_d hZ g x s t := by
  obtain ⟨v,code,state⟩ := h
  obtain ⟨w,b,next,edge⟩ := state.advance_l hZFC root numbers hx
  obtain ⟨t,tuple,valid⟩ := next.pack_l hZ
  refine ⟨t,valid,v,_,code,tuple,?_⟩
  simpa only [Fin.addCases_left,Fin.addCases_right] using edge

theorem Td_state_code_d.choice_l {g : Fin 10 → M.Domain} {wr zr A r : M.Domain}
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (numbers : Rr_layer_d I (g 0) (g 3) (g 4) wr zr)
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    (initial : Td_state_code_d hZ g r) : ∃ X D K, Td_choice_d hZ g A r X D K := by
  have hw : M.IsOmega (g 0) := initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 10 := ⟨g,fun _ => g 0⟩
  let V : UnarySchema 10 := { body := td_state_code_m (fun i => .bound i.succ) .newest }
  let φ : UnarySchema 12 := { body := td_edge_m (fun i => .bound ⟨i.val+3,by omega⟩) (.bound 1) (.bound 2) .newest }
  have valid s : V.denote ρ s ↔ Td_state_code_d hZ g s := td_state_code_sat_l hZ ..
  have action s x t : φ.denote ((ρ.push s).push x) t ↔ Td_edge_d hZ g x s t := td_edge_sat_l hZ ..
  obtain ⟨X,D,K,member,product,function,steps⟩ := ZFC.class_response_l I hZFC V φ ρ (a := r) hw (by
    intro s x hs hx
    obtain ⟨t,next,edge⟩ := ((valid s).mp hs).advance_l hZFC root numbers ((letters x).mp hx)
    exact ⟨t,(valid t).mpr next,(action s x t).mpr edge⟩)
  refine ⟨X,D,K,initial,member,product,fn0_of_function_l (ZF.modelsKP hZ) function,?_⟩
  intro s x t p state pair entry
  obtain ⟨next,edge⟩ := steps s x t p pair entry ((valid s).mpr state)
  exact ⟨(valid t).mp next,(action s x t).mp edge⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原响应表上的内部全 ω 运行

模型自己的分离与 ω 归纳保持全部六十六项状态。原档案轮号恰是递归轮号，
每次后继保存两条原边、实际输入步及奇父深度方程。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_run_d (g : Fin 10 → M.Domain) (X K r a f H : M.Domain) : Prop where
  recursion : Gi_d hZF true (g 0) X K r a f H
  rows : ∀ n s, Rd_entry_d n s H → Td_state_code_d hZF g s ∧ Rt_coord_d (12 : Fin 66) s n
  steps : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
    ∃ x, Gi_input_d hZF true (g 0) a f i x ∧ Td_edge_d hZF g x s t

theorem Td_choice_d.validate_l {g : Fin 10 → M.Domain} {A r X D K a f H : M.Domain}
    (choice : Td_choice_d hZF g A r X D K) (zero : Rt_coord_d (12 : Fin 66) r (g 2))
    (empty : ∀ x, ¬ M.mem x (g 2)) (run : Gi_d hZF true (g 0) X K r a f H) : Td_run_d hZF g X K r a f H := by
  have hw : M.IsOmega (g 0) := choice.initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 11 := ⟨Fin.cases H g,fun _ => H⟩
  let φ : UnarySchema 11 := {
    body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 2))
      (.conj (td_state_code_m (fun i => .bound ⟨i.val+3,by omega⟩) .newest)
        (rt_coord_m (12 : Fin 66) .newest (.bound 1)))) }
  have sat n : φ.denote ρ n ↔ ∀ s, Rd_entry_d n s H → Td_state_code_d hZF g s ∧ Rt_coord_d (12 : Fin 66) s n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_conj_iff,td_state_code_sat_l hZF,rt_coord_sat_l hZF.1]
    rfl
  have all : ∀ n, M.mem n (g 0) → ∀ s, Rd_entry_d n s H →
      Td_state_code_d hZF g s ∧ Rt_coord_d (12 : Fin 66) s n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ (g 0)
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s hs
      have ez := hZF.1.eq_of_same_members z (g 2) (fun x => iff_of_false (hz x) (empty x))
      have es := (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 z s r hs (run.2.1 z hz)
      exact ⟨es.symm ▸ choice.initial,es.symm ▸ ez.symm ▸ zero⟩
    · intro i hi ih j succ t ht
      obtain ⟨s,_,hs⟩ := run.1.2.1 i hi
      obtain ⟨x,p,_,pair,entry⟩ := run.2.2 i j s t succ hs ht
      obtain ⟨next,v,w,ps,pt,_,edge⟩ := choice.step s x t p (ih s hs).1 pair entry
      obtain ⟨_,_,_,_,_,_,_,_,_,_,step,_⟩ := edge
      have eq : v 12 = i := (ih s hs).2.read_l v ps
      have step : M.SuccessorOf (w 12) i := eq ▸ step
      exact ⟨next,w,pt,step.eq hZF.1 succ⟩
  have rows n s (hs : Rd_entry_d n s H) := all n (run.1.bound_l hs).1 s hs
  refine ⟨run,rows,?_⟩
  intro i j s t succ hs ht
  obtain ⟨x,p,input,pair,entry⟩ := run.2.2 i j s t succ hs ht
  exact ⟨x,input,(choice.step s x t p (rows i s hs).1 pair entry).2⟩

theorem Td_choice_d.run_l {g : Fin 10 → M.Domain} {A r X D K a f : M.Domain}
    (choice : Td_choice_d hZF g A r X D K) (zero : Rt_coord_d (12 : Fin 66) r (g 2))
    (empty : ∀ x, ¬ M.mem x (g 2)) (ha : M.mem a A)
    (ff : M.IsSetFunction I f) (range : ∀ i x, Rd_entry_d i x f → M.mem x A) :
    ∃ H, Td_run_d hZF g X K r a f H := by
  have hw : M.IsOmega (g 0) := choice.initial.elim fun _ h => h.2.tree.omega
  obtain ⟨H,run⟩ := gi_exists_l hZF (b := true) hw choice.product choice.function choice.member ha ff range
  exact ⟨H,choice.validate_l hZF zero empty run⟩

theorem Td_run_d.read_l {g : Fin 10 → M.Domain} {X K r a f H i s : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (tuple : Rt_tuple_d v s) :
    Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)) :=
  (run.rows i s hs).1.read_l hZF tuple

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

theorem Td_state_d.recursion_l {g : Fin 10 → M.Domain} {v : Fin 19 → M.Domain} {b : Fin 47 → M.Domain}
    {wr zr A a : M.Domain} (root : Zc_model_d J (g 0) (g 1) (g 3) (g 4))
    (numbers : Rr_layer_d J (g 0) (g 3) (g 4) wr zr)
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    (initial : Td_state_d hZ g v b) (zero : v 12 = g 2) (empty : ∀ x, ¬ M.mem x (g 2)) (ha : M.mem a A) :
    ∃ r X D K, Rt_tuple_d (Fin.addCases (m := 19) (n := 47) (motive := fun _ => M.Domain) v b) r ∧
      Td_choice_d hZ g A r X D K ∧ ∀ f, Fn0_d (g 0) A f → ∃ H, Td_run_d hZ g X K r a f H := by
  obtain ⟨r,tuple,code⟩ := initial.pack_l hZ
  obtain ⟨X,D,K,choice⟩ := code.choice_l hZFC root numbers letters
  have index : Rt_coord_d (12 : Fin 66) r (g 2) :=
    ⟨_,tuple,(Fin.addCases_left (m := 19) (n := 47) (motive := fun _ => M.Domain) 12).trans zero⟩
  refine ⟨r,X,D,K,tuple,choice,fun f ff => ?_⟩
  exact choice.run_l hZ index empty ha (fn0_function_l (ZF.modelsKP hZ) ff).1 (fun _ _ h => (ff.bound_l h).2)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 实际内部运行的并树与完整档案

公共树框架只重排十九项头部，支撑列来自同一操作图的实际载荷。
每条活动边在某个有限阶段出现，其所属强度证书沿同一模型列进入并树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def td_frame_idx_d : Fin 14 → Fin 66 := fun i => [0,1,2,3,4,14,6,5,7,8,9,10,18,11].get i

structure Td_union_d (g : Fin 10 → M.Domain) (H : M.Domain) (U : Fin 6 → M.Domain) : Prop where
  tree : It_tree_d hZF (g 0) (g 1) (g 0) (U 0) (U 1) (U 2) (U 3)
  levels_function : M.IsSetFunction I (U 4)
  levels : ∀ i L, Rd_entry_d i L (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ L F
  archive : M.IsSequenceOfLength I (U 5) (g 0)
  columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (td_frame_idx_d ⟨8+a.val,by omega⟩) H x
  restriction : ∀ i s (v : Fin 66 → M.Domain), Rd_entry_d i s H → Rt_tuple_d v s →
    ∀ x y, M.mem y (v 6) → (Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 7))
  owned : It_owned_d I (g 0) (U 1) (U 3)
  links : Td_archive_links_d (g 2) (U 1) (U 2) (U 3) (U 5)

theorem Td_run_step_d.keep_l {g : Fin 10 → M.Domain} {x : M.Domain} {v w : Fin 66 → M.Domain}
    (h : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (h' : Td_state_d hZF g (fun i => w (i.castAdd 47)) (fun i => w (Fin.natAdd 19 i)))
    (step : Td_run_step_d hZF g x (fun i => v (i.castAdd 47)) (fun i => w (i.castAdd 47))
      (fun i => v (Fin.natAdd 19 i)) (fun i => w (Fin.natAdd 19 i))) :
    Tg_tree_keep_d (fun i => v (td_frame_idx_d i)) (fun i => w (td_frame_idx_d i)) := by
  obtain ⟨k,T,Q,G,E,J,mid,e,e',edge,_,_,row,r,_,_,_,append⟩ := step.2
  obtain ⟨order,t,q,maps,moves⟩ := h.tree.extension_keep_l hZF e
  obtain ⟨order',t',q',maps',moves'⟩ := mid.extension_keep_l hZF e'
  have sub {a b : M.Domain} (s : M.SuccessorOf b a) : M.MemberSubset a b := fun x hx => (s x).mpr (Or.inl hx)
  have levels := it_levels_subset_l hZF.1 h.levels_function.1
    (fun i l => (h.levels i l).mp) (fun i l => (h'.levels i l).mpr) (fun x hx => moves' x (moves x hx))
  have archive : M.MemberSubset (v 11) (w 11) := by
    intro p hp
    obtain ⟨i,s,pair⟩ := h.sequence.2.1.1 p hp
    obtain ⟨p',pair',hp'⟩ := (append i s).mpr (Or.inl ⟨p,pair,hp⟩)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  refine ⟨fun x hx => sub e'.1 x (sub e.1 x hx),
    fun i j hj => (order' i j (sub e.1 j hj)).trans (order i j hj),?_,?_⟩
  · exact Fin.cases (fun x hx => t' x (t x hx)) (Fin.cases (fun x hx => q' x (q x hx))
      (Fin.cases (fun x hx => maps' x (maps x hx)) (Fin.cases (fun x hx => moves' x (moves x hx))
        (Fin.cases levels (Fin.cases archive (fun i => Fin.elim0 i))))))
  · intro i hi
    have old := (e'.2.1 i (v 5)).mpr (Or.inl ((e.2.1 i (v 5)).mpr (Or.inl hi)))
    exact h'.tree.diagram.order.trans i (v 5) (w 5) old (h'.tree.diagram.map_bound_l hZF edge)

variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}

theorem Td_run_d.omega_l (run : Td_run_d hZF g X K r a f H) : M.IsOmega (g 0) := by
  obtain ⟨o,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨_,_,state⟩ := (run.rows o r (run.recursion.2.1 o empty)).1
  exact state.tree.omega

theorem Td_run_d.span_l (run : Td_run_d hZF g X K r a f H)
    {i s m : M.Domain} (hs : Rd_entry_d i s H) (coord : Rt_coord_d (6 : Fin 66) s m) : M.mem i m := by
  have hw := run.omega_l hZF
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ s m,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 2)⌝ₛ,s,⌜(.bound 1 : Term 2)⌝ₛ) →
    ⌜(rt_coord_m (6 : Fin 66))⌝ₚ(s,m) → ⌜(.newest : Term 2)⌝ₛ ∈ m⟫ }
  have sat n : φ.denote ρ n ↔ ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 66) s m → M.mem n m := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  have all : ∀ n, M.mem n (g 0) → ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 66) s m → M.mem n m := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ (g 0)
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s m hs coord
      obtain ⟨v,code,eq⟩ := coord
      have state := run.read_l hZF hs code
      exact eq ▸ state.tree.diagram.order.ordinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
        ⟨v 5,state.successor.predecessor_mem⟩ hz
    · intro n hn ih j succ t m ht coord
      obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 n hn
      obtain ⟨x,_,v,w,ps,pt,step⟩ := run.steps n j s t succ hs ht
      have old := run.read_l hZF hs ps
      have bound := ih s (v 6) hs ⟨v,ps,rfl⟩
      have eq := coord.read_l w pt
      obtain ⟨_,_,_,_,_,_,mid,e,e',_⟩ := step.2
      have sub : M.MemberSubset j (v 6) := by
        intro z hz
        rcases (succ z).mp hz with hz | eq
        · exact old.tree.diagram.order.ordinal.transitive n bound z hz
        · exact (hZF.1.eq_of_same_members z n eq).symm ▸ bound
      have jm : M.mem j (w 5) := Structure.IsOrdinal.mem_of_properSubset hZF.1
        (KP.successor_isOrdinal (ZF.modelsKP hZF) (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) succ)
        mid.diagram.order.ordinal
        ⟨fun z hz => (e.1 z).mpr (Or.inl (sub z hz)),fun eq =>
          KP.mem_irrefl_d (ZF.modelsKP hZF) (v 6) (sub (v 6) ((eq (v 6)).mpr e.1.predecessor_mem))⟩
        (KP.difference_exists_d (ZF.modelsKP hZF) j (w 5))
      exact eq ▸ (e'.1 j).mpr (Or.inl jm)
  exact all i (run.recursion.1.bound_l hs).1 s m hs coord

theorem Td_run_d.frames_l (run : Td_run_d hZF g X K r a f H) :
    It_frames_d hZF td_frame_idx_d (g 0) (g 1) X H := by
  have hw := run.omega_l hZF
  refine ⟨run.recursion.1,?_,?_⟩
  · intro i s hs
    obtain ⟨v,code,state⟩ := (run.rows i s hs).1
    obtain ⟨m,succ,hm⟩ := hw.1.2 (v 5) state.finite
    have finite : M.mem (v 6) (g 0) := succ.eq hZF.1 state.successor ▸ hm
    exact ⟨v,code,state.tree,finite,run.span_l hZF hs ⟨v,code,rfl⟩,
      state.levels_function,state.levels,state.sequence.2.1⟩
  · have next i j s t (succ : M.SuccessorOf j i) (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H) :
        Tg_run_keep_d td_frame_idx_d s t := by
      obtain ⟨x,_,v,w,ps,pt,step⟩ := run.steps i j s t succ hs ht
      exact ⟨v,w,ps,pt,step.keep_l hZF (run.read_l hZF hs ps) (run.read_l hZF ht pt)⟩
    exact fun _ _ _ _ _ _ hs ht ps pt => Tg_run_keep_d.merge_l hZF hw run.recursion.1 next hs ht ps pt

theorem Td_run_d.union_l (run : Td_run_d hZF g X K r a f H) : ∃ U, Td_union_d hZF g H U := by
  have hw := run.omega_l hZF
  have frames := run.frames_l hZF
  obtain ⟨U,tree,lf,levels,archive,columns⟩ := frames.union_l hZF hw
  refine ⟨U,tree,lf,levels,⟨hw.isOrdinal (ZF.modelsKP hZF),archive,?_⟩,columns,?_,?_,?_⟩
  · intro i
    constructor
    · intro hi
      obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
      obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 j hj
      obtain ⟨v,code,state⟩ := (run.rows j s hs).1
      have index := (run.rows j s hs).2.read_l v code
      obtain ⟨t,p,pair,hp⟩ := (state.sequence.2.2 i).mp (index.symm ▸ succ.predecessor_mem)
      exact ⟨t,p,pair,(columns 5 p).mpr ⟨v,j,s,hs,code,hp⟩⟩
    · rintro ⟨t,p,pair,hp⟩
      obtain ⟨v,j,s,hs,code,hp⟩ := (columns 5 p).mp hp
      have state := run.read_l hZF hs code
      exact (hw.isOrdinal (ZF.modelsKP hZF)).transitive (v 12) state.round i
        ((state.sequence.2.2 i).mpr ⟨t,p,pair,hp⟩)
  · exact fun _ _ _ hs code _ _ hy => frames.order_l hZF columns hs code hy
  · intro i p κ L F ⟨q,pair,hq⟩ payload
    obtain ⟨v,n,s,hs,code,hq⟩ := (columns 3 q).mp hq
    obtain ⟨c,⟨r,pair',hr⟩,quality⟩ := (run.read_l hZF hs code).owned i p κ L F ⟨q,pair,hq⟩ payload
    exact ⟨c,⟨r,pair',(columns 1 r).mpr ⟨v,n,s,hs,code,hr⟩⟩,quality⟩
  · intro m r a ⟨p,pair,hp⟩ pack
    obtain ⟨v,n,s,hs,code,hp⟩ := (columns 5 p).mp hp
    obtain ⟨node,root,q,κ,F,move,payload⟩ :=
      (run.read_l hZF hs code).links m r a ⟨p,pair,hp⟩ pack
    have keep {a x y : M.Domain} (i : Fin 6) (eq : a = v (td_frame_idx_d ⟨8+i.val,by omega⟩))
        (entry : Rd_entry_d x y a) : Rd_entry_d x y (U i) := by
      obtain ⟨p,pair,hp⟩ := entry
      exact ⟨p,pair,(columns i p).mpr ⟨v,n,s,hs,code,eq ▸ hp⟩⟩
    obtain ⟨p,pair,entry⟩ := root
    exact ⟨keep 1 rfl node,⟨p,pair,keep 2 rfl entry⟩,q,κ,F,keep 3 rfl move,payload⟩

theorem Td_run_d.mono_l (run : Td_run_d hZF g X K r a f H) {i j s t : M.Domain}
    {v w : Fin 66 → M.Domain} (ij : M.mem i j) (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H)
    (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Tg_tree_keep_d (fun k => v (td_frame_idx_d k)) (fun k => w (td_frame_idx_d k)) := by
  let η : Env M 0 := ⟨Fin.elim0,fun _ => H⟩
  let φ : BinarySchema 0 := { body := tg_run_keep_m td_frame_idx_d (.bound 1) .newest }
  have sat s t : φ.denote η s t ↔ Tg_run_keep_d td_frame_idx_d s t := tg_run_keep_sat_l hZF.1 ..
  have chain := ZF.rel_chain_l I hZF φ η (run.omega_l hZF) (fn0_function_l (ZF.modelsKP hZF) run.recursion.1)
    (fun _ _ _ _ _ _ a b => (sat _ _).mpr (((sat _ _).mp a).trans_l ((sat _ _).mp b))) (by
      intro i j s t succ hs ht
      obtain ⟨_,_,v,w,ps,pt,step⟩ := run.steps i j s t succ hs ht
      exact (sat s t).mpr ⟨v,w,ps,pt,step.keep_l hZF (run.read_l hZF hs ps) (run.read_l hZF ht pt)⟩)
  obtain ⟨v',w',ps',pt',keep⟩ := (sat s t).mp (chain i j s t ij hs ht)
  exact rt_tuple_inj_l ps' ps ▸ rt_tuple_inj_l pt' pt ▸ keep

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 并档案中的实际节点、唯一性及与偶数枝分离 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_union_d.entry_l (u : Td_union_d hZF g H U) {v : Fin 66 → M.Domain} {i s x y : M.Domain}
    (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) (b : Fin 6)
    (entry : Rd_entry_d x y (v (td_frame_idx_d ⟨8+b.val,by omega⟩))) : Rd_entry_d x y (U b) := by
  obtain ⟨p,pair,hp⟩ := entry
  exact ⟨p,pair,(u.columns b p).mpr ⟨v,i,s,hs,code,hp⟩⟩

theorem Td_run_d.even_branch_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U) :
    ∃ B, It_branch_d (g 0) (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x :=
  (run.frames_l hZF).even_branch_l hZF u.tree u.columns
    (fun _ _ _ hs code => (run.read_l hZF hs code).successor)

theorem Td_run_d.archive_source_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p : M.Domain} (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p) :
    Td_archive_source_d I (g 0) (g 1) (g 3) (g 8) (g 9) (g 6) row := by
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨v,i,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
  exact ((run.read_l hZF hs code).archive m p ⟨q,pair,hq⟩ |>.read_l I tuple).1

theorem Td_run_d.archive_stage_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p s : M.Domain} (row : Td_archive_row_d M.Domain) {v : Fin 66 → M.Domain}
    (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p)
    (hs : Rd_entry_d m s H) (code : Rt_tuple_d v s) : row.i = v 6 := by
  have hm := (u.archive.2.2 m).mpr ⟨p,entry⟩
  obtain ⟨j,succ,hj⟩ := u.tree.omega.1.2 m hm
  obtain ⟨t,_,ht⟩ := run.recursion.1.2.1 j hj
  obtain ⟨_,_,v',w,ps,pt,next⟩ := run.steps m j s t succ hs ht
  have eq := rt_tuple_inj_l ps code
  subst v'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,new,q,index,pack,_,entries⟩ := next.2
  have added : Rd_entry_d (v 12) q (w 11) := (entries (v 12) q).mpr (Or.inr ⟨rfl,rfl⟩)
  have number : v 12 = m := (run.rows m s hs).2.read_l v code
  have global : Rd_entry_d m q (U 5) := number ▸ u.entry_l hZF ht pt 5 added
  have eq := u.archive.2.1.2 m q p global entry
  subst q
  have eq := Td_archive_row_d.eq_l (rt_tuple_inj_l pack tuple)
  subst new
  exact index

theorem Td_run_d.archive_order_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m n p q : M.Domain} (left right : Td_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (mn : M.mem m n) : M.mem left.i right.i := by
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 n hn
  obtain ⟨v,code,state⟩ := (run.rows n s hs).1
  have number : v 12 = n := (run.rows n s hs).2.read_l v code
  obtain ⟨p',entry⟩ := (state.sequence.2.2 m).mp (number.symm ▸ mn)
  have global := u.entry_l hZF hs code 5 entry
  have eq := u.archive.2.1.2 m p' p global hp
  subst p'
  have node := (state.links m p left entry cp).1
  have bound : M.mem left.i (v 6) := (state.tree.diagram.model_domain left.i).mpr ⟨left.c,node⟩
  exact (run.archive_stage_l hZF u right hq cq hs code).symm ▸ bound

theorem Td_run_d.archive_unique_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m n p q : M.Domain} (left right : Td_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (eq : left.i = right.i) :
    m = n ∧ p = q := by
  have hm := (u.archive.2.2 m).mpr ⟨p,hp⟩
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with same | mn | nm
  · have same := hZF.1.eq_of_same_members m n same
    subst n
    exact ⟨rfl,u.archive.2.1.2 m p q hp hq⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) right.i (eq ▸ run.archive_order_l hZF u left right hp hq cp cq mn)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) left.i (eq.symm ▸ run.archive_order_l hZF u right left hq hp cq cp nm)).elim

theorem Td_run_d.archive_not_even_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p : M.Domain} (row : Td_archive_row_d M.Domain)
    (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p) :
    ¬ Tg_even_d (5 : Fin 66) H (U 0) row.i := by
  rintro ⟨v,i,s,hs,code,edge⟩
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨w,j,t,ht,pack,hq⟩ := (u.columns 5 q).mp hq
  obtain ⟨k,r,z,hr,pz,keep,keep'⟩ := (run.frames_l hZF).merge i j s t v w hs ht code pack
  have old := run.read_l hZF hs code
  have zz := run.read_l hZF hr pz
  have vz := u.entry_l hZF hr pz 0
    (keep.2.2.2 (v 5) (old.tree.diagram.order.refl _ old.successor.predecessor_mem))
  have edge := u.tree.diagram.order.trans _ _ _ edge vz
  have edge := (u.restriction k r z hr pz _ _ zz.successor.predecessor_mem).mp edge
  exact zz.clear m p row ⟨q,pair,keep'.2.2.1 5 q hq⟩ tuple edge

theorem Td_run_d.archive_outside_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p e s₀ : M.Domain} {v₀ : Fin 66 → M.Domain} (row : Td_archive_row_d M.Domain)
    (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p)
    (empty : ∀ x, ¬ M.mem x e) (first : Rd_entry_d e s₀ H) (code₀ : Rt_tuple_d v₀ s₀) :
    ¬ M.mem row.i (v₀ 6) := by
  have hw := u.tree.omega
  have hm := (u.archive.2.2 m).mpr ⟨p,entry⟩
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 m hm
  obtain ⟨v,code,_⟩ := (run.rows m s hs).1
  have index := run.archive_stage_l hZF u row entry tuple hs code
  intro inside
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare e (run.recursion.1.bound_l first).1 m hm with eq | em | me
  · have eq := hZF.1.eq_of_same_members e m eq
    have es := (fn0_function_l (ZF.modelsKP hZF) run.recursion.1).1.2 m s s₀ hs (eq ▸ first)
    have coords := rt_tuple_inj_l code (es.symm ▸ code₀)
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) (v₀ 6) ((index.trans (congrFun coords 6)) ▸ inside)
  · have hin : M.mem row.i (v 6) := (run.mono_l hZF em first hs code₀ code).1 row.i inside
    rw [index] at hin
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) (v 6) hin
  · exact empty m me

theorem Td_run_d.archive_node_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p : M.Domain} (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5))
    (tuple : Rt_tuple_d row.values_d p) : Rd_entry_d row.i row.c (U 1) := by
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨v,i,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
  exact u.entry_l hZF hs code 1 ((run.read_l hZF hs code).links m p row ⟨q,pair,hq⟩ tuple).1

theorem Td_run_d.archive_index_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m n p q : M.Domain} (left right : Td_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (lt : M.mem left.i right.i) : M.mem m n := by
  have hm := (u.archive.2.2 m).mpr ⟨p,hp⟩
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with eq | mn | nm
  · have eq := hZF.1.eq_of_same_members m n eq
    have ep := u.archive.2.1.2 n p q (eq ▸ hp) hq
    have rows := Td_archive_row_d.eq_l (rt_tuple_inj_l cp (ep.symm ▸ cq))
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) right.i (congrArg Td_archive_row_d.i rows ▸ lt)).elim
  · exact mn
  · have back := run.archive_order_l hZF u right left hq hp cq cp nm
    have hleft := (u.tree.diagram.model_domain left.i).mpr ⟨left.c,run.archive_node_l hZF u left hp cp⟩
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) left.i
      ((u.tree.omega.members_areOrdinals (ZF.modelsKP hZF) left.i hleft).transitive right.i back left.i lt)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际奇节点的出生回合与原奇父边

从内部最早出现阶段读取两次原树延伸；非偶数节点只能是第一次新增的奇节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_birth_d (Ω H D T G B y : M.Domain) : Prop :=
  ∃ n s, ∃ v : Fin 66 → M.Domain, Rd_entry_d n s H ∧ Rt_tuple_d v s ∧ y = v 6 ∧
    ∃ k, ∃ row : Td_archive_row_d M.Domain, ∃ r,
      row.i = y ∧ Rd_entry_d (v 12) r D ∧ Rt_tuple_d row.values_d r ∧
      Td_parent_d I Ω (fun i => v (i.castAdd 47)) k G row ∧ It_pred_d T k y ∧ M.mem (v 5) B

theorem Td_run_d.birth_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    {B e s₀ y : M.Domain} {v₀ : Fin 66 → M.Domain}
    (even : ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x)
    (empty : ∀ x, ¬ M.mem x e) (first : Rd_entry_d e s₀ H) (code₀ : Rt_tuple_d v₀ s₀)
    (hy : M.mem y (g 0)) (outside : ¬ M.mem y (v₀ 6)) (notEven : ¬ M.mem y B) :
    Td_birth_d hZF (g 0) H (U 5) (U 0) (U 2) B y := by
  obtain ⟨l,k,t,s,w,v,succ,ht,ct,hs,code,old,hyv⟩ :=
    (run.frames_l hZF).first_l hZF v₀ empty first code₀ hy outside
  obtain ⟨_,_,w',v',ct',code',next⟩ := run.steps l k t s succ ht hs
  have eq := rt_tuple_inj_l ct' ct
  subst w'
  have eq := rt_tuple_inj_l code' code
  subst v'
  obtain ⟨a,T,Q,G,E,J,mid,e₁,e₂,_,_,_,row,r,index,rc,parent,entries⟩ := next.2
  rcases (e₂.1 y).mp hyv with hym | eq
  · rcases (e₁.1 y).mp hym with hyo | eq
    · exact (old hyo).elim
    · have eq := hZF.1.eq_of_same_members y (w 6) eq
      subst y
      have state := run.read_l hZF ht ct
      have ha : M.mem a (w 6) := by
        obtain ⟨_,_,choice⟩ := parent
        rcases choice with ⟨eq,_⟩ | ⟨l,r,old,_,entry,pack,eq,_⟩
        · exact eq.symm ▸ state.successor.predecessor_mem
        · exact eq ▸ (state.tree.diagram.model_domain old.i).mpr ⟨old.c,(state.links l r old entry pack).1⟩
      have keep₁ := state.tree.extension_keep_l hZF e₁
      have keep₂ := mid.extension_keep_l hZF e₂
      have hw := e₁.1.predecessor_mem
      have hyv := (e₂.1 _).mpr (Or.inl hw)
      have hav := (e₂.1 _).mpr (Or.inl ((e₁.1 _).mpr (Or.inl ha)))
      have tip i : Rd_entry_d i (w 6) T ↔ i = w 6 ∨ Rd_entry_d i a (w 7) :=
        (e₁.2.1 i (w 6)).trans ⟨fun h => h.elim
          (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) _ (state.tree.diagram.order.bound _ _ h).2).elim)
          And.right,fun h => Or.inr ⟨rfl,h⟩⟩
      have pred : It_pred_d (U 0) a (w 6) := ⟨ha,fun i =>
        (u.restriction k s v hs code i _ hyv).trans ((keep₂.1 i _ hw).trans
          ((tip i).trans (or_congr Iff.rfl ((keep₁.1 i a ha).symm.trans
            ((keep₂.1 i a ((e₁.1 a).mpr (Or.inl ha))).symm.trans (u.restriction k s v hs code i a hav).symm)))))⟩
      have lift {i j} (edge : It_map_d G i (w 6) j) : It_map_d (U 2) i (w 6) j := by
        obtain ⟨p,pair,entry⟩ := (e₂.2.2.2.1 i (w 6) j hw).mpr edge
        exact ⟨p,pair,u.entry_l hZF hs code 2 entry⟩
      have parent' : Td_parent_d I (g 0) (fun i => w (i.castAdd 47)) a (U 2) row := by
        obtain ⟨j,edge,choice⟩ := parent
        exact ⟨j,lift edge,choice⟩
      exact ⟨l,t,w,ht,ct,rfl,a,row,r,index,
        u.entry_l hZF hs code 5 ((entries (w 12) r).mpr (Or.inr ⟨rfl,rfl⟩)),rc,parent',pred,
        (even _).mpr ⟨w,l,t,ht,ct,u.tree.diagram.order.refl _ state.finite⟩⟩
  · have eq := hZF.1.eq_of_same_members y (v 5) eq
    exact (notEven ((even y).mpr ⟨v,k,s,hs,code,
      eq.symm ▸ u.tree.diagram.order.refl _ (run.read_l hZF hs code).finite⟩)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 偶数枝上的同一控制像

内部全 ω 运行给出共尾偶数枝。各坐标沿真实锥腿成像；十九项控制
在每个后继沿原边保持，故内部归纳证明它们在共同锥中恒定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.node_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {i s} {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Rd_entry_d (v 5) (v 2) (U 1) :=
  u.entry_l hZF hs code 1 (run.read_l hZF hs code).node

theorem Td_run_d.limit_values_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) B (U 1) (U 2) d N W P) (b : Fin 47) :
    ∃ F, Fn0_d (g 0) N F ∧
      ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d (5 : Fin 66) (Fin.natAdd 19 b) H P i x := by
  apply cone.record_values_l hZF (5 : Fin 66) (Fin.natAdd 19 b) run.recursion.1
  · intro i s hs
    obtain ⟨v,code,_⟩ := (run.rows i s hs).1
    exact ⟨v,code⟩
  · intro i s v hs code
    have state := run.read_l hZF hs code
    exact ⟨v 2,v 0,v 1,run.node_l hZF u hs code,state.model,state.issued.1 b,
      (branch _).mpr ⟨v,i,s,hs,code,u.tree.diagram.order.refl _ state.finite⟩⟩

theorem Td_run_d.control_const_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) B (U 1) (U 2) d N W P) (b : Fin 19) :
    ∃ z, M.mem z N ∧
      ∀ i x, Tg_limit_value_d (5 : Fin 66) (Fin.natAdd 19 (b.castAdd 28)) H P i x → x = z := by
  obtain ⟨F,ff,fs⟩ := run.limit_values_l hZF u branch cone (b.castAdd 28)
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : x = y := by
    obtain ⟨v,s,r,hs,ps,hr,hx⟩ := (fs i x).mp hx
    obtain ⟨w,t,l,ht,pt,hl,hy⟩ := (fs j y).mp hy
    obtain ⟨_,_,v',w',ps',pt',next⟩ := run.steps i j s t succ hs ht
    have eq := rt_tuple_inj_l ps' ps
    subst v'
    have eq := rt_tuple_inj_l pt' pt
    subst w'
    obtain ⟨_,_,_,_,_,k,_,_,_,edge,_,images,_⟩ := next.2
    obtain ⟨q,points,head,_⟩ := images
    have edge : It_map_d (U 2) (v 5) (w 5) k := by
      obtain ⟨p,pair,entry⟩ := edge
      exact ⟨p,pair,u.entry_l hZF ht pt 2 entry⟩
    have control : Rd_entry_d (v (Fin.natAdd 19 (b.castAdd 28))) (w (Fin.natAdd 19 (b.castAdd 28))) k := by
      have hb := points (b.castAdd 28)
      rw [← head b] at hb
      exact hb
    have elem := cone.elementary (v 5) r (v 2) (v 0) (v 1) hr
      (run.node_l hZF u hs ps) (run.read_l hZF hs ps).model
    exact elem.1.1.1.2 _ x y hx (cone.commute (v 5) (w 5) k r l edge hr hl _ _ y control hy)
  -- 归纳施于可分离的图像等式，包含模型内部全部自然数。
  let η : Env M 0 := ⟨Fin.elim0,fun _ => F⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  have eqv x y : φ.denote η x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have all := ZF.rel_chain_l I hZF φ η u.tree.omega (fn0_function_l (ZF.modelsKP hZF) ff)
    (fun _ _ _ _ _ _ hx hy => (eqv _ _).mpr (((eqv _ _).mp hx).trans ((eqv _ _).mp hy)))
    (fun i j x y succ hx hy => (eqv _ _).mpr (step i j x y succ hx hy))
  obtain ⟨e,he,heω⟩ := u.tree.omega.1.1
  obtain ⟨z,hz,first⟩ := ff.2.1 e heω
  refine ⟨z,hz,fun i x hx => ?_⟩
  have hx := (fs i x).mpr hx
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare e heω i (ff.bound_l hx).1 with eq | ei | ie
  · have eq := hZF.1.eq_of_same_members e i eq
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i x z hx (eq ▸ first)
  · exact ((eqv z x).mp (all e i z x ei first hx)).symm
  · exact (he i ie).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 回合的历史严格增长

回答先在原历史末尾追加一项，随后实数步和下一请求都保留它。
本证明只读取节点已有的外延性、配对及真实追加证据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_step_d.history_l {g : Fin 10 → M.Domain} {x : M.Domain}
    {v w : Fin 19 → M.Domain} {a b : Fin 47 → M.Domain}
    (state : Td_state_d hZF g w b) (step : Td_run_step_d hZF g x v w a b) :
    ∃ J z, It_map_d (w 9) (v 5) (w 5) J ∧ Rd_entry_d (a 20) z J ∧ z ≠ b 20 ∧
      Rr_truth_d I (w 0) (w 1) (Formula.subset (.bound 1) .newest)
        (Fin.cases (b 20) (fun _ : Fin 1 => z)) := by
  obtain ⟨_,_,_,_,_,J,_,_,_,edge,_,images,_⟩ := step.2
  obtain ⟨u,points,_,h,t,y,z,_,digit⟩ := images
  -- 配对来自该节点自己的源证书，不假定整个原关系模型满足 KP。
  obtain ⟨Y,S,_,_,_,model,source,_⟩ := (state.tree.sources (w 5) (w 2) state.node).objects
  obtain ⟨eqY,eqS⟩ := smdl_unique_l I model state.model
  subst Y S
  let N := smdl_structure_l I (R := w 1) state.model.2.1
  have ext := source.ext.native_l I state.model.2.1
  let η : Env N 0 := ⟨Fin.elim0,fun _ => ⟨b 0,state.issued.1 0⟩⟩
  have pair := (sc_pair_union_l ext η (source.theory.algebra state.model.2.1 η)).1
  let Jn := kpair_interpretation_l N ext pair
  let q := td_digit_values_d u b h t y z
  let ρ : Env N 11 := ⟨fun i => ⟨q i,digit.1 i⟩,fun _ => ⟨q 0,digit.1 0⟩⟩
  have data : Formula.satisfies ρ td_digit0_m :=
    (rr_truth_native_l I state.model.2.1 td_digit0_m td_digit0_closed_l ρ.bound).mp digit
  simp only [td_digit0_m,Formula.satisfies_conj_iff] at data
  have real := (fseq_end_sat_l Jn ext ρ (.bound 0) (.bound 5) (.bound 4) (.bound 8)).mp data.2.2.2.1
  have request := (fseq_end_sat_l Jn ext ρ (.bound 0) (.bound 6) (.bound 5) (.bound 7)).mp data.2.2.2.2.1
  obtain ⟨c,answer⟩ := data.2.2.2.2.2.2
  have answer := (fseq_end_sat_l Jn ext (ρ.push c) (.bound 1) (.bound 5) (.bound 11) .newest).mp answer
  have tail : N.MemberSubset (ρ.bound 4) (ρ.bound 6) :=
    fun p hp => request.subset_l Jn p (real.subset_l Jn p hp)
  have sub : N.MemberSubset (ρ.bound 10) (ρ.bound 6) :=
    fun p hp => tail p (answer.subset_l Jn p hp)
  have ne : u 20 ≠ b 20 := by
    intro eq
    have eq : ρ.bound 10 = ρ.bound 6 := Subtype.ext eq
    obtain ⟨n,m,last⟩ := answer
    obtain ⟨p,pp,hp⟩ := last.last_value
    have hp' : N.mem p (ρ.bound 10) := eq.symm ▸ tail p hp
    have mm := (last.prefix_sequence.2.2.2 m).mpr ⟨c,p,pp,hp'⟩
    exact last.prefix_sequence.2.1.wellOrder.linear.irrefl m mm mm
  let ξ : Env N 2 := ⟨Fin.cases (ρ.bound 6) (fun _ => ρ.bound 10),fun _ => ρ.bound 6⟩
  have values : (fun i => (ξ.bound i).val) = Fin.cases (b 20) (fun _ : Fin 1 => u 20) :=
    funext (Fin.cases rfl (fun _ => rfl))
  have raw : Rr_truth_d I (w 0) (w 1) (Formula.subset (.bound 1) .newest)
      (Fin.cases (b 20) (fun _ : Fin 1 => u 20)) := by
    rw [← values]
    exact (rr_truth_native_l I state.model.2.1 (Formula.subset (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ξ.bound).mpr
      ((Formula.satisfies_subset_iff (⟨ξ.bound,fun _ => ξ.bound 0⟩ : Env N 2) (.bound 1) .newest).mpr sub)
  exact ⟨J,u 20,edge,points 20,ne,raw⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意实际奇节点之后的相邻奇档案列

从给定枝和给定源行出发取真正树后继。奇节点不属于偶数枝，故每个后继
都由继续回合产生，深度恰增加一，祖先表遵循同一原边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_node_row_d (D k r : M.Domain) : Prop := ∃ m, Rd_entry_d m r D ∧ Rt_coord_d (62 : Fin 73) r k
def td_node_row_m {d} (D k r : Term d) : Formula 1 d := .existsE
  (.conj (rd_entry0_m .newest r.weaken D.weaken) (rt_coord_m (62 : Fin 73) r.weaken k.weaken))
derive_free_closed td_node_row_m

theorem td_node_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D k r : Term d) :
    Formula.satisfies ρ (td_node_row_m D k r) ↔ Td_node_row_d (D.eval ρ) (k.eval ρ) (r.eval ρ) := by
  simp only [td_node_row_m,Td_node_row_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,rt_coord_sat_l hE,Definitional.Term.eval_weaken]
  rfl

structure Td_branch_rows_d (I : kpair_convention_l.Interpretation M) (Ω D T G b start r₀ A J F : M.Domain) : Prop where
  indices : Fn0_d Ω b J
  sequence : Fn0_d Ω A F
  first : ∀ e, (∀ x, ¬ M.mem x e) → Rd_entry_d e r₀ F
  records : ∀ i r, Rd_entry_d i r F → ∃ k, Rd_entry_d i k J ∧ Td_node_row_d D k r
  above : ∀ i k, Rd_entry_d i k J → start = k ∨ M.mem start k
  equations : ∀ i j r s, ∀ v w : Td_archive_row_d M.Domain,
    M.SuccessorOf j i → Rd_entry_d i r F → Rd_entry_d j s F → Rt_tuple_d v.values_d r → Rt_tuple_d w.values_d s →
      ∃ f, It_map_d G v.i w.i f ∧ M.SuccessorOf w.depth v.depth ∧
        (∀ p y, Rd_entry_d p y w.ancestors ↔ Td_depth_next_d Ω v.depth v.ancestors v.enumeration f p y) ∧
        Td_aux_growth_d I w.X w.R f v.v w.v
  first_node : ∀ e, (∀ x, ¬ M.mem x e) → Rd_entry_d e start J
  adjacent : ∀ i j x y, M.SuccessorOf j i → Rd_entry_d i x J → Rd_entry_d j y J → It_pred_d T x y

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.archive_decode_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p : M.Domain} (entry : Rd_entry_d m p (U 5)) : ∃ row : Td_archive_row_d M.Domain, Rt_tuple_d row.values_d p := by
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨v,i,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
  obtain ⟨row,pack,_⟩ := (run.read_l hZF hs code).archive m p ⟨q,pair,hq⟩
  exact ⟨row,pack⟩

theorem Td_run_d.node_row_unique_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {k p q : M.Domain} (left : Td_node_row_d (U 5) k p) (right : Td_node_row_d (U 5) k q) : p = q := by
  obtain ⟨m,hm,cm⟩ := left
  obtain ⟨n,hn,cn⟩ := right
  obtain ⟨v,cv⟩ := run.archive_decode_l hZF u hm
  obtain ⟨w,cw⟩ := run.archive_decode_l hZF u hn
  exact (run.archive_unique_l hZF u v w hm hn cv cw ((cm.read_l v.values_d cv).trans (cn.read_l w.values_d cw).symm)).2

theorem Td_run_d.branch_rows_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b m r₀ : M.Domain} (branch : It_branch_d (g 0) (U 0) b) (base : Td_archive_row_d M.Domain)
    (entry : Rd_entry_d m r₀ (U 5)) (tuple : Rt_tuple_d base.values_d r₀) (member : M.mem base.i b) :
    ∃ A J F, Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b base.i r₀ A J F := by
  have hw := u.tree.omega
  obtain ⟨B,evenBranch,even⟩ := run.even_branch_l hZF u
  have notEven : ¬ M.mem base.i B := fun h => run.archive_not_even_l hZF u base entry tuple ((even _).mp h)
  obtain ⟨e,empty,he⟩ := hw.1.1
  obtain ⟨s₀,_,first⟩ := run.recursion.1.2.1 e he
  obtain ⟨v₀,code₀,state₀⟩ := (run.rows e s₀ first).1
  have outside := run.archive_outside_l hZF u base entry tuple empty first code₀
  have finite := ((run.frames_l hZF).read_l hZF v₀ first code₀).finite
  obtain ⟨J,jf,jzero,adjacent,above⟩ := branch.successor_sequence_l hZF hw u.tree.diagram.order member
  have not_even i k (ik : Rd_entry_d i k J) : ¬ M.mem k B := by
    intro h
    exact notEven (evenBranch.down _ _ (branch.forward_l u.tree.diagram.order member (jf.bound_l ik).2 (above i k ik)) h)
  have birth i k (ik : Rd_entry_d i k J) : Td_birth_d hZF (g 0) H (U 5) (U 0) (U 2) B k := by
    apply run.birth_l hZF u even empty first code₀ (branch.subset _ (jf.bound_l ik).2) ?_ (not_even i k ik)
    intro hk
    rcases above i k ik with eq | lt
    · exact outside (eq.symm ▸ hk)
    · exact outside ((hw.members_areOrdinals (ZF.modelsKP hZF) _ finite).transitive k hk base.i lt)
  let ρ : Env M 2 := ⟨fun i => [U 5,J].get i,fun _ => J⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ k,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,k,⌜(.bound 3 : Term 4)⌝ₛ) ∧
    ⌜td_node_row_m⌝ₚ(⌜(.bound 2 : Term 4)⌝ₛ,k,⌜(.newest : Term 4)⌝ₛ)⟫ }
  have sat i r : φ.denote ρ i r ↔ ∃ k, Rd_entry_d i k J ∧ Td_node_row_d (U 5) k r := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,td_node_row_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total i (hi : M.mem i (g 0)) : ∃ r, φ.denote ρ i r := by
    obtain ⟨k,_,ik⟩ := jf.2.1 i hi
    obtain ⟨n,s,v,_,_,_,_,row,r,eq,entry,tuple,_⟩ := birth i k ik
    exact ⟨r,(sat i r).mpr ⟨k,ik,v 12,entry,row.values_d,tuple,eq⟩⟩
  have unique i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s := by
    obtain ⟨k,ik,kr⟩ := (sat i r).mp hr
    obtain ⟨l,il,ls⟩ := (sat i s).mp hs
    have eq := (fn0_function_l (ZF.modelsKP hZF) jf).1.2 i l k il ik
    exact run.node_row_unique_l hZF u kr (eq ▸ ls)
  obtain ⟨A,range⟩ := ZF.exists_functionalImage hZF φ ρ (g 0) total unique
  obtain ⟨F,ff,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun i _ => unique i)
    (fun i r hi hr => (range r).mpr ⟨i,hi,hr⟩)
  have records i r (ir : Rd_entry_d i r F) := (sat i r).mp ((graph i r).mp ir).2
  refine ⟨A,J,F,jf,fn0_of_function_l (ZF.modelsKP hZF) ff,?_,records,above,?_,jzero,adjacent⟩
  · intro e empty
    exact (graph e r₀).mpr ⟨num_mem_l hZF.1 hw (show Num_d 0 e from empty),
      (sat e r₀).mpr ⟨base.i,jzero e empty,m,entry,base.values_d,tuple,rfl⟩⟩
  · intro i j r s left right succ ir js cr cs
    obtain ⟨x,ix,m,entryL,coordL⟩ := records i r ir
    obtain ⟨y,jy,n,entryR,coordR⟩ := records j s js
    have ex : left.i = x := coordL.read_l left.values_d cr
    have ey : right.i = y := coordR.read_l right.values_d cs
    obtain ⟨a,t,v,ht,cv,yv,k,new,q,newy,entryN,cn,parent,pred,ev⟩ := birth j y jy
    have eq := (run.archive_unique_l hZF u new right entryN entryR cn cs (newy.trans ey.symm)).2
    have en := Td_archive_row_d.eq_l (rt_tuple_inj_l cn (eq.symm ▸ cs))
    subst new
    have ek : k = x := pred.unique_l hZF u.tree.diagram.order (adjacent i j x y succ ix jy) (branch.subset _ (jf.bound_l jy).2)
    obtain ⟨map,edge,choice⟩ := parent
    rcases choice with ⟨reset,_⟩ | ⟨l,p,old,_,oldEntry,co,index,depth,table,growth⟩
    · exact (not_even i x ix (ek ▸ reset.symm ▸ ev)).elim
    · have oldEntry := u.entry_l hZF ht cv 5 oldEntry
      have eo : old.i = left.i := index.trans (ek.trans ex.symm)
      have ep := (run.archive_unique_l hZF u old left oldEntry entryL co cr eo).2
      have eo := Td_archive_row_d.eq_l (rt_tuple_inj_l co (ep.symm ▸ cr))
      subst old
      have edge' : It_map_d (U 2) k y map := yv.symm ▸ edge
      exact ⟨map,index.symm ▸ newy.symm ▸ edge',depth,table,growth⟩

/-- 相邻行列覆盖整个实际奇尾段；不是仅外部标准长度的一个子列。 -/
theorem Td_run_d.branch_range_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b start r₀ A J F m p : M.Domain} (branch : It_branch_d (g 0) (U 0) b) (hs : M.mem start b)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b start r₀ A J F)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d row.values_d p)
    (member : M.mem row.i b) (above : start = row.i ∨ M.mem start row.i) : ∃ i, Rd_entry_d i p F := by
  obtain ⟨i,ir⟩ := branch.successor_range_l hZF u.tree.omega u.tree.diagram.order hs
    rows.indices rows.first_node rows.adjacent row.i member above
  obtain ⟨q,_,iq⟩ := rows.sequence.2.1 i (rows.indices.bound_l ir).1
  obtain ⟨k,ik,n,nq,coord⟩ := rows.records i q iq
  have eq := (fn0_function_l (ZF.modelsKP hZF) rows.indices).1.2 i k row.i ik ir
  have eq := run.node_row_unique_l hZF u (eq ▸ (show Td_node_row_d (U 5) k q from ⟨n,nq,coord⟩))
    ⟨m,entry,row.values_d,code,rfl⟩
  exact ⟨i,eq ▸ iq⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际奇枝逐一达到所有较大的内部深度

以深度为变量作模型内部归纳；相邻节点的深度后继来自真实继续回合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.branch_read_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b start r₀ A J F i s : M.Domain}
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b start r₀ A J F)
    (row : Td_archive_row_d M.Domain) (is : Rd_entry_d i s F) (tuple : Rt_tuple_d row.values_d s) :
    ∃ m, Rd_entry_d m s (U 5) ∧ Rd_entry_d i row.i J ∧ M.mem row.i b ∧
      (start = row.i ∨ M.mem start row.i) ∧ Rd_entry_d row.i row.c (U 1) ∧
      Td_archive_source_d I (g 0) (g 1) (g 3) (g 8) (g 9) (g 6) row := by
  obtain ⟨k,ik,m,entry,coord⟩ := rows.records i s is
  have eq : row.i = k := coord.read_l row.values_d tuple
  exact ⟨m,entry,eq.symm ▸ ik,eq.symm ▸ (rows.indices.bound_l ik).2,
    eq.symm ▸ rows.above i k ik,run.archive_node_l hZF u row entry tuple,
    run.archive_source_l hZF u row entry tuple⟩

theorem Td_run_d.branch_depth_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b r₀ A J F d : M.Domain} (base : Td_archive_row_d M.Domain) (tuple : Rt_tuple_d base.values_d r₀)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b base.i r₀ A J F)
    (hd : M.mem d (g 0)) (above : base.depth = d ∨ M.mem base.depth d) :
    ∃ i s, ∃ row : Td_archive_row_d M.Domain, Rd_entry_d i s F ∧ Rt_tuple_d row.values_d s ∧ row.depth = d := by
  have hw := u.tree.omega
  have decode i r (ir : Rd_entry_d i r F) : ∃ row : Td_archive_row_d M.Domain, Rt_tuple_d row.values_d r := by
    obtain ⟨_,_,m,entry,_⟩ := rows.records i r ir
    exact run.archive_decode_l hZF u entry
  obtain ⟨o,empty,ho⟩ := hw.1.1
  let ρ : Env M 2 := ⟨fun i => [F,base.depth].get i,fun _ => F⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪
    (⌜(.bound 2 : Term 3)⌝ₛ = ⌜(.newest : Term 3)⌝ₛ ∨ ⌜(.bound 2 : Term 3)⌝ₛ ∈ ⌜(.newest : Term 3)⌝ₛ) →
    ∃ i s, ⌜rd_entry0_m⌝ₚ(i,s,⌜(.bound 1 : Term 3)⌝ₛ) ∧ ⌜(rt_coord_m (70 : Fin 73))⌝ₚ(s,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat d : φ.denote ρ d ↔ (base.depth = d ∨ M.mem base.depth d) →
      ∃ i s, Rd_entry_d i s F ∧ Rt_coord_d (70 : Fin 73) s d := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff,rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all : ∀ d, M.mem d (g 0) → (base.depth = d ∨ M.mem base.depth d) →
      ∃ i s, Rd_entry_d i s F ∧ Rt_coord_d (70 : Fin 73) s d := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ (g 0)
      exact ⟨B,fun d => (bs d).trans (and_congr_right fun _ => sat d)⟩
    · intro e he h
      rcases h with eq | mem
      · exact ⟨o,r₀,rows.first o empty,base.values_d,tuple,eq⟩
      · exact (he base.depth mem).elim
    · intro d hd ih d' succ h
      rcases h with eq | mem
      · exact ⟨o,r₀,rows.first o empty,base.values_d,tuple,eq⟩
      · have lower : base.depth = d ∨ M.mem base.depth d :=
          ((succ base.depth).mp mem).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members _ _ eq))
        obtain ⟨i,r,ir,coord⟩ := ih lower
        obtain ⟨left,cl⟩ := decode i r ir
        have ed : left.depth = d := coord.read_l left.values_d cl
        obtain ⟨j,step,hj⟩ := hw.1.2 i (rows.sequence.bound_l ir).1
        obtain ⟨s,_,js⟩ := rows.sequence.2.1 j hj
        obtain ⟨right,cr⟩ := decode j s js
        obtain ⟨_,_,depth,_⟩ := rows.equations i j r s left right step ir js cl cr
        have depth : M.SuccessorOf right.depth d := ed ▸ depth
        exact ⟨j,s,js,right.values_d,cr,depth.eq hZF.1 succ⟩
  obtain ⟨i,s,is,coord⟩ := all d hd above
  obtain ⟨row,pack⟩ := decode i s is
  exact ⟨i,s,row,is,pack,coord.read_l row.values_d pack⟩

end YesMetaZFC.SetTheory.LargeCardinal
