import YesMetaZFC.SetTheory.LargeCardinal.Game.RunMove
import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.Model.SetTheory.ClassResponse
import YesMetaZFC.SetTheory.Descriptive.Demand.InputIteration

/-! # 所有原实局共用的实际后继函数

原树名称与全部递归不变量一起进入反射闭包。选择只执行一次，
输入为当前状态和一个字母；以后有限前缀递归不再调用选择公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
section State
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_run_choice_d (ω c o C γ Z A S r X D K : M.Domain) : Prop where
  initial : Tg_run_code_d hZF ω c o C γ Z A o r
  name : Tg_run_name_d S r
  member : M.mem r X
  product : M.IsCartesianProduct I D X A
  function : Fn0_d D X K
  step : ∀ n s x t p, Tg_run_code_d hZF ω c o C γ Z A n s → Tg_run_name_d S s →
    (I).Codes p s x → Rd_entry_d p t K → ∃ m, M.SuccessorOf m n ∧
      Tg_run_code_d hZF ω c o C γ Z A m t ∧ Tg_run_name_d S t ∧
      Tg_run_edge_d hZF ω c s t ∧ Tg_run_move_d hZF ω A n m s t x

end State

section Choice
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_code_d.choice_l {ω c o C γ Z A S r : M.Domain}
    (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o) (hγ : M.IsLimitOrdinal γ)
    (hωZ : M.mem ω Z) (hAZ : M.mem A Z)
    (initial : Tg_run_code_d hZF ω c o C γ Z A o r) (name : Tg_run_name_d S r) :
    ∃ X D K, Tg_run_choice_d hZF ω c o C γ Z A S r X D K := by
  let ρ : Env M 8 := ⟨fun i => [ω,c,o,C,γ,Z,A,S].get i,fun _ => ω⟩
  let V : UnarySchema 8 := { body := set[9] ⟪∃ n,
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ,⌜(.bound 2 : Term 9)⌝ₛ,⌜(.bound 3 : Term 9)⌝ₛ,
      ⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ,⌜(.bound 6 : Term 9)⌝ₛ,⌜(.bound 7 : Term 9)⌝ₛ,n,⌜(.newest : Term 9)⌝ₛ) ∧
    ⌜tg_run_name_m⌝ₚ(⌜(.bound 8 : Term 9)⌝ₛ,⌜(.newest : Term 9)⌝ₛ)⟫ }
  have valid s : V.denote ρ s ↔ ∃ n, Tg_run_code_d hZF ω c o C γ Z A n s ∧ Tg_run_name_d S s := by
    simp only [V,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      tg_run_code_sat_l hZF,tg_run_name_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  let φ : UnarySchema 10 := { body := set[11] ⟪∃ n m,
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,
      ⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 7 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,n,⌜(.bound 2 : Term 11)⌝ₛ) ∧
    ⌜KP.succ0_m⌝ₚ(m,n) ∧
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,
      ⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 7 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,m,⌜(.newest : Term 11)⌝ₛ) ∧
    ⌜tg_run_edge_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 2 : Term 11)⌝ₛ,⌜(.newest : Term 11)⌝ₛ) ∧
    ⌜tg_run_move_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,n,m,
      ⌜(.bound 2 : Term 11)⌝ₛ,⌜(.newest : Term 11)⌝ₛ,⌜(.bound 1 : Term 11)⌝ₛ)⟫ }
  have action s x t : φ.denote ((ρ.push s).push x) t ↔ ∃ n m,
      Tg_run_code_d hZF ω c o C γ Z A n s ∧ M.SuccessorOf m n ∧
      Tg_run_code_d hZF ω c o C γ Z A m t ∧ Tg_run_edge_d hZF ω c s t ∧ Tg_run_move_d hZF ω A n m s t x := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      tg_run_code_sat_l hZF,KP.succ0_sat_l hZF.1,tg_run_edge_sat_l hZF,tg_run_move_sat_l hZF,Definitional.Term.eval_weaken]; rfl
  obtain ⟨X,D,K,mem,prod,fn,steps⟩ := ZFC.class_response_l I hZFC V φ ρ (a := r) hw (by
    intro s x hs hx
    obtain ⟨n,run,name⟩ := (valid s).mp hs
    obtain ⟨m,t,succ,next,edge,move⟩ := run.advance_l hZFC ho hγ hωZ hAZ hx
    exact ⟨t,(valid t).mpr ⟨m,next,edge.name_l hZF run next name⟩,(action s x t).mpr ⟨n,m,run,succ,next,edge,move⟩⟩)
  refine ⟨X,D,K,⟨initial,name,mem,prod,fn0_of_function_l (ZF.modelsKP hZF) fn,?_⟩⟩
  intro n s x t p run name pair entry
  obtain ⟨vt,act⟩ := steps s x t p pair entry ((valid s).mpr ⟨n,run,name⟩)
  obtain ⟨k,m,old,succ,next,edge,move⟩ := (action s x t).mp act
  obtain ⟨v,code,_,eq⟩ := old
  obtain ⟨w,pack,_,eq'⟩ := run
  have kn : k = n := eq.symm.trans ((congrFun (rt_tuple_inj_l code pack) 37).trans eq')
  exact ⟨m,kn ▸ succ,next,((valid t).mp vt).choose_spec.2,edge,kn ▸ move⟩

end Choice
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从统一响应表构造原博弈的实际策略

有限局面先确定当前递归状态，再以固定字母查询下一状态并读取最后一字母。
此定义只量化已经实现的内部递归；状态和输出的唯一性均由原函数图证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_choice_d.valid_l {ω c o C γ Z A S r X D K a f H : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (run : Gi_d hZF true ω X K r a f H) : ∀ n u, Rd_entry_d n u H →
      Tg_run_code_d hZF ω c o C γ Z A n u ∧ Tg_run_name_d S u := by
  let ρ : Env M 9 := ⟨fun i => [ω,c,o,C,γ,Z,A,S,H].get i,fun _ => ω⟩
  let φ : UnarySchema 9 := { body := set[10] ⟪∀ u,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 10)⌝ₛ,u,⌜(.bound 9 : Term 10)⌝ₛ) →
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 1 : Term 10)⌝ₛ,⌜(.bound 2 : Term 10)⌝ₛ,⌜(.bound 3 : Term 10)⌝ₛ,
      ⌜(.bound 4 : Term 10)⌝ₛ,⌜(.bound 5 : Term 10)⌝ₛ,⌜(.bound 6 : Term 10)⌝ₛ,⌜(.bound 7 : Term 10)⌝ₛ,
      ⌜(.newest : Term 10)⌝ₛ,u) ∧ ⌜tg_run_name_m⌝ₚ(⌜(.bound 8 : Term 10)⌝ₛ,u)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ u, Rd_entry_d n u H → Tg_run_code_d hZF ω c o C γ Z A n u ∧ Tg_run_name_d S u := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hZF.1,
      Formula.satisfies_conj_iff,tg_run_code_sat_l hZF,tg_run_name_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ u, Rd_entry_d n u H → Tg_run_code_d hZF ω c o C γ Z A n u ∧ Tg_run_name_d S u := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz u hu
      have zo := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (ho x))
      have ur := (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 z u r hu (run.2.1 z hz)
      exact ur.symm ▸ zo.symm ▸ ⟨h.initial,h.name⟩
    · intro i hi ih j succ t ht
      obtain ⟨s,_,hs⟩ := run.1.2.1 i hi
      obtain ⟨x,p,_,pair,entry⟩ := run.2.2 i j s t succ hs ht
      obtain ⟨m,ms,next,name,_,_⟩ := h.step i s x t p (ih s hs).1 (ih s hs).2 pair entry
      exact ms.eq hZF.1 succ ▸ ⟨next,name⟩
  exact fun n u hu => all n (run.1.bound_l hu).1 u hu

def Tg_response_d (ω A X K r a s y : M.Domain) : Prop := ∃ n H u p t m q,
  M.IsDomainOf I n s ∧ Gi_d hZF true ω X K r a s H ∧ Rd_entry_d n u H ∧
    (I).Codes p u a ∧ Rd_entry_d p t K ∧ M.SuccessorOf m n ∧ Tg_run_real_d I A m t q ∧ Rd_entry_d n y q
def tg_response_m {d} (ω A X K r a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H u p t m q,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n,⌜s⌝ₛ) ∧ ⌜gi_m true⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜s⌝ₛ,H) ∧
  ⌜rd_entry0_m⌝ₚ(n,u,H) ∧ ⌜kpair_m⌝ₚ(p,u,⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ) ∧
  ⌜KP.succ0_m⌝ₚ(m,n) ∧ ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,m,t,q) ∧ ⌜rd_entry0_m⌝ₚ(n,⌜y⌝ₛ,q)⟫
derive_free_closed tg_response_m
theorem tg_response_sat_l {d} (ρ : Env M d) (ω A X K r a s y : Term d) : Formula.satisfies ρ (tg_response_m ω A X K r a s y) ↔
    Tg_response_d hZF (ω.eval ρ) (A.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [tg_response_m,Tg_response_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I,gi_sat_l hZF true,rd_entry0_sat_l hZF.1,kpair_sat_l M hZF.1,KP.succ0_sat_l hZF.1,
    tg_run_real_sat_l I hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_choice_d.response_l {ω c o C γ Z A S r X D K a s n : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) : ∃ y, Tg_response_d hZF ω A X K r a s y := by
  obtain ⟨H,run⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha fs.1 (fun _ _ hx => fs.output_mem_of_pairMember hx)
  obtain ⟨u,hu,nu⟩ := run.1.2.1 n hn
  obtain ⟨p,pair⟩ := (I).total u a
  obtain ⟨t,_,pt⟩ := h.function.2.1 p ((h.product p).mpr ⟨u,hu,a,ha,pair⟩)
  have valid := h.valid_l hZF hw ho run n u nu
  obtain ⟨m,succ,_,_,_,move⟩ := h.step n u a t p valid.1 valid.2 pair pt
  obtain ⟨_,q,y,_,real,_,last,_⟩ := move.last_l hZF
  exact ⟨y,n,H,u,p,t,m,q,fs.2.1,run,nu,pair,pt,succ,real,last⟩

theorem Tg_run_choice_d.response_unique_l {ω c o C γ Z A S r X D K a s x y : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (fs : M.IsSetFunction I s) (hx : Tg_response_d hZF ω A X K r a s x) (hy : Tg_response_d hZF ω A X K r a s y) : x = y := by
  obtain ⟨n,H,u,p,t,m,q,dom,run,nu,pair,pt,succ,real,last⟩ := hx
  obtain ⟨n',H',u',p',t',m',q',dom',run',nu',pair',pt',succ',real',last'⟩ := hy
  have eq := dom'.eq hZF.1 dom
  subst n'
  have uu := run.agree_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1 fs run'
    (run.1.bound_l nu).1 (fun _ _ _ => Iff.rfl) u u' nu nu'
  have pp := (I).unique pair (uu.symm ▸ pair')
  have tt := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 p t t' pt (pp.symm ▸ pt')
  have mm := succ'.eq hZF.1 succ
  have valid := h.valid_l hZF hw ho run n u nu
  obtain ⟨l,ls,next,_,_,_⟩ := h.step n u a t p valid.1 valid.2 pair pt
  have next := ls.eq hZF.1 succ ▸ next
  have qq := next.real_unique_l hZF real (tt.symm ▸ mm ▸ real')
  exact (fn0_function_l (ZF.modelsKP hZF) (real.function_l I)).1.2 n x y last (qq.symm ▸ last')

theorem Tg_run_choice_d.strategy_l {ω c o C γ Z A S r X D K a F : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) : ∃ σ, Fn0_d F A σ ∧
      ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_response_d hZF ω A X K r a s y := by
  let ρ : Env M 6 := ⟨fun i => [ω,A,X,K,r,a].get i,fun _ => ω⟩
  let φ : BinarySchema 6 := { body := tg_response_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 1) .newest }
  have sat s y : φ.denote ρ s y ↔ Tg_response_d hZF ω A X K r a s y := tg_response_sat_l hZF ..
  obtain ⟨σ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := A) (by
    intro s hs
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨y,hy⟩ := h.response_l hZF hw ho ha hn fs
    exact ⟨y,(sat s y).mpr hy⟩) (by
    intro s hs x y hx hy
    obtain ⟨_,_,fs⟩ := (space s).mp hs
    exact h.response_unique_l hZF hw ho fs.1 ((sat s x).mp hx) ((sat s y).mp hy)) (by
    intro s y _ hy
    obtain ⟨n,_,_,_,_,_,q,_,_,_,_,_,_,real,last⟩ := (sat s y).mp hy
    exact ((real.function_l I).bound_l last).2)
  exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun s y => (values s y).trans (and_congr_right fun _ => sat s y)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 服从所构造策略的任意原对局与递归前缀逐轮一致 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_choice_d.play_l {ω c o C γ Z A S r X D K a F σ f H : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_response_d hZF ω A X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f) (run : Gi_d hZF true ω X K r a f H) :
    ∀ n u s, Rd_entry_d n u H → Tg_run_real_d I A n u s → M.IsRestrictionOf I s f n := by
  classical
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  let ρ : Env M 3 := ⟨fun i => [A,H,f].get i,fun _ => A⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∀ u s,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,u,⌜(.bound 2 : Term 4)⌝ₛ) →
    ⌜tg_run_real_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ,u,s) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(s,⌜(.bound 3 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ u s, Rd_entry_d n u H → Tg_run_real_d I A n u s → M.IsRestrictionOf I s f n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hZF.1,
      tg_run_real_sat_l I hZF.1,Formula.satisfies_isRestriction_iff I,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ u s, Rd_entry_d n u H → Tg_run_real_d I A n u s → M.IsRestrictionOf I s f n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz u s _ real
      exact ⟨(fn0_function_l (ZF.modelsKP hZF) (real.function_l I)).1.1,fun i y =>
        ⟨fun hi => (hz i ((real.function_l I).bound_l hi).1).elim,fun hi => (hz i hi.1).elim⟩⟩
    · intro n hn ih m succ t q mt real
      obtain ⟨u,_,nu⟩ := run.1.2.1 n hn
      have valid := h.valid_l hZF hw ho run n u nu
      obtain ⟨x,p,inp,pair,pt⟩ := run.2.2 n m u t succ nu mt
      obtain ⟨m',succ',next,_,_,move⟩ := h.step n u x t p valid.1 valid.2 pair pt
      have mm := succ'.eq hZF.1 succ
      have next := mm ▸ next
      obtain ⟨s,q',y,old,new,endt,last,even⟩ := (show Tg_run_move_d hZF ω A n m u t x from mm ▸ move).last_l hZF
      have qq := next.real_unique_l hZF new real
      subst q'
      have cut := ih u s nu old
      have fs := fn0_function_l (ZF.modelsKP hZF) (old.function_l I)
      obtain ⟨z,_,nz⟩ := ff.2.1 n hn
      have yz : y = z := by
        by_cases he : Gm_even_d I ω n
        · exact (even he).trans (inp.elim (fun hx => fn.1.2 n x z hx.2 nz) (fun hx => (hx.1 ⟨he,z,nz⟩).elim))
        · have xa : x = a := inp.elim (fun hx => (he hx.1).elim) And.right
          obtain ⟨G,grun⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha fs.1 (fun _ _ hs => fs.output_mem_of_pairMember hs)
          obtain ⟨u',_,nu'⟩ := grun.1.2.1 n hn
          have uu := run.prefix_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1 fn.1 grun hn cut u u' nu nu'
          have response : Tg_response_d hZF ω A X K r a s y :=
            ⟨n,G,u,p,t,m,q,fs.2.1,grun,uu.symm ▸ nu',xa ▸ pair,pt,succ,real,last⟩
          have sy := (values s y).mpr ⟨(space s).mpr ⟨n,hn,fs⟩,response⟩
          exact (fn0_function_l (ZF.modelsKP hZF) sf).1.2 s y z sy (follows n hn he s cut z nz)
      have fq := fn0_function_l (ZF.modelsKP hZF) (real.function_l I)
      apply (ds_restrict_iff_l I fq fn.1).mpr
      intro p hp
      obtain ⟨i,v,pair⟩ := fq.1.1 p hp
      have iv : Rd_entry_d i v q := ⟨p,pair,hp⟩
      have entry : Rd_entry_d i v f := by
        rcases (succ i).mp (fq.input_mem_of_pairMember iv) with hi | eq
        · obtain ⟨l,k,d⟩ := endt
          have kn := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
          exact ((cut.2 i v).mp ((d.prefix_restriction.2 i v).mpr ⟨kn.symm ▸ hi,iv⟩)).2
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          exact (fq.1.2 n v y iv last).symm ▸ yz.symm ▸ nz
      obtain ⟨p',pair',hp'⟩ := entry
      exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  exact fun n u s nu real => all n (run.1.bound_l nu).1 u s nu real

theorem Tg_run_choice_d.sequence_l {ω c o C γ Z A S r X D K a F σ f : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_response_d hZF ω A X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f) : ∃ H,
      Tg_sequence_d hZF ω c o C γ Z A X H ∧ (∀ i u, Rd_entry_d i u H → Tg_run_name_d S u) ∧
      ∀ i u, Rd_entry_d i u H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d I A n u s ∧ M.IsRestrictionOf I s f n := by
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  obtain ⟨G,run⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha fn.1 (fun _ _ hi => fn.output_mem_of_pairMember hi)
  let ρ : Env M 1 := ⟨fun _ => G,fun _ => G⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ n, ⌜KP.succ0_m⌝ₚ(n,⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(n,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat i u : φ.denote ρ i u ↔ ∃ n, M.SuccessorOf n i ∧ Rd_entry_d n u G := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      KP.succ0_sat_l hZF.1,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  obtain ⟨H,hf,hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro i hi
    obtain ⟨n,succ,hn⟩ := hw.1.2 i hi
    obtain ⟨u,_,nu⟩ := run.1.2.1 n hn
    exact ⟨u,(sat i u).mpr ⟨n,succ,nu⟩⟩) (by
    intro i _ u v hu hv
    obtain ⟨n,ni,nu⟩ := (sat i u).mp hu
    obtain ⟨m,mi,mv⟩ := (sat i v).mp hv
    exact (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 n u v nu ((mi.eq hZF.1 ni) ▸ mv)) (by
    intro i u _ hu
    obtain ⟨n,_,nu⟩ := (sat i u).mp hu
    exact (run.1.bound_l nu).2)
  have read i u (hu : Rd_entry_d i u H) := (sat i u).mp ((hs i u).mp hu).2
  refine ⟨H,⟨fn0_of_function_l (ZF.modelsKP hZF) hf,?_,?_⟩,?_,?_⟩
  · intro i u hu
    obtain ⟨n,ni,nu⟩ := read i u hu
    exact ⟨n,ni,(h.valid_l hZF hw ho run n u nu).1⟩
  · intro i j u v succ hu hv
    obtain ⟨n,ni,nu⟩ := read i u hu
    obtain ⟨m,mj,mv⟩ := read j v hv
    have nj := ni.eq hZF.1 succ
    obtain ⟨x,p,_,pair,pv⟩ := run.2.2 n m u v (nj.symm ▸ mj) nu mv
    have valid := h.valid_l hZF hw ho run n u nu
    exact (h.step n u x v p valid.1 valid.2 pair pv).choose_spec.2.2.2.1
  · intro i u hu
    obtain ⟨n,_,nu⟩ := read i u hu
    exact (h.valid_l hZF hw ho run n u nu).2
  · intro i u hu
    obtain ⟨n,ni,nu⟩ := read i u hu
    obtain ⟨s,real⟩ := (h.valid_l hZF hw ho run n u nu).1.real_l hZF
    exact ⟨n,s,ni,real,h.play_l hZF hw ho ha space sf values ff follows run n u s nu real⟩

end YesMetaZFC.SetTheory.LargeCardinal
