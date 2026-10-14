import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunChoice
import YesMetaZFC.SetTheory.Descriptive.InputIteration

/-! # 从统一响应表构造原博弈的实际策略

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
    (run : Gi_d hZF ω X K r a f H) : ∀ n u, Rd_entry_d n u H →
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
  M.IsDomainOf I n s ∧ Gi_d hZF ω X K r a s H ∧ Rd_entry_d n u H ∧
    (I).Codes p u a ∧ Rd_entry_d p t K ∧ M.SuccessorOf m n ∧ Tg_run_real_d A m t q ∧ Rd_entry_d n y q
def tg_response_m {d} (ω A X K r a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H u p t m q,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n,⌜s⌝ₛ) ∧ ⌜gi_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜s⌝ₛ,H) ∧
  ⌜rd_entry0_m⌝ₚ(n,u,H) ∧ ⌜kpair_m⌝ₚ(p,u,⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ) ∧
  ⌜KP.succ0_m⌝ₚ(m,n) ∧ ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,m,t,q) ∧ ⌜rd_entry0_m⌝ₚ(n,⌜y⌝ₛ,q)⟫
derive_free_closed tg_response_m
theorem tg_response_sat_l {d} (ρ : Env M d) (ω A X K r a s y : Term d) : Formula.satisfies ρ (tg_response_m ω A X K r a s y) ↔
    Tg_response_d hZF (ω.eval ρ) (A.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [tg_response_m,Tg_response_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I,gi_sat_l hZF,rd_entry0_sat_l hZF.1,kpair_sat_l M hZF.1,KP.succ0_sat_l hZF.1,
    tg_run_real_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_choice_d.response_l {ω c o C γ Z A S r X D K a s n : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) : ∃ y, Tg_response_d hZF ω A X K r a s y := by
  obtain ⟨H,run⟩ := gi_exists_l hZF hw h.product h.function h.member ha fs.1 (fun _ _ hx => fs.output_mem_of_pairMember hx)
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
  exact (fn0_function_l (ZF.modelsKP hZF) real.function_l).1.2 n x y last (qq.symm ▸ last')

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
    exact (real.function_l.bound_l last).2)
  exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun s y => (values s y).trans (and_congr_right fun _ => sat s y)⟩

end YesMetaZFC.SetTheory.LargeCardinal
