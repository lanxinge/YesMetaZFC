import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Descriptive.Game.GameStrategyProjection
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 全部输入字母驱动的内部历史递归

固定状态转移表逐个读取实际输入；同一有限前缀给出同一当前状态。
所有递归和归纳都在背景模型的内部 ω 上进行。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Hr_run_d (ω X K r f H : M.Domain) : Prop := Fn0_d ω X H ∧
  (∀ o, (∀ z, ¬ M.mem z o) → Rd_entry_d o r H) ∧
  ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
    ∃ x p, Rd_entry_d i x f ∧ (I).Codes p s x ∧ Rd_entry_d p t K
def hr_run_m {d} (ω X K r f H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜H⌝ₛ) ∧ (∀ o, (∀ z, ¬ z ∈ o) → ⌜rd_entry0_m⌝ₚ(o,⌜r⌝ₛ,⌜H⌝ₛ)) ∧
  (∀ i j s t, ⌜KP.succ0_m⌝ₚ(j,i) → ⌜rd_entry0_m⌝ₚ(i,s,⌜H⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j,t,⌜H⌝ₛ) →
    ∃ x p, ⌜rd_entry0_m⌝ₚ(i,x,⌜f⌝ₛ) ∧ ⌜kpair_m⌝ₚ(p,s,x) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ))⟫
derive_free_closed hr_run_m
theorem hr_run_sat_l {d} (ρ : Env M d) (ω X K r f H : Term d) : Formula.satisfies ρ (hr_run_m ω X K r f H) ↔
    Hr_run_d hZF (ω.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (f.eval ρ) (H.eval ρ) := by
  simp only [hr_run_m,Hr_run_d,Formula.satisfies_conj_iff,fn0_sat_l hZF.1,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,rd_entry0_sat_l hZF.1,
    KP.succ0_sat_l hZF.1,Formula.satisfies_exists_iff,kpair_sat_l M hZF.1,
    Definitional.Term.eval_weaken]; rfl

theorem hr_run_exists_l {ω A X D K r f : M.Domain} (hw : M.IsOmega ω)
    (prod : M.IsCartesianProduct I D X A) (fn : Fn0_d D X K) (hr : M.mem r X) (ff : Fn0_d ω A f) : ∃ H, Hr_run_d hZF ω X K r f H := by
  obtain ⟨E,ep⟩ := ZF.exists_cartesianProduct hZF I ω X
  let ρ : Env M 2 := ⟨fun i => [f,K].get i,fun _ => f⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ i s x p,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,i,s) ∧
    ⌜rd_entry0_m⌝ₚ(i,x,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜kpair_m⌝ₚ(p,s,x) ∧ ⌜rd_entry0_m⌝ₚ(p,⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat q t : φ.denote ρ q t ↔ ∃ i s x p, (I).Codes q i s ∧ Rd_entry_d i x f ∧
      (I).Codes p s x ∧ Rd_entry_d p t K := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have fk := fn0_function_l (ZF.modelsKP hZF) fn
  obtain ⟨L,lf,ls⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := E) (target := X) (by
    intro q hq
    obtain ⟨i,hi,s,hs,pair⟩ := (ep q).mp hq
    obtain ⟨x,hx,inp⟩ := ff.2.1 i hi
    obtain ⟨p,px⟩ := (I).total s x
    obtain ⟨t,_,ht⟩ := fn.2.1 p ((prod p).mpr ⟨s,hs,x,hx,px⟩)
    exact ⟨t,(sat q t).mpr ⟨i,s,x,p,pair,inp,px,ht⟩⟩) (by
    intro q _ t u ht hu
    obtain ⟨i,s,x,p,pair,inp,px,ht⟩ := (sat q t).mp ht
    obtain ⟨j,z,y,q',pair',inp',py,hu⟩ := (sat q u).mp hu
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    have xy := (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i x y inp inp'
    have pq := (I).unique px (xy.symm ▸ py)
    exact fk.1.2 p t u ht (pq.symm ▸ hu)) (by
    intro q t _ ht
    obtain ⟨_,_,_,p,_,_,_,ht⟩ := (sat q t).mp ht
    exact (fn.bound_l ht).2)
  obtain ⟨H,hf,hz,steps⟩ := ZF.indexed_iteration_l I hZF hw ep lf hr
  refine ⟨H,fn0_of_function_l (ZF.modelsKP hZF) hf,hz,fun i j s t succ hs ht => ?_⟩
  obtain ⟨q,pair,qt⟩ := steps i j s t succ hs ht
  obtain ⟨i',s',x,p,pair',inp,px,pt⟩ := (sat q t).mp ((ls q t).mp qt).2
  obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
  exact ⟨x,p,inp,px,pt⟩

theorem Hr_run_d.agree_l {ω X K r f g H G n : M.Domain} (hw : M.IsOmega ω)
    (kf : M.IsSetFunction I K) (ff : M.IsSetFunction I f) (h : Hr_run_d hZF ω X K r f H)
    (g' : Hr_run_d hZF ω X K r g G) (hn : M.mem n ω)
    (same : ∀ i, M.mem i n → ∀ x, Rd_entry_d i x f ↔ Rd_entry_d i x g) :
    ∀ s t, Rd_entry_d n s H → Rd_entry_d n t G → s = t := by
  let ρ : Env M 3 := ⟨fun i => [n,H,G].get i,fun _ => n⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪(⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ ∨
    ⌜(.newest : Term 4)⌝ₛ = ⌜(.bound 1 : Term 4)⌝ₛ) → ∀ s t,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,s,⌜(.bound 2 : Term 4)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,t,⌜(.bound 3 : Term 4)⌝ₛ) → s = t⟫ }
  have sat i : φ.denote ρ i ↔ (M.mem i n ∨ i = n) → ∀ s t, Rd_entry_d i s H → Rd_entry_d i t G → s = t := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_forall_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have hf := fn0_function_l (ZF.modelsKP hZF) h.1
  have gf := fn0_function_l (ZF.modelsKP hZF) g'.1
  have all : ∀ i, M.mem i ω → (M.mem i n ∨ i = n) → ∀ s t, Rd_entry_d i s H → Rd_entry_d i t G → s = t := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun i => (bs i).trans (and_congr_right fun _ => sat i)⟩
    · intro o ho _ s t hs ht
      exact (hf.1.2 o s r hs (h.2.1 o ho)).trans (gf.1.2 o r t (g'.2.1 o ho) ht)
    · intro i hi ih j succ bound s t hs ht
      have hin : M.mem i n := bound.elim (fun hj => (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive j hj i succ.predecessor_mem)
        (fun eq => eq ▸ succ.predecessor_mem)
      obtain ⟨u,_,hu⟩ := h.1.2.1 i hi
      obtain ⟨v,_,hv⟩ := g'.1.2.1 i hi
      obtain ⟨x,p,inp,pair,pt⟩ := h.2.2 i j u s succ hu hs
      obtain ⟨y,q,inp',pair',qt⟩ := g'.2.2 i j v t succ hv ht
      have xy := ff.2 i x y inp ((same i hin y).mpr inp')
      have pq := (I).unique pair ((ih (Or.inl hin) u v hu hv).symm ▸ xy.symm ▸ pair')
      exact kf.2 p s t pt (pq.symm ▸ qt)
  exact all n hn (Or.inr rfl)

theorem Hr_run_d.prefix_l {ω X K r f g H G n : M.Domain} (hw : M.IsOmega ω)
    (kf : M.IsSetFunction I K) (ff : M.IsSetFunction I f) (h : Hr_run_d hZF ω X K r f H)
    (g' : Hr_run_d hZF ω X K r g G) (hn : M.mem n ω) (cut : M.IsRestrictionOf I g f n) :
    ∀ s t, Rd_entry_d n s H → Rd_entry_d n t G → s = t := by
  apply h.agree_l hZF hw kf ff g' hn
  intro i hi x
  have ent y : Rd_entry_d i y g ↔ Rd_entry_d i y f := (cut.2 i y).trans (and_iff_right hi)
  exact (ent x).symm

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限输入上的确定求值表

有限列任取常值尾延拓，运行至其长度。前缀因果性证明结果不依赖尾部，
替换于是收集整张内部有限历史函数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Hr_eval_d (ω A Q K r s t : M.Domain) : Prop := ∃ n f H,
  M.mem n ω ∧ Fn0_d ω A f ∧ M.IsRestrictionOf I s f n ∧
    Hr_run_d hZF ω Q K r f H ∧ Rd_entry_d n t H

def hr_eval_m {d} (ω A Q K r s t : Term d) : Formula 1 d := set[d] ⟪∃ n f H,
  n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,f) ∧
  ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜s⌝ₛ,f,n) ∧
  ⌜hr_run_m⌝ₚ(⌜ω⌝ₛ,⌜Q⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,f,H) ∧ ⌜rd_entry0_m⌝ₚ(n,⌜t⌝ₛ,H)⟫
derive_free_closed hr_eval_m

theorem hr_eval_sat_l {d} (ρ : Env M d) (ω A Q K r s t : Term d) :
    Formula.satisfies ρ (hr_eval_m ω A Q K r s t) ↔
      Hr_eval_d hZF (ω.eval ρ) (A.eval ρ) (Q.eval ρ) (K.eval ρ) (r.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [hr_eval_m,Hr_eval_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hZF.1,Formula.satisfies_isRestriction_iff I,
    hr_run_sat_l hZF,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

variable {ω A Q K r s t : M.Domain}

theorem Hr_eval_d.unique_l (hw : M.IsOmega ω) (fk : M.IsSetFunction I K)
    {u : M.Domain} (h : Hr_eval_d hZF ω A Q K r s t) (h' : Hr_eval_d hZF ω A Q K r s u) : t = u := by
  obtain ⟨n,f,H,hn,ff,cut,run,nt⟩ := h
  obtain ⟨m,g,G,hm,fg,cut',run',mu⟩ := h'
  have fs := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ff) (hw.transitive (ZF.modelsKP hZF) n hn)
  have gs := cut'.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fg) (hw.transitive (ZF.modelsKP hZF) m hm)
  have eq := gs.2.1.eq hZF.1 fs.2.1
  subst m
  exact run.agree_l hZF hw fk (fn0_function_l (ZF.modelsKP hZF) ff).1 run' hn
    (fun i hi x => ((cut.2 i x).trans (and_iff_right hi)).symm.trans
      ((cut'.2 i x).trans (and_iff_right hi))) t u nt mu

theorem hr_eval_table_l {F D a : M.Domain} (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    (product : M.IsCartesianProduct I D Q A) (fn : Fn0_d D Q K) (initial : M.mem r Q) (ha : M.mem a A) :
    ∃ π, Fn0_d F Q π ∧ ∀ s t, Rd_entry_d s t π ↔ M.mem s F ∧ Hr_eval_d hZF ω A Q K r s t := by
  let ρ : Env M 5 := ⟨fun i => [ω,A,Q,K,r].get i,fun _ => ω⟩
  let φ : BinarySchema 5 := { body := (hr_eval_m (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 1) .newest) }
  have sat s t : φ.denote ρ s t ↔ Hr_eval_d hZF ω A Q K r s t := hr_eval_sat_l hZF ..
  obtain ⟨π,ff,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := Q) (by
    intro s hs
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨f,ff,cut,_⟩ := ds_extend_l I hZF hw hn fs ha
    obtain ⟨H,run⟩ := hr_run_exists_l hZF hw product fn initial (fn0_of_function_l (ZF.modelsKP hZF) ff)
    obtain ⟨t,_,nt⟩ := run.1.2.1 n hn
    exact ⟨t,(sat s t).mpr ⟨n,f,H,hn,fn0_of_function_l (ZF.modelsKP hZF) ff,cut,run,nt⟩⟩) (by
    intro s _ x y hx hy
    exact Hr_eval_d.unique_l hZF hw (fn0_function_l (ZF.modelsKP hZF) fn).1 ((sat s x).mp hx) ((sat s y).mp hy)) (by
    intro s t _ ht
    obtain ⟨_,_,_,_,_,_,run,nt⟩ := (sat s t).mp ht
    exact (run.1.bound_l nt).2)
  exact ⟨π,fn0_of_function_l (ZF.modelsKP hZF) ff,fun s t =>
    (values s t).trans (and_congr_right fun _ => sat s t)⟩

/-- 已知某次完整运行时，有限求值就是其在该长度的状态。 -/
theorem Hr_eval_d.read_l {f H n : M.Domain} (hw : M.IsOmega ω) (fk : M.IsSetFunction I K)
    (ff : Fn0_d ω A f) (run : Hr_run_d hZF ω Q K r f H) (hn : M.mem n ω)
    (cut : M.IsRestrictionOf I s f n) (h : Hr_eval_d hZF ω A Q K r s t) : Rd_entry_d n t H := by
  obtain ⟨u,_,nu⟩ := run.1.2.1 n hn
  exact (Hr_eval_d.unique_l hZF hw fk ⟨n,f,H,hn,ff,cut,run,nu⟩ h) ▸ nu

theorem Hr_eval_d.zero_l (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x s)
    (h : Hr_eval_d hZF ω A Q K r s t) : t = r := by
  obtain ⟨n,f,H,hn,ff,cut,run,nt⟩ := h
  have fs := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ff) (hw.transitive (ZF.modelsKP hZF) n hn)
  have en i (hi : M.mem i n) : False := by
    obtain ⟨_,_,p,_,hp⟩ := fs.2.2 i hi
    exact empty p hp
  exact (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 n t r nt (run.2.1 n en)

theorem Hr_eval_d.step_l (hw : M.IsOmega ω) (fk : M.IsSetFunction I K) {s' t' x : M.Domain}
    (h : Hr_eval_d hZF ω A Q K r s t) (h' : Hr_eval_d hZF ω A Q K r s' t')
    (end' : Fseq_end_d I ω s' s x) : ∃ p, (I).Codes p t x ∧ Rd_entry_d p t' K := by
  obtain ⟨n,f,H,hn,ff,cut,run,nt⟩ := h'
  obtain ⟨k,m,e⟩ := end'
  have fs := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ff) (hw.transitive (ZF.modelsKP hZF) n hn)
  have eq := e.source.2.2.2.eq hZF.1 fs.2.1
  subst k
  have sub : M.MemberSubset m n := fun i hi => (e.length_successor i).mpr (Or.inl hi)
  have oldCut : M.IsRestrictionOf I s f m := ⟨e.prefix_restriction.1,fun i y =>
    (e.prefix_restriction.2 i y).trans ⟨fun ⟨hi,iy⟩ => ⟨hi,((cut.2 i y).mp iy).2⟩,
      fun ⟨hi,iy⟩ => ⟨hi,(cut.2 i y).mpr ⟨sub i hi,iy⟩⟩⟩⟩
  have mt := h.read_l hZF hw fk ff run e.predecessor_mem_omega oldCut
  obtain ⟨y,p,ny,pair,value⟩ := run.2.2 m n t t' e.length_successor mt nt
  have nx := ((cut.2 m x).mp e.last_value).2
  have eq := (fn0_function_l (ZF.modelsKP hZF) ff).1.2 m y x ny nx
  exact ⟨p,eq ▸ pair,value⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 对全部内部有限历史作末项归纳

归纳性质先由其实际公式分离，再按内部自然数长度归纳。
后继历史由限制图和末项精确分解，不使用宿主列表。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem history_ind_l {ω A F : M.Domain} (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    {d} (φ : UnarySchema d) (ρ : Env M d)
    (base : ∀ e, (∀ x, ¬ M.mem x e) → φ.denote ρ e)
    (step : ∀ s t a, M.mem s F → M.mem t F → M.mem a A → Fseq_end_d I ω t s a →
      φ.denote ρ s → φ.denote ρ t) : ∀ s, M.mem s F → φ.denote ρ s := by
  obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ F
  let η : Env M 2 := ⟨fun i => [A,B].get i,fun _ => A⟩
  let ψ : UnarySchema 2 := { body := set[3] ⟪∀ s,
    ⌜fn0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,⌜(.bound 1 : Term 3)⌝ₛ,s) → s ∈ ⌜(.bound 2 : Term 3)⌝ₛ⟫ }
  have sat n : ψ.denote η n ↔ ∀ s, Fn0_d n A s → M.mem s B := by
    simp only [ψ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  have all : ∀ n, M.mem n ω → ∀ s, Fn0_d n A s → M.mem s B := by
    apply hw.induction
    · obtain ⟨D,ds⟩ := ZF.separation_exists_d hZF ψ η ω
      exact ⟨D,fun n => (ds n).trans (and_congr_right fun _ => sat n)⟩
    · intro e empty s fs
      have hs : ∀ x, ¬ M.mem x s := by
        intro p hp
        obtain ⟨i,a,pair⟩ := (fn0_function_l (ZF.modelsKP hZF) fs).1.1 p hp
        exact empty i (fs.bound_l ⟨p,pair,hp⟩).1
      have heω := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
      exact (bs s).mpr ⟨(space s).mpr ⟨e,heω,fn0_function_l (ZF.modelsKP hZF) fs⟩,base s hs⟩
    · intro n hn ih m succ t ft
      have ff := fn0_function_l (ZF.modelsKP hZF) ft
      obtain ⟨s,cut⟩ := ZF.exists_restriction hZF I t n
      have sub : M.MemberSubset n m := fun i hi => (succ i).mpr (Or.inl hi)
      have fs := cut.isSetFunctionFromTo ff sub
      obtain ⟨a,ha,na⟩ := ft.2.1 n succ.predecessor_mem
      obtain ⟨j,succ',hj⟩ := hw.1.2 n hn
      have hm : M.mem m ω := succ'.eq hZF.1 succ ▸ hj
      have hsF := (space s).mpr ⟨n,hn,fs⟩
      have htF := (space t).mpr ⟨m,hm,ff⟩
      have end' : Fseq_end_d I ω t s a := ⟨m,n,⟨hm,hw.members_areOrdinals (ZF.modelsKP hZF) m hm,ff.1,ff.2.1⟩,
        hn,succ,⟨hn,hw.members_areOrdinals (ZF.modelsKP hZF) n hn,fs.1,fs.2.1⟩,cut,na⟩
      exact (bs t).mpr ⟨htF,step s t a hsF htF ha end' ((bs s).mp (ih s (fn0_of_function_l (ZF.modelsKP hZF) fs))).2⟩
  intro s hs
  obtain ⟨n,hn,fs⟩ := (space s).mp hs
  exact ((bs s).mp (all n hn s (fn0_of_function_l (ZF.modelsKP hZF) fs))).2

end YesMetaZFC.SetTheory.Descriptive

/-! ## 无终端节点树上的实际纠正表

先在模型内为每个节点选定一个后继。给定原字母时，若追加合法则保留它，
否则使用该后继；整张响应表由集合选择与替换构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tree_correction_l {ω A F R : M.Domain}
    (space : Fseq_space_d I ω A F) (tree : Tree_d F R)
    (next : ∀ s, M.mem s R → ∃ t, M.mem t R ∧ Step_d I ω s t) :
    ∃ D K, M.IsCartesianProduct I D R A ∧ Fn0_d D R K ∧
      (∀ s a p t, (I).Codes p s a → Rd_entry_d p t K → Step_d I ω s t) ∧
      (∀ s t a p, M.mem s R → M.mem t R → Fseq_end_d I ω t s a →
        (I).Codes p s a → Rd_entry_d p t K) := by
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let ψ : BinarySchema 1 := { body := step_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) .newest }
  obtain ⟨d,fd,steps⟩ := ZFC.uniformize_formula_l I hZFC ψ ρ (by
    intro s hs
    obtain ⟨t,ht,st⟩ := next s hs
    exact ⟨t,ht,(step_sat_l I hZF.1 ..).mpr st⟩)
  have chosen s t (st : Rd_entry_d s t d) : Step_d I ω s t := (step_sat_l I hZF.1 ..).mp (steps s t st)
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF I R A
  let η : Env M 3 := ⟨fun i => [ω,R,d].get i,fun _ => ω⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ s a,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,s,a) ∧
    ((⌜(.newest : Term 5)⌝ₛ ∈ ⌜(.bound 3 : Term 5)⌝ₛ ∧
      ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ,⌜(.newest : Term 5)⌝ₛ,s,a)) ∨
    (¬ (∃ t ∈ ⌜(.bound 3 : Term 5)⌝ₛ, ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ,t,s,a))) ∧
      ⌜rd_entry0_m⌝ₚ(s,⌜(.newest : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ))⟫ }
  have sat p t : φ.denote η p t ↔ ∃ s a, (I).Codes p s a ∧
      ((M.mem t R ∧ Fseq_end_d I ω t s a) ∨
        (¬ ∃ u, M.mem u R ∧ Fseq_end_d I ω u s a) ∧ Rd_entry_d s t d) := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,fseq_end_sat_l I hZF.1,
      Formula.satisfies_neg_iff,Formula.satisfies_existsMem_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨K,fk,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η (source := D) (target := R) (by
    intro p hp
    obtain ⟨s,hs,a,_,pair⟩ := (product p).mp hp
    rcases Classical.em (∃ t, M.mem t R ∧ Fseq_end_d I ω t s a) with yes | no
    · obtain ⟨t,ht,end'⟩ := yes
      exact ⟨t,(sat p t).mpr ⟨s,a,pair,Or.inl ⟨ht,end'⟩⟩⟩
    · obtain ⟨t,_,st⟩ := fd.2.2 s hs
      exact ⟨t,(sat p t).mpr ⟨s,a,pair,Or.inr ⟨no,st⟩⟩⟩) (by
    intro p _ t u ht hu
    obtain ⟨s,a,pair,ht⟩ := (sat p t).mp ht
    obtain ⟨s',a',pair',hu⟩ := (sat p u).mp hu
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact fseq_end_rebuild_l I hZF.1 ht.2 hu.2
    · exact (hu.1 ⟨t,ht⟩).elim
    · exact (ht.1 ⟨u,hu⟩).elim
    · exact fd.1.2 s t u ht.2 hu.2) (by
    intro p t _ ht
    obtain ⟨s,_,_,ht⟩ := (sat p t).mp ht
    exact ht.elim And.left (fun ht => fd.output_mem_of_pairMember ht.2))
  refine ⟨D,K,product,fn0_of_function_l (ZF.modelsKP hZF) fk,?_,?_⟩
  · intro s a p t pair pt
    obtain ⟨s',a',pair',cases⟩ := (sat p t).mp ((values p t).mp pt).2
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    exact cases.elim (fun ht => ⟨a,ht.2⟩) (fun ht => chosen s t ht.2)
  · intro s t a p hs ht end' pair
    obtain ⟨n,hn,ft⟩ := (space t).mp (tree.1 t ht)
    have ending := end'
    obtain ⟨_,_,decomp⟩ := ending
    have ha := ft.output_mem_of_pairMember decomp.last_value
    exact (values p t).mpr ⟨(product p).mpr ⟨s,hs,a,ha,pair⟩,(sat p t).mpr ⟨s,a,pair,Or.inl ⟨ht,end'⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 无终端节点树的保长度、保前缀收缩

同一纠正表的有限求值构成收缩图。精确阶段长度与完整运行的并图证明
前缀保持；树内节点逐步不需纠正，故收缩在原树上恒等。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tr_retract_d (I : kpair_convention_l.Interpretation M) (ω A F R π : M.Domain) : Prop where
  function : Fn0_d F R π
  length : ∀ n s t, M.mem n ω → Fn0_d n A s → Rd_entry_d s t π → Fn0_d n A t
  monotone : ∀ s t u v, Rd_entry_d s u π → Rd_entry_d t v π → M.MemberSubset s t → M.MemberSubset u v
  fixed : ∀ s, M.mem s R → Rd_entry_d s s π
  lift : ∀ s r t a u, Rd_entry_d s r π → M.mem t R → Fseq_end_d I ω t r a →
    Fseq_end_d I ω u s a → Rd_entry_d u t π

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tree_retraction_l {ω A F R e : M.Domain} (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    (tree : Tree_d F R) (empty : ∀ x, ¬ M.mem x e) (root : M.mem e R)
    (next : ∀ s, M.mem s R → ∃ t, M.mem t R ∧ Step_d I ω s t) :
    ∃ π, Tr_retract_d I ω A F R π := by
  obtain ⟨D,K,prod,fn,step,keep⟩ := tree_correction_l hZFC space tree next
  have fk := (fn0_function_l (ZF.modelsKP hZF) fn).1
  obtain ⟨t,ht,a,end'⟩ := next e root
  obtain ⟨_,_,ft⟩ := (space t).mp (tree.1 t ht)
  obtain ⟨_,_,last⟩ := end'
  have ha := ft.output_mem_of_pairMember last.last_value
  obtain ⟨π,ff,values⟩ := hr_eval_table_l hZF hw space prod fn root ha
  have path {f H} (run : Hr_run_d hZF ω R K e f H) :
      ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H → Step_d I ω s t := by
    intro i j s t succ hs ht
    obtain ⟨x,p,_,pair,pt⟩ := run.2.2 i j s t succ hs ht
    exact step s x p t pair pt
  have typed s (hs : M.mem s R) := (space s).mp (tree.1 s hs)
  have length {n s t} (hn : M.mem n ω) (fs : Fn0_d n A s) (st : Rd_entry_d s t π) : Fn0_d n A t := by
    obtain ⟨m,f,H,hm,ft,cut,run,mt⟩ := ((values s t).mp st).2
    have eq := (cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ft)
      (hw.transitive (ZF.modelsKP hZF) m hm)).2.1.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fs).2.1
    subst m
    exact fn0_of_function_l (ZF.modelsKP hZF) (ds_path_length_l I hZF hw typed
      (fn0_function_l (ZF.modelsKP hZF) run.1) empty run.2.1 (path run) n hn t mt)
  refine ⟨π,ff,(fun n s t => length (n := n) (s := s) (t := t)),?_,?_,?_⟩
  · intro s t u v su tv sub
    obtain ⟨n,hn,fs⟩ := (space s).mp (ff.bound_l su).1
    have eval := ((values t v).mp tv).2
    obtain ⟨m,f,H,hm,ft,cut,run,mv⟩ := eval
    have tf := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ft) (hw.transitive (ZF.modelsKP hZF) m hm)
    have sf := (ds_restrict_iff_l I fs (fn0_function_l (ZF.modelsKP hZF) ft).1).mpr
      (fun p hp => (ds_restrict_iff_l I tf (fn0_function_l (ZF.modelsKP hZF) ft).1).mp cut p (sub p hp))
    have nu := Hr_eval_d.read_l hZF hw fk ft run hn sf ((values s u).mp su).2
    obtain ⟨out,fout,actual⟩ := ds_path_run_l I hZF hw typed
      (fn0_function_l (ZF.modelsKP hZF) run.1) empty run.2.1 (path run)
    have nm : M.MemberSubset n m := by
      intro i hi
      obtain ⟨x,_,ix⟩ := fs.2.2 i hi
      exact tf.input_mem_of_pairMember (ix.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩)
    exact ds_prefix_mono_l I (actual n u nu).1 (actual m v mv).1.1
      ((ds_restrict_iff_l I (actual n u nu).1 fout.1).mpr (actual n u nu).2)
      ((ds_restrict_iff_l I (actual m v mv).1 fout.1).mpr (actual m v mv).2) nm
  · let ρ : Env M 2 := ⟨fun i => [R,π].get i,fun _ => R⟩
    let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 1)) (rd_entry0_m .newest .newest (.bound 2)) }
    have sat s : φ.denote ρ s ↔ (M.mem s R → Rd_entry_d s s π) := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,rd_entry0_sat_l hZF.1]
      rfl
    have all := history_ind_l hZF hw space φ ρ (by
      intro s hs
      apply (sat s).mpr
      intro hsR
      obtain ⟨u,_,su⟩ := ff.2.1 s (tree.1 s hsR)
      have ue := (((values s u).mp su).2.zero_l hZF hw hs)
      have es := hZF.1.eq_of_same_members e s (fun x => iff_of_false (empty x) (hs x))
      exact ue.trans es ▸ su) (by
      intro s t a hs ht _ end' ih
      apply (sat t).mpr
      intro htR
      have hsR := tree.2 t htR s hs (end'.subset_l I)
      have ss := (sat s).mp ih hsR
      obtain ⟨v,_,tv⟩ := ff.2.1 t ht
      obtain ⟨p,pair,pv⟩ := (((values s s).mp ss).2.step_l hZF hw fk ((values t v).mp tv).2 end')
      have eq := fk.2 p v t pv (keep s t a p hsR htR end' pair)
      exact eq ▸ tv)
    exact fun s hs => (sat s).mp (all s (tree.1 s hs)) hs
  · intro s r t a u sr ht endt endu
    obtain ⟨n,hn,fs⟩ := (space s).mp (ff.bound_l sr).1
    have ending := endt
    obtain ⟨_,_,decomp⟩ := ending
    obtain ⟨_,_,ft⟩ := typed t ht
    have ha := ft.output_mem_of_pairMember decomp.last_value
    obtain ⟨m,u',hm,fu,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn fs ha
    have eq := fseq_end_rebuild_l I hZF.1 end' endu
    subst u'
    obtain ⟨v,_,uv⟩ := ff.2.1 u ((space u).mpr ⟨m,hm,fu⟩)
    obtain ⟨p,pair,pv⟩ := (((values s r).mp sr).2.step_l hZF hw fk ((values u v).mp uv).2 endu)
    exact fk.2 p v t pv (keep r t a p (ff.bound_l sr).2 ht endt pair) ▸ uv

end YesMetaZFC.SetTheory.Descriptive

/-! ## 历史收缩的逐步响应及无限对局像 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tr_path_d (ω π x y : M.Domain) : Prop := ∀ n, M.mem n ω → ∀ s t,
  M.IsRestrictionOf I s x n → M.IsRestrictionOf I t y n → Rd_entry_d s t π

variable {ω A F R π : M.Domain}

theorem Tr_retract_d.end_l (retract : Tr_retract_d I ω A F R π)
    (space : Fseq_space_d I ω A F) {s t u v a : M.Domain}
    (su : Rd_entry_d s u π) (tv : Rd_entry_d t v π) (end' : Fseq_end_d I ω t s a) :
    ∃ b, M.mem b A ∧ Fseq_end_d I ω v u b := by
  obtain ⟨n,hn,fs⟩ := (space s).mp (retract.function.bound_l su).1
  obtain ⟨m,hm,ft⟩ := (space t).mp (retract.function.bound_l tv).1
  obtain ⟨j,k,e⟩ := end'
  have eq := e.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst k
  have eq := e.source.2.2.2.eq hZF.1 ft.2.1
  subst j
  have fu := fn0_function_l (ZF.modelsKP hZF) (retract.length n s u hn (fn0_of_function_l (ZF.modelsKP hZF) fs) su)
  have fv := fn0_function_l (ZF.modelsKP hZF) (retract.length m t v hm (fn0_of_function_l (ZF.modelsKP hZF) ft) tv)
  obtain ⟨b,hb,nb⟩ := fv.2.2 n e.length_successor.predecessor_mem
  have subset := retract.monotone s t u v su tv (Fseq_end_d.subset_l I ⟨m,n,e⟩)
  exact ⟨b,hb,m,n,⟨hm,e.source.2.1,fv.1,fv.2.1⟩,hn,e.length_successor,
    ⟨hn,e.prefix_sequence.2.1,fu.1,fu.2.1⟩,(ds_restrict_iff_l I fu fv.1).mpr subset,nb⟩

theorem Tr_retract_d.branch_l (retract : Tr_retract_d I ω A F R π) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F R) {e x : M.Domain}
    (empty : ∀ z, ¬ M.mem z e) (root : M.mem e R) (fx : Fn0_d ω A x) :
    ∃ y, Fn0_d ω A y ∧ Branch_d F R y ∧ Tr_path_d hZF ω π x y := by
  let ρ : Env M 2 := ⟨fun i => [x,π].get i,fun _ => x⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ s,
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(s,⌜(.bound 2 : Term 4)⌝ₛ,⌜(.bound 1 : Term 4)⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(s,⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat n t : φ.denote ρ n t ↔ ∃ s, M.IsRestrictionOf I s x n ∧ Rd_entry_d s t π := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_isRestriction_iff I,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have ff := fn0_function_l (ZF.modelsKP hZF) fx
  have fp := (fn0_function_l (ZF.modelsKP hZF) retract.function).1
  obtain ⟨H,fh,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := R) (by
    intro n hn
    obtain ⟨s,fs,cut,_⟩ := ds_prefix_l I hZF hw ff hn
    obtain ⟨t,_,st⟩ := retract.function.2.1 s ((space s).mpr ⟨n,hn,fs⟩)
    exact ⟨t,(sat n t).mpr ⟨s,cut,st⟩⟩) (by
    intro n _ u v hu hv
    obtain ⟨s,cut,su⟩ := (sat n u).mp hu
    obtain ⟨t,cut',tv⟩ := (sat n v).mp hv
    exact fp.2 s u v su (cut'.eq hZF.1 cut ▸ tv)) (by
    intro n t _ ht
    obtain ⟨s,_,st⟩ := (sat n t).mp ht
    exact (retract.function.bound_l st).2)
  have hz z (ez : ∀ a, ¬ M.mem a z) : Rd_entry_d z e H := by
    refine (values z e).mpr ⟨num_mem_l hZF.1 hw (show Num_d 0 z from ez),(sat z e).mpr ⟨e,?_,retract.fixed e root⟩⟩
    exact ⟨(ds_empty_fun_l I (X := A) empty).1.1,fun i a => iff_of_false
      (fun ⟨p,_,hp⟩ => empty p hp) (fun hi => ez i hi.1)⟩
  have step i j u v (succ : M.SuccessorOf j i) (hu : Rd_entry_d i u H) (hv : Rd_entry_d j v H) : Step_d I ω u v := by
    obtain ⟨s,rs,su⟩ := (sat i u).mp ((values i u).mp hu).2
    obtain ⟨t,rt,tv⟩ := (sat j v).mp ((values j v).mp hv).2
    have hi := fh.input_mem_of_pairMember hu
    have hj := fh.input_mem_of_pairMember hv
    have fs := rs.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) i hi)
    have ft := rt.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) j hj)
    obtain ⟨a,_,ia⟩ := ft.2.2 i succ.predecessor_mem
    have end' : Fseq_end_d I ω t s a := ⟨j,i,⟨hj,hw.members_areOrdinals (ZF.modelsKP hZF) j hj,ft.1,ft.2.1⟩,
      hi,succ,⟨hi,hw.members_areOrdinals (ZF.modelsKP hZF) i hi,fs.1,fs.2.1⟩,
      rt.trans rs (fun k hk => (succ k).mpr (Or.inl hk)),ia⟩
    obtain ⟨b,_,end'⟩ := retract.end_l hZF space su tv end'
    exact ⟨b,end'⟩
  obtain ⟨y,fy,actual⟩ := ds_path_run_l I hZF hw (fun t ht => (space t).mp (tree.1 t ht)) fh empty hz step
  refine ⟨y,fn0_of_function_l (ZF.modelsKP hZF) fy,?_,?_⟩
  · apply (tree_branch_l I hZF hw space fy).mpr
    intro n hn
    obtain ⟨t,ht,nt⟩ := fh.2.2 n hn
    exact ⟨t,ht,(ds_restrict_iff_l I (actual n t nt).1 fy.1).mpr (actual n t nt).2⟩
  · intro n hn s t rs rt
    obtain ⟨v,_,nv⟩ := fh.2.2 n hn
    obtain ⟨u,ru,uv⟩ := (sat n v).mp ((values n v).mp nv).2
    have es := ru.eq hZF.1 rs
    have et := ((ds_restrict_iff_l I (actual n v nv).1 fy.1).mpr (actual n v nv).2).eq hZF.1 rt
    exact es ▸ et ▸ uv

end YesMetaZFC.SetTheory.Descriptive

/-! ## 两方共用的虚拟历史一步表

本方策略建议经收缩后恰为实际落子时，记录原建议；否则记录实际字母。
因此对所有合法历史都保持精确收缩关系，不仅限于服从策略的历史。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Rs_match_d (b : Bool) (ω π σ s a t : M.Domain) : Prop := ∃ n c r u,
  M.IsDomainOf I n s ∧ Gm_turn_d I b ω n ∧ Rd_entry_d s c σ ∧ Fseq_end_d I ω t s c ∧
    Rd_entry_d s r π ∧ Rd_entry_d t u π ∧ Fseq_end_d I ω u r a

def rs_match_m (b : Bool) {d} (ω π σ s a t : Term d) : Formula 1 d := set[d] ⟪∃ n c r u,
  ⌜(Formula.isDomain kpair_convention_l)⌝ₚ(n,⌜s⌝ₛ) ∧ ⌜(gm_turn_m (𝒞 := kpair_convention_l) b)⌝ₚ(⌜ω⌝ₛ,n) ∧
  ⌜rd_entry0_m⌝ₚ(⌜s⌝ₛ,c,⌜σ⌝ₛ) ∧ ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,⌜t⌝ₛ,⌜s⌝ₛ,c) ∧
  ⌜rd_entry0_m⌝ₚ(⌜s⌝ₛ,r,⌜π⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜t⌝ₛ,u,⌜π⌝ₛ) ∧
  ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,u,r,⌜a⌝ₛ)⟫
derive_free_closed rs_match_m

theorem rs_match_sat_l (b : Bool) {d} (ρ : Env M d) (ω π σ s a t : Term d) :
    Formula.satisfies ρ (rs_match_m b ω π σ s a t) ↔
      Rs_match_d hZF b (ω.eval ρ) (π.eval ρ) (σ.eval ρ) (s.eval ρ) (a.eval ρ) (t.eval ρ) := by
  simp only [rs_match_m,Rs_match_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I,gm_turn_sat_l I hZF.1 b,rd_entry0_sat_l hZF.1,
    fseq_end_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

def Rs_step_d (b : Bool) (ω π σ s a t : M.Domain) : Prop := Rs_match_d hZF b ω π σ s a t ∨
  (¬ ∃ u, Rs_match_d hZF b ω π σ s a u) ∧ Fseq_end_d I ω t s a

def rs_step_m (b : Bool) {d} (ω π σ s a t : Term d) : Formula 1 d :=
  .disj (rs_match_m b ω π σ s a t) (.conj
    (.neg (.existsE (rs_match_m b ω.weaken π.weaken σ.weaken s.weaken a.weaken .newest)))
    (fseq_end_m (𝒞 := kpair_convention_l) ω t s a))
derive_free_closed rs_step_m

theorem rs_step_sat_l (b : Bool) {d} (ρ : Env M d) (ω π σ s a t : Term d) :
    Formula.satisfies ρ (rs_step_m b ω π σ s a t) ↔
      Rs_step_d hZF b (ω.eval ρ) (π.eval ρ) (σ.eval ρ) (s.eval ρ) (a.eval ρ) (t.eval ρ) := by
  simp only [rs_step_m,Rs_step_d,Formula.satisfies_disj_iff,rs_match_sat_l hZF b,
    Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,Formula.satisfies_exists_iff,
    fseq_end_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

variable {b : Bool} {ω A F R π σ s a t : M.Domain}

theorem Rs_match_d.unique_l {u : M.Domain} (fs : M.IsSetFunction I σ)
    (h : Rs_match_d hZF b ω π σ s a t) (h' : Rs_match_d hZF b ω π σ s a u) : t = u := by
  obtain ⟨_,c,_,_,_,_,sc,ending,_⟩ := h
  obtain ⟨_,d,_,_,_,_,sd,ending',_⟩ := h'
  exact fseq_end_rebuild_l I hZF.1 ending (fs.2 s d c sd sc ▸ ending')

theorem Rs_step_d.end_l (h : Rs_step_d hZF b ω π σ s a t) : Step_d I ω s t := by
  rcases h with ⟨_,c,_,_,_,_,_,ending,_⟩ | ⟨_,ending⟩
  · exact ⟨c,ending⟩
  · exact ⟨a,ending⟩

theorem Rs_step_d.image_l (retract : Tr_retract_d I ω A F R π) {r u : M.Domain}
    (h : Rs_step_d hZF b ω π σ s a t) (sr : Rd_entry_d s r π) (hu : M.mem u R)
    (ending : Fseq_end_d I ω u r a) : Rd_entry_d t u π := by
  rcases h with ⟨_,_,r',u',_,_,_,_,sr',tu',ending'⟩ | ⟨_,end'⟩
  · have eq := (fn0_function_l (ZF.modelsKP hZF) retract.function).1.2 s r' r sr' sr
    exact fseq_end_rebuild_l I hZF.1 (eq ▸ ending') ending ▸ tu'
  · exact retract.lift s r u a t sr hu ending end'

theorem rs_table_l (b : Bool) (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    (retract : Tr_retract_d I ω A F R π) (strategy : Fn0_d F A σ) :
    ∃ D K, M.IsCartesianProduct I D F A ∧ Fn0_d D F K ∧
      ∀ s a p t, (I).Codes p s a → Rd_entry_d p t K → Rs_step_d hZF b ω π σ s a t := by
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF I F A
  let ρ : Env M 3 := ⟨fun i => [ω,π,σ].get i,fun _ => ω⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ s a, ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,s,a) ∧
    ⌜(rs_step_m b)⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ,s,a,⌜(.newest : Term 5)⌝ₛ)⟫ }
  have sat p t : φ.denote ρ p t ↔ ∃ s a, (I).Codes p s a ∧ Rs_step_d hZF b ω π σ s a t := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,rs_step_sat_l hZF b,Definitional.Term.eval_weaken]
    rfl
  have ss := (fn0_function_l (ZF.modelsKP hZF) strategy).1
  obtain ⟨K,fk,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := F) (by
    intro p hp
    obtain ⟨s,hs,a,ha,pair⟩ := (product p).mp hp
    rcases Classical.em (∃ t, Rs_match_d hZF b ω π σ s a t) with yes | no
    · obtain ⟨t,match'⟩ := yes
      exact ⟨t,(sat p t).mpr ⟨s,a,pair,Or.inl match'⟩⟩
    · obtain ⟨n,hn,fs⟩ := (space s).mp hs
      obtain ⟨_,t,_,_,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn fs ha
      exact ⟨t,(sat p t).mpr ⟨s,a,pair,Or.inr ⟨no,end'⟩⟩⟩) (by
    intro p _ t u ht hu
    obtain ⟨s,a,pair,ht⟩ := (sat p t).mp ht
    obtain ⟨s',a',pair',hu⟩ := (sat p u).mp hu
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact ht.unique_l hZF ss hu
    · exact (hu.1 ⟨t,ht⟩).elim
    · exact (ht.1 ⟨u,hu⟩).elim
    · exact fseq_end_rebuild_l I hZF.1 ht.2 hu.2) (by
    intro p t hp ht
    obtain ⟨s,a,pair,ht⟩ := (sat p t).mp ht
    rcases ht with ⟨_,_,_,_,_,_,_,_,_,point,_⟩ | ⟨_,end'⟩
    · exact (retract.function.bound_l point).1
    · obtain ⟨s',hs,a',ha,pair'⟩ := (product p).mp hp
      obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
      obtain ⟨n,hn,fs⟩ := (space s).mp hs
      obtain ⟨m,u,hm,fu,ending⟩ := ZF.fseq_end_exists_l I hZF hw hn fs ha
      exact fseq_end_rebuild_l I hZF.1 ending end' ▸ (space u).mpr ⟨m,hm,fu⟩)
  refine ⟨D,K,product,fn0_of_function_l (ZF.modelsKP hZF) fk,?_⟩
  intro s a p t pair pt
  obtain ⟨s',a',pair',step⟩ := (sat p t).mp ((values p t).mp pt).2
  obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
  exact step

end YesMetaZFC.SetTheory.Descriptive

/-! ## 虚拟历史在全部合法节点上精确提升收缩

一步匹配规则和树内原样提升共同保持 π(H(r))=r。归纳使用原公式，
包含偏离策略的合法历史，故最终策略确实定义在全部本方节点上。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Rs_sim_d (b : Bool) (ω A F R π σ e D K H : M.Domain) : Prop where
  product : M.IsCartesianProduct I D F A
  response : Fn0_d D F K
  step : ∀ s a p t, (I).Codes p s a → Rd_entry_d p t K → Rs_step_d hZF b ω π σ s a t
  function : Fn0_d F F H
  values : ∀ r s, Rd_entry_d r s H ↔ M.mem r F ∧ Hr_eval_d hZF ω A F K e r s
  image : ∀ r s, M.mem r R → Rd_entry_d r s H → Rd_entry_d s r π

theorem rs_simulation_l {b : Bool} {ω A F R π σ e a : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F R) (retract : Tr_retract_d I ω A F R π)
    (strategy : Fn0_d F A σ) (empty : ∀ x, ¬ M.mem x e) (root : M.mem e R) (ha : M.mem a A) :
    ∃ D K H, Rs_sim_d hZF b ω A F R π σ e D K H := by
  obtain ⟨D,K,prod,fk,step⟩ := rs_table_l hZF b hw space retract strategy
  obtain ⟨H,fh,values⟩ := hr_eval_table_l hZF hw space prod fk (tree.1 e root) ha
  refine ⟨D,K,H,prod,fk,step,fh,values,?_⟩
  let ρ : Env M 3 := ⟨fun i => [R,H,π].get i,fun _ => R⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ →
    ∀ s, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,s,⌜(.bound 2 : Term 4)⌝ₛ) →
      ⌜rd_entry0_m⌝ₚ(s,⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat r : φ.denote ρ r ↔ M.mem r R → ∀ s, Rd_entry_d r s H → Rd_entry_d s r π := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_forall_iff,
      Formula.satisfies_mem_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all := history_ind_l hZF hw space φ ρ (by
    intro r er
    apply (sat r).mpr
    intro hr s rs
    have se := (((values r s).mp rs).2.zero_l hZF hw er)
    have eq := hZF.1.eq_of_same_members e r (fun x => iff_of_false (empty x) (er x))
    exact (se.trans eq).symm ▸ retract.fixed r hr) (by
    intro r t a hr ht _ end' ih
    apply (sat t).mpr
    intro htR u tu
    have hrR := tree.2 t htR r hr (end'.subset_l I)
    obtain ⟨s,_,rs⟩ := fh.2.1 r hr
    have sr := (sat r).mp ih hrR s rs
    obtain ⟨p,pair,pu⟩ := (((values r s).mp rs).2.step_l hZF hw
      (fn0_function_l (ZF.modelsKP hZF) fk).1 ((values t u).mp tu).2 end')
    exact (step s a p u pair pu).image_l hZF retract sr htR end')
  exact fun r s hr rs => (sat r).mp (all r (tree.1 r hr)) hr s rs

theorem Rs_sim_d.path_l {b : Bool} {ω A F R π σ e D K H f G : M.Domain}
    (sim : Rs_sim_d hZF b ω A F R π σ e D K H) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (empty : ∀ x, ¬ M.mem x e)
    (run : Hr_run_d hZF ω F K e f G) : ∃ x, Fn0_d ω A x ∧
      ∀ n s, Rd_entry_d n s G → Fn0_d n A s ∧ M.IsRestrictionOf I s x n := by
  obtain ⟨x,fx,actual⟩ := ds_path_run_l I hZF hw (fun s hs => (space s).mp hs)
    (fn0_function_l (ZF.modelsKP hZF) run.1) empty run.2.1 (by
      intro i j s t succ hs ht
      obtain ⟨a,p,_,pair,pt⟩ := run.2.2 i j s t succ hs ht
      exact (sim.step s a p t pair pt).end_l hZF)
  exact ⟨x,fn0_of_function_l (ZF.modelsKP hZF) fx,fun n s ns =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF) (actual n s ns).1,
      (ds_restrict_iff_l I (actual n s ns).1 fx.1).mpr (actual n s ns).2⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 虚拟历史中原策略的建议给出实际树上落子 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Rs_answer_d (ω π σ H r b : M.Domain) : Prop := ∃ s a q t,
  Rd_entry_d r s H ∧ Rd_entry_d s a σ ∧ Fseq_end_d I ω q s a ∧
    Rd_entry_d q t π ∧ Fseq_end_d I ω t r b

def rs_answer_m {d} (ω π σ H r b : Term d) : Formula 1 d := set[d] ⟪∃ s a q t,
  ⌜rd_entry0_m⌝ₚ(⌜r⌝ₛ,s,⌜H⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(s,a,⌜σ⌝ₛ) ∧
  ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,q,s,a) ∧
  ⌜rd_entry0_m⌝ₚ(q,t,⌜π⌝ₛ) ∧ ⌜(fseq_end_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,t,⌜r⌝ₛ,⌜b⌝ₛ)⟫
derive_free_closed rs_answer_m

theorem rs_answer_sat_l {d} (ρ : Env M d) (ω π σ H r b : Term d) :
    Formula.satisfies ρ (rs_answer_m ω π σ H r b) ↔
      Rs_answer_d hZF (ω.eval ρ) (π.eval ρ) (σ.eval ρ) (H.eval ρ) (r.eval ρ) (b.eval ρ) := by
  simp only [rs_answer_m,Rs_answer_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1,fseq_end_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem Rs_sim_d.strategy_l {b : Bool} {ω A F R π σ e D K H : M.Domain}
    (sim : Rs_sim_d hZF b ω A F R π σ e D K H) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F R) (retract : Tr_retract_d I ω A F R π)
    (strategy : Fn0_d F A σ) : ∃ τ, Fn0_d R A τ ∧
      (∀ r b, Rd_entry_d r b τ ↔ M.mem r R ∧ Rs_answer_d hZF ω π σ H r b) ∧
      ∀ r b, Rd_entry_d r b τ → ∃ t, M.mem t R ∧ Fseq_end_d I ω t r b := by
  let ρ : Env M 4 := ⟨fun i => [ω,π,σ,H].get i,fun _ => ω⟩
  let φ : BinarySchema 4 := { body := rs_answer_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) .newest }
  have sat r b : φ.denote ρ r b ↔ Rs_answer_d hZF ω π σ H r b := rs_answer_sat_l hZF ..
  have fs := (fn0_function_l (ZF.modelsKP hZF) strategy).1
  have fh := (fn0_function_l (ZF.modelsKP hZF) sim.function).1
  have fp := (fn0_function_l (ZF.modelsKP hZF) retract.function).1
  obtain ⟨τ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := R) (target := A) (by
    intro r hr
    obtain ⟨s,hs,rs⟩ := sim.function.2.1 r (tree.1 r hr)
    obtain ⟨a,ha,sa⟩ := strategy.2.1 s hs
    obtain ⟨n,hn,fn⟩ := (space s).mp hs
    obtain ⟨m,q,hm,fq,ending⟩ := ZF.fseq_end_exists_l I hZF hw hn fn ha
    obtain ⟨t,_,qt⟩ := retract.function.2.1 q ((space q).mpr ⟨m,hm,fq⟩)
    obtain ⟨b,_,end'⟩ := retract.end_l hZF space (sim.image r s hr rs) qt ending
    exact ⟨b,(sat r b).mpr ⟨s,a,q,t,rs,sa,ending,qt,end'⟩⟩) (by
    intro r _ x y hx hy
    obtain ⟨s,a,q,t,rs,sa,ending,qt,end'⟩ := (sat r x).mp hx
    obtain ⟨s',a',q',t',rs',sa',ending',qt',end''⟩ := (sat r y).mp hy
    have eq := fh.2 r s' s rs' rs
    subst s'
    have eq := fs.2 s a' a sa' sa
    subst a'
    have eq := fseq_end_rebuild_l I hZF.1 ending' ending
    subst q'
    have eq := fp.2 q t' t qt' qt
    subst t'
    exact (fseq_end_unique_l I hZF.1 end' end'').2) (by
    intro r b _ hb
    obtain ⟨_,_,q,t,_,_,_,qt,_,_,ending⟩ := (sat r b).mp hb
    obtain ⟨_,_,ft⟩ := (space t).mp (tree.1 t (retract.function.bound_l qt).2)
    exact ft.output_mem_of_pairMember ending.last_value)
  refine ⟨τ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun r b =>
    (values r b).trans (and_congr_right fun _ => sat r b),?_⟩
  intro r b rb
  obtain ⟨_,_,q,t,_,_,_,qt,end'⟩ := (sat r b).mp ((values r b).mp rb).2
  exact ⟨t,(retract.function.bound_l qt).2,end'⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 保前缀收缩下的双向回合策略模拟

树上策略的每个服从对局都有一个服从原策略的虚拟对局，且前者是
后者的收缩像。赢家参数统一处理 I 和 II，不依赖任何收益集的决定性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Gt_strategy_d (b : Bool) (ω A R σ : M.Domain) : Prop where
  strategy : Gm_strategy_d I b ω A R σ
  legal : ∀ s a, Rd_entry_d s a σ → ∃ t, M.mem t R ∧ Fseq_end_d I ω t s a

theorem Rs_sim_d.follows_l {b : Bool} {ω A F R π σ e D K H τ f G : M.Domain}
    (sim : Rs_sim_d hZF b ω A F R π σ e D K H) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (empty : ∀ x, ¬ M.mem x e)
    (strategy : Fn0_d F A σ)
    (values : ∀ r a, Rd_entry_d r a τ → Rs_answer_d hZF ω π σ H r a)
    (input : Fn0_d ω A f) (branch : Branch_d F R f) (follows : Gm_follows_d I b ω τ f)
    (run : Hr_run_d hZF ω F K e f G) :
    ∃ x, Fn0_d ω A x ∧ Gm_follows_d I b ω σ x ∧ Tr_path_d hZF ω π x f := by
  obtain ⟨x,fx,actual⟩ := sim.path_l hZF hw space empty run
  have fk := (fn0_function_l (ZF.modelsKP hZF) sim.response).1
  have ff := fn0_function_l (ZF.modelsKP hZF) input
  have xf := fn0_function_l (ZF.modelsKP hZF) fx
  have finite {n r s} (hn : M.mem n ω) (cut : M.IsRestrictionOf I r f n) (ns : Rd_entry_d n s G) :
      M.mem r R ∧ Rd_entry_d r s H := by
    have fr := cut.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) n hn)
    have hrF := (space r).mpr ⟨n,hn,fr⟩
    have hr := branch r hrF ((ds_restrict_iff_l I fr ff.1).mp cut)
    obtain ⟨t,_,rt⟩ := sim.function.2.1 r hrF
    have nt := Hr_eval_d.read_l hZF hw fk input run hn cut ((sim.values r t).mp rt).2
    exact ⟨hr,(fn0_function_l (ZF.modelsKP hZF) run.1).1.2 n t s nt ns ▸ rt⟩
  refine ⟨x,fx,?_,?_⟩
  · intro n hn turn s cut a na
    obtain ⟨v,_,nv⟩ := run.1.2.1 n hn
    have eq := (actual n v nv).2.eq hZF.1 cut
    subst v
    obtain ⟨r,fr,rf,_⟩ := ds_prefix_l I hZF hw ff hn
    obtain ⟨hr,rs⟩ := finite hn rf nv
    obtain ⟨c,_,nc⟩ := input.2.1 n hn
    obtain ⟨s',a',q,t,rs',sa',endq,qt,endt⟩ := values r c (follows n hn turn r rf c nc)
    have eq := (fn0_function_l (ZF.modelsKP hZF) sim.function).1.2 r s' s rs' rs
    subst s'
    have matched : Rs_match_d hZF b ω π σ s c q :=
      ⟨n,a',r,t,(fn0_function_l (ZF.modelsKP hZF) (actual n s nv).1).2.1,turn,sa',endq,
        sim.image r s hr rs,qt,endt⟩
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨u,_,mu⟩ := run.1.2.1 m hm
    obtain ⟨c',p,nc',pair,pu⟩ := run.2.2 n m s u succ nv mu
    have eq := ff.1.2 n c' c nc' nc
    subst c'
    have step := sim.step s c p u pair pu
    have uq : u = q := step.elim (fun match' => match'.unique_l hZF
      (fn0_function_l (ZF.modelsKP hZF) strategy).1 matched) (fun no => (no.1 ⟨q,matched⟩).elim)
    have endu := uq.symm ▸ endq
    obtain ⟨_,k,ending⟩ := endu
    have eq := ending.prefix_sequence.2.2.2.eq hZF.1
      (fn0_function_l (ZF.modelsKP hZF) (actual n s nv).1).2.1
    have last : Rd_entry_d n a' u := eq ▸ ending.last_value
    have value := ((actual m u mu).2.2 n a').mp last |>.2
    exact xf.1.2 n a' a value na ▸ sa'
  · intro n hn s r sx rf
    obtain ⟨v,_,nv⟩ := run.1.2.1 n hn
    have eq := (actual n v nv).2.eq hZF.1 sx
    subst v
    obtain ⟨hr,rs⟩ := finite hn rf nv
    exact sim.image r s hr rs

theorem Tr_retract_d.strategy_l {b : Bool} {ω A F R π σ e a : M.Domain}
    (retract : Tr_retract_d I ω A F R π) (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    (tree : Tree_d F R) (empty : ∀ x, ¬ M.mem x e) (root : M.mem e R) (ha : M.mem a A)
    (strategy : Gm_strategy_d I b ω A F σ) :
    ∃ τ, Gt_strategy_d hZF b ω A R τ ∧ ∀ f, Fn0_d ω A f → Branch_d F R f →
      Gm_follows_d I b ω τ f → ∃ x, Fn0_d ω A x ∧ Gm_follows_d I b ω σ x ∧ Tr_path_d hZF ω π x f := by
  obtain ⟨O,turns,part⟩ := strategy
  obtain ⟨σ',full,fullValues⟩ := Gm_strategy_d.totalize_l hZF (F := F) part ha
  obtain ⟨D,K,H,sim⟩ := rs_simulation_l hZF (b := b) hw space tree retract full empty root ha
  obtain ⟨υ,fn,values,legal⟩ := sim.strategy_l hZF hw space tree retract full
  obtain ⟨P,own⟩ := gm_turns_l hZF b ω A R
  obtain ⟨τ,partFn,cut⟩ := own.restrict_l (ZF.modelsKP hZF) fn
  refine ⟨τ,⟨⟨P,own,partFn⟩,fun s a sa => legal s a ((cut.2 s a).mp sa).2⟩,?_⟩
  intro f ff branch follows
  have follows : Gm_follows_d I b ω υ f := fun n hn turn s rest a na =>
    ((cut.2 s a).mp (follows n hn turn s rest a na)).2
  obtain ⟨G,run⟩ := hr_run_exists_l hZF hw sim.product sim.response (tree.1 e root) ff
  obtain ⟨x,fx,played,mapped⟩ := sim.follows_l hZF hw space empty full
    (fun r a ra => ((values r a).mp ra).2) ff branch follows run
  refine ⟨x,fx,?_,mapped⟩
  intro n hn turn s rest a na
  have fs := rest.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fx) (hw.transitive (ZF.modelsKP hZF) n hn)
  have hsO := (turns s).mpr ⟨(space s).mpr ⟨n,hn,fs⟩,n,hn,fn0_of_function_l (ZF.modelsKP hZF) fs,turn⟩
  exact ((fullValues s a).mp (played n hn turn s rest a na)).2.elim And.right (fun no => (no.1 hsO).elim)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 合法树上两张实际策略的完整对弈

仅在本方合法历史上给定的策略先填充到全有限空间。内部 ω 归纳证明
实际对局的每个前缀留在原树，故填充值从未在本方回合被使用。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem gt_battle_l {ω A F R e σ τ : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (empty : ∀ x, ¬ M.mem x e) (root : M.mem e R)
    (first : Gt_strategy_d hZF true ω A R σ) (second : Gt_strategy_d hZF false ω A R τ) :
    ∃ f, Fn0_d ω A f ∧ Branch_d F R f ∧ Gm_follows_d I true ω σ f ∧ Gm_follows_d I false ω τ f := by
  classical
  obtain ⟨Os,os,fs⟩ := first.strategy
  obtain ⟨Ot,ot,ft⟩ := second.strategy
  have he := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  have fe := fn0_of_function_l (ZF.modelsKP hZF) (ds_empty_fun_l I (X := A) empty)
  obtain ⟨a,ha,_⟩ := fs.2.1 e ((os e).mpr ⟨root,e,he,fe,gm_even_zero_l I hZF hw empty⟩)
  obtain ⟨s,ss,sval⟩ := Gm_strategy_d.totalize_l hZF (F := F) fs ha
  obtain ⟨t,tt,tval⟩ := Gm_strategy_d.totalize_l hZF (F := F) ft ha
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : UnarySchema 1 := { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J,read⟩ := ZF.separation_exists_d hZF φ ρ ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (read n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 ..)
  obtain ⟨f,ff,left,right⟩ := cg_battle_l hZF (J := J) hw space ss tt
  have first_read {n h x} (hn : M.mem n ω) (hh : M.mem h R)
      (cut : M.IsRestrictionOf I h f n) (nx : Rd_entry_d n x f) (even : Gm_even_d I ω n) : Rd_entry_d h x σ := by
    have fh := cut.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) n hn)
    have own := (os h).mpr ⟨hh,n,hn,fn0_of_function_l (ZF.modelsKP hZF) fh,even⟩
    have value := ((sval h x).mp (left n hn ((turns n).mpr ⟨hn,even⟩) h cut x nx)).2
    exact value.elim And.right (fun no => (no.1 own).elim)
  have second_read {n h x} (hn : M.mem n ω) (hh : M.mem h R)
      (cut : M.IsRestrictionOf I h f n) (nx : Rd_entry_d n x f) (odd : ¬ Gm_even_d I ω n) : Rd_entry_d h x τ := by
    have fh := cut.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) n hn)
    have own := (ot h).mpr ⟨hh,n,hn,fn0_of_function_l (ZF.modelsKP hZF) fh,odd⟩
    have value := ((tval h x).mp (right n hn (fun h => odd ((turns n).mp h).2) h cut x nx)).2
    exact value.elim And.right (fun no => (no.1 own).elim)
  let η : Env M 2 := ⟨Fin.cases f (fun _ => R),fun _ => ω⟩
  let ψ : UnarySchema 2 := { body := set[3] ⟪∀ h,
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(h,⌜(.bound 1 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ) →
      h ∈ ⌜(.bound 2 : Term 3)⌝ₛ⟫ }
  have sat n : ψ.denote η n ↔ ∀ h, M.IsRestrictionOf I h f n → M.mem h R := by
    simp only [UnarySchema.denote,ψ,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_isRestriction_iff I,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  have all : ∀ n, M.mem n ω → ∀ h, M.IsRestrictionOf I h f n → M.mem h R := by
    apply hw.induction
    · obtain ⟨D,sep⟩ := ZF.separation_exists_d hZF ψ η ω
      exact ⟨D,fun n => (sep n).trans (and_congr_right fun _ => sat n)⟩
    · intro n no h cut
      have hn x (hx : M.mem x h) : False := by
        obtain ⟨i,y,pair⟩ := cut.1 x hx
        exact no i ((cut.2 i y).mp ⟨x,pair,hx⟩).1
      exact (hZF.1.eq_of_same_members h e (fun x => iff_of_false (hn x) (empty x))).symm ▸ root
    · intro n hn ih m succ h cut
      obtain ⟨q,_,cq,_⟩ := ds_prefix_l I hZF hw ff hn
      obtain ⟨x,_,nx⟩ := ff.2.2 n hn
      have end' := ds_cut_end_l hZF hw ff hn succ cq cut nx
      by_cases even : Gm_even_d I ω n
      · obtain ⟨h',hh',end''⟩ := first.legal q x (first_read hn (ih q cq) cq nx even)
        exact fseq_end_rebuild_l I hZF.1 end'' end' ▸ hh'
      · obtain ⟨h',hh',end''⟩ := second.legal q x (second_read hn (ih q cq) cq nx even)
        exact fseq_end_rebuild_l I hZF.1 end'' end' ▸ hh'
  refine ⟨f,fn0_of_function_l (ZF.modelsKP hZF) ff,?_,?_,?_⟩
  · intro h hh sub
    obtain ⟨n,hn,fh⟩ := (space h).mp hh
    exact all n hn h ((ds_restrict_iff_l I fh ff.1).mpr sub)
  · intro n hn even h cut x nx
    exact first_read hn (all n hn h cut) cut nx even
  · intro n hn odd h cut x nx
    exact second_read hn (all n hn h cut) cut nx odd

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限历史收缩图在实际初等嵌入下固定

字母表及其成员固定即足够。先固定完整有限空间及其每个成员，再固定
合法树和收缩函数；不向临界点条件添加收缩图的秩。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tr_retract_d.fixed_l {ω c d X E Y H j A F R π : M.Domain}
    (retract : Tr_retract_d I ω A F R π)
    (hw : M.IsOmega ω) (tx : M.TransitiveSet X) (ty : M.TransitiveSet Y)
    (source : Smem_d I c X E) (target : Smem_d I d Y H) (map : Smap_d I ω c d X Y j)
    (hω : M.mem ω X) (ha : Rd_entry_d A A j) (letters : ∀ x, M.mem x A → Rd_entry_d x x j)
    (hF : M.mem F X) (hR : M.mem R X) (hπ : M.mem π X)
    (space : Fseq_space_d I ω A F) (sub : M.MemberSubset R F) :
    Rd_entry_d F F j ∧ Rd_entry_d R R j ∧ Rd_entry_d π π j := by
  obtain ⟨fixed,finite⟩ := map.fixed_fseq_l hZF hw tx ty source target hω ha letters hF space
  exact ⟨fixed,map.fixed_subset_l hZF hw tx ty source target fixed finite hR sub,
    map.fixed_function_l hZF hw tx ty source target fixed finite hR hπ retract.function
      (fun _ t st => finite t (sub t (retract.function.bound_l st).2))⟩

end YesMetaZFC.SetTheory.Descriptive
