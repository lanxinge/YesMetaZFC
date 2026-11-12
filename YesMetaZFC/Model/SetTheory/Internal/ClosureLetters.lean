import YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative
import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem
import YesMetaZFC.Model.SetTheory.Embedding.Elementary
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree

/-! # 带见证位置表的有限闭包尝试

枚举 e 和自然数表 u 同时增长。任务由规则及有限输入位置列编号；u 指定
其输出位置。仅当任务编号、全部输入位置和输出位置均可见时核验运算值。
任意任务在无限枝中最终可见，因而枚举值域真正对全部内部有限元运算闭合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def Cl_at_d (ω X T J K n e u : M.Domain) : Prop :=
  ∀ m t q v k l s p x, M.mem m ω → M.mem t T → Fn0_d m n q → KPair_d M v t q →
    Rd_entry_d v k J → M.mem k n → Rd_entry_d k l u → M.mem l n → Cp0_d m n X q e s →
    KPair_d M p t s → Rd_entry_d l x e → Rd_entry_d p x K

def cl_at_m {d} (ω X T J K n e u : Term d) : Formula 1 d := set[d] ⟪∀ m t q v k l s p x,
  m ∈ ⌜ω⌝ₛ → t ∈ ⌜T⌝ₛ → ⌜fn0_m⌝ₚ(m,⌜n⌝ₛ,q) → ⌜kpair0_m⌝ₚ(v,t,q) →
  ⌜rd_entry0_m⌝ₚ(v,k,⌜J⌝ₛ) → k ∈ ⌜n⌝ₛ → ⌜rd_entry0_m⌝ₚ(k,l,⌜u⌝ₛ) → l ∈ ⌜n⌝ₛ →
  ⌜cp0_m⌝ₚ(m,⌜n⌝ₛ,⌜X⌝ₛ,q,⌜e⌝ₛ,s) → ⌜kpair0_m⌝ₚ(p,t,s) →
  ⌜rd_entry0_m⌝ₚ(l,x,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(p,x,⌜K⌝ₛ)⟫
derive_free_closed cl_at_m

theorem cl_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X T J K n e u : Term d) :
    Formula.satisfies ρ (cl_at_m ω X T J K n e u) ↔
      Cl_at_d (ω.eval ρ) (X.eval ρ) (T.eval ρ) (J.eval ρ) (K.eval ρ) (n.eval ρ) (e.eval ρ) (u.eval ρ) := by
  simp only [cl_at_m,Cl_at_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hE,kpair0_sat_l hE,rd_entry0_sat_l hE,cp0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

structure Cl_node_d (ω X T J K n e u : M.Domain) : Prop where
  natural : M.mem n ω
  enumeration : Fn0_d n X e
  witnesses : Fn0_d n ω u
  check : Cl_at_d ω X T J K n e u

def cl_node_m {d} (ω X T J K n e u : Term d) : Formula 1 d :=
  .conj (.mem n ω) (.conj (fn0_m n X e) (.conj (fn0_m n ω u) (cl_at_m ω X T J K n e u)))
derive_free_closed cl_node_m

theorem cl_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X T J K n e u : Term d) :
    Formula.satisfies ρ (cl_node_m ω X T J K n e u) ↔
      Cl_node_d (ω.eval ρ) (X.eval ρ) (T.eval ρ) (J.eval ρ) (K.eval ρ) (n.eval ρ) (e.eval ρ) (u.eval ρ) := by
  simp only [cl_node_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,fn0_sat_l hE,cl_at_sat_l hE]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.natural,h.enumeration,h.witnesses,h.check⟩⟩

theorem Cl_at_d.prefix_l {ω X T J K n m e u f v : M.Domain} (h : Cl_at_d ω X T J K m e u)
    (en : Fn0_d m X e) (ff : Fn0_d n X f)
    (fe : M.MemberSubset f e) (vu : M.MemberSubset v u) : Cl_at_d ω X T J K n f v := by
  have move {a b} (ab : Rd_entry_d a b f) : Rd_entry_d a b e := ab.elim fun p hp => ⟨p,hp.1,fe p hp.2⟩
  have sub : M.MemberSubset n m := fun i hi => (ff.2.1 i hi).elim fun x hx => (en.bound_l (move hx.2)).1
  intro a t q p k l s r x ha ht fq pair pk hk kl hl comp rpair lx
  have comp' : Cp0_d a m X q e s := ⟨comp.1,fun i hi => by
    obtain ⟨j,hj,y,hy,ij,jy,iy⟩ := comp.2 i hi
    exact ⟨j,sub j hj,y,hy,ij,move jy,iy⟩⟩
  exact h a t q p k l s r x ha ht (fq.mono_target_l sub) pair pk (sub k hk)
    (kl.elim fun p hp => ⟨p,hp.1,vu p hp.2⟩) (sub l hl) comp' rpair (move lx)

theorem Cl_node_d.prefix_l {ω X T J K n m e u f v : M.Domain} (h : Cl_node_d ω X T J K m e u)
    (hn : M.mem n ω) (ff : Fn0_d n X f) (fv : Fn0_d n ω v)
    (fe : M.MemberSubset f e) (vu : M.MemberSubset v u) : Cl_node_d ω X T J K n f v :=
  ⟨hn,ff,fv,h.check.prefix_l h.enumeration ff fe vu⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部合法有限尝试的总枝具有实际可数且运算闭合的值域。 -/
theorem cl_branch_closed_l {ω X T Q D J K e u : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω ω Q) (tasks : M.IsCartesianProduct I D T Q)
    (index : Fn0_d D ω J) (operations : M.IsSetFunction I K)
    (fe : Fn0_d ω X e) (fu : Fn0_d ω ω u)
    (branch : ∀ n, M.mem n ω → ∃ f v, Cl_node_d ω X T J K n f v ∧
      M.IsRestrictionOf I f e n ∧ M.IsRestrictionOf I v u n) :
    ∃ N, M.IsRangeOf I N e ∧ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧ Fc_closed_d I ω T K N := by
  have ef := fn0_function_l (ZF.modelsKP hZF) fe
  obtain ⟨N,range⟩ := ZF.exists_range_of_setFunction hZF I ef.1 ef.2.1
  have eN := fe.retarget_l (fun i x ix => (range x).mpr ⟨i,ix⟩)
  have sub : M.MemberSubset N X := fun x hx => ((range x).mp hx).elim fun _ h => (fe.bound_l h).2
  -- 最小原像截面把任意内部有限参数列提升为实际位置列。
  obtain ⟨ι,inj,section'⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I
    (hw.isOrdinal (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF) eN)
    (fun x hx => ((range x).mp hx).imp fun i hi => ⟨(fe.bound_l hi).1,hi⟩)
  have fi := fn0_of_function_l (ZF.modelsKP hZF) inj.1
  refine ⟨N,range,sub,⟨ι,inj⟩,?_⟩
  rintro x ⟨m,s,t,p,hm,fs,ht,pair,px⟩
  have fs := fn0_of_function_l (ZF.modelsKP hZF) fs
  obtain ⟨q,cq⟩ := cp0_exists_l (ZF.modelsKP hZF) fs fi
  obtain ⟨v,vpair⟩ := (I).total t q
  have vD := (tasks v).mpr ⟨t,ht,q,(space q).mpr ⟨m,hm,fn0_function_l (ZF.modelsKP hZF) cq.1⟩,vpair⟩
  obtain ⟨k,hk,vk⟩ := index.2.1 v vD
  obtain ⟨l,hl,kl⟩ := fu.2.1 k hk
  -- 全部输入位置、任务编号及指定输出位置有共同的内部自然数界。
  obtain ⟨b,hb,qb⟩ := at_index_bound_l hZF hw hm cq.1
  obtain ⟨a,ha,ba,ka⟩ := at_upper_l hZF hw hb hk
  obtain ⟨n,hn,an,ln⟩ := at_upper_l hZF hw ha hl
  have bn : M.MemberSubset b n := fun i hi => (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive a an i
    ((hw.members_areOrdinals (ZF.modelsKP hZF) a ha).transitive b ba i hi)
  have kn := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive a an k ka
  have qn := qb.mono_target_l bn
  obtain ⟨f,v',node,rf,rv⟩ := branch n hn
  have comp : Cp0_d m n X q f s := ⟨fs.mono_target_l sub,fun i hi => by
    obtain ⟨y,hy,iy⟩ := fs.2.1 i hi
    obtain ⟨j,hj,yj⟩ := fi.2.1 y hy
    have ij := (cq.value_l fs fi iy).mpr yj
    exact ⟨j,(qn.bound_l ij).2,y,sub y hy,ij,(rf.2 j y).mpr ⟨(qn.bound_l ij).2,section' y j yj⟩,iy⟩⟩
  obtain ⟨y,hy,ly⟩ := eN.2.1 l hl
  -- 在这一节点完成检查，由原运算图的单值性识别所需输出。
  have py := node.check m t q v k l s p y hm ht qn vpair vk kn
    ((rv.2 k l).mpr ⟨kn,kl⟩) ln comp pair ((rf.2 l y).mpr ⟨ln,ly⟩)
  exact (operations.2 p y x py px) ▸ hy

end YesMetaZFC.SetTheory.Internal

/-! ## 从真实可数闭集构造全部任务的见证位置表

枚举的最小原像给出实际截面。每个规则及有限输入位置列先求运算值，
再取该值的枚举位置；任务单射的带默认值反向函数补齐全部自然数坐标。
不同任务可自由选择相同或不同的输出位置，不施加虚假的位置互异要求。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cl_witness_l {ω X T Q D J L E K N e : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω ω Q) (tasks : M.IsCartesianProduct I D T Q)
    (index : M.IsSetInjectionFromTo I J D ω) (params : Fseq_space_d I ω X L)
    (domain : M.IsCartesianProduct I E T L) (operations : M.IsSetFunctionFromTo I K E X)
    (sub : M.MemberSubset N X) (closed : Fc_closed_d I ω T K N)
    (fe : Fn0_d ω N e) (onto : M.IsSetSurjectiveOnto I e ω N) :
    ∃ u, Fn0_d ω ω u ∧ Cl_at_d ω X T J K ω e u := by
  obtain ⟨ι,inj,section'⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I
    (hw.isOrdinal (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF) fe) onto
  have fi := fn0_of_function_l (ZF.modelsKP hZF) inj.1
  have eX := fe.mono_target_l sub
  let ρ : Env M 5 := ⟨fun i => [ω,X,e,K,ι].get i,fun _ => ω⟩
  let φ : BinarySchema 5 := { body := set[7] ⟪∃ t q m s p x,
    ⌜kpair0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,t,q) ∧ m ∈ ⌜(.bound 2 : Term 7)⌝ₛ ∧
    ⌜fn0_m⌝ₚ(m,⌜(.bound 2 : Term 7)⌝ₛ,q) ∧
    ⌜cp0_m⌝ₚ(m,⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,q,⌜(.bound 4 : Term 7)⌝ₛ,s) ∧
    ⌜kpair0_m⌝ₚ(p,t,s) ∧ ⌜rd_entry0_m⌝ₚ(p,x,⌜(.bound 5 : Term 7)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(x,⌜(.newest : Term 7)⌝ₛ,⌜(.bound 6 : Term 7)⌝ₛ)⟫ }
  have sat v l : φ.denote ρ v l ↔ ∃ t q m s p x, KPair_d M v t q ∧ M.mem m ω ∧ Fn0_d m ω q ∧
      Cp0_d m ω X q e s ∧ KPair_d M p t s ∧ Rd_entry_d p x K ∧ Rd_entry_d x l ι := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1,Formula.satisfies_mem_iff,fn0_sat_l hZF.1,cp0_sat_l hZF.1,rd_entry0_sat_l hZF.1,
      Definitional.Term.eval_weaken]
    rfl
  have total v (hv : M.mem v D) : ∃ l, φ.denote ρ v l := by
    obtain ⟨t,ht,q,hq,pair⟩ := (tasks v).mp hv
    obtain ⟨m,hm,fq⟩ := (space q).mp hq
    have fq := fn0_of_function_l (ZF.modelsKP hZF) fq
    obtain ⟨s,comp⟩ := cp0_exists_l (ZF.modelsKP hZF) fq fe
    obtain ⟨p,pp⟩ := (I).total t s
    have hp := (domain p).mpr ⟨t,ht,s,(params s).mpr ⟨m,hm,fn0_function_l (ZF.modelsKP hZF) (comp.1.mono_target_l sub)⟩,pp⟩
    obtain ⟨x,_,px⟩ := operations.2.2 p hp
    have hx := closed x ⟨m,s,t,p,hm,fn0_function_l (ZF.modelsKP hZF) comp.1,ht,pp,px⟩
    obtain ⟨l,_,xl⟩ := fi.2.1 x hx
    exact ⟨l,(sat v l).mpr ⟨t,q,m,s,p,x,pair,hm,fq,cp0_mono_l sub comp,pp,px,xl⟩⟩
  have unique v l l' (hl : φ.denote ρ v l) (hl' : φ.denote ρ v l') : l = l' := by
    obtain ⟨t,q,m,s,p,x,pair,_,fq,comp,pp,px,xl⟩ := (sat v l).mp hl
    obtain ⟨t',q',m',s',p',x',pair',_,fq',comp',pp',px',xl'⟩ := (sat v l').mp hl'
    obtain ⟨et,eq⟩ := kpair_injective_l M pair pair'
    subst t' q'
    have em := fq'.domain_eq_l hZF.1 fq
    subst m'
    have es := cp0_unique_l hZF.1 fq eX comp' comp
    subst s'
    have ep := kpair_unique_l M hZF.1 pp' pp
    subst p'
    have ex := operations.1.2 p x' x px' px
    subst x'
    exact inj.1.1.2 x l l' xl xl'
  obtain ⟨F,ff,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := ω)
    total (fun v _ => unique v) (fun v l _ hl => by
      obtain ⟨_,_,_,_,_,x,_,_,_,_,_,_,xl⟩ := (sat v l).mp hl
      exact (fi.bound_l xl).2)
  classical
  by_cases inhabited : ∃ v, M.mem v D
  · obtain ⟨v,hv⟩ := inhabited
    obtain ⟨R,fr,retract⟩ := ZF.injection_retract_l I hZF index (fun _ h => h) hv
    have fr := fn0_of_function_l (ZF.modelsKP hZF) fr
    obtain ⟨u,compU⟩ := cp0_exists_l (ZF.modelsKP hZF) fr (fn0_of_function_l (ZF.modelsKP hZF) ff)
    refine ⟨u,compU.1,fun m t q v k l s p x hm ht fq pair vk _ kl _ comp pp lx => ?_⟩
    have vl : Rd_entry_d v l F := (compU.value_l fr (fn0_of_function_l (ZF.modelsKP hZF) ff) (retract v k vk)).mp kl
    obtain ⟨t',q',m',s',p',y,pair',_,fq',comp',pp',py,yl⟩ := (sat v l).mp ((entries v l).mp vl).2
    obtain ⟨et,eq⟩ := kpair_injective_l M pair' pair
    subst t' q'
    have em := fq'.domain_eq_l hZF.1 fq
    subst m'
    have es := cp0_unique_l hZF.1 fq eX comp' comp
    subst s'
    have ep := kpair_unique_l M hZF.1 pp' pp
    subst p'
    exact (fn0_function_l (ZF.modelsKP hZF) fe).1.2 l y x (section' y l yl) lx ▸ py
  · obtain ⟨z,_,hz⟩ := hw.1.1
    obtain ⟨u,fu,_⟩ := ZF.exists_constantFunction hZF I (source := ω) hz
    refine ⟨u,fn0_of_function_l (ZF.modelsKP hZF) fu,fun m t q v _ _ _ _ _ hm ht fq pair _ _ _ _ _ _ _ => ?_⟩
    exact (inhabited ⟨v,(tasks v).mpr ⟨t,ht,q,(space q).mpr ⟨m,hm,fn0_function_l (ZF.modelsKP hZF) fq⟩,pair⟩⟩).elim

end YesMetaZFC.SetTheory.Internal

/-! ## 闭包尝试的实际有限序列树

字母的两个实际坐标映射分别读出枚举值和见证位置。分离给出树集合，
坐标复合的前缀保持给出树闭性；无限枝的两个总图交由闭包解码定理读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Cl_word_d (ω X T J K Y d h p : M.Domain) : Prop := ∃ n e u,
  Fn0_d n Y p ∧ Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) d p e ∧
    Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) h p u ∧ Cl_node_d ω X T J K n e u

def cl_word_m {a} (ω X T J K Y d h p : Term a) : Formula 1 a := set[a] ⟪∃ n e u,
  ⌜fn0_m⌝ₚ(n,⌜Y⌝ₛ,⌜p⌝ₛ) ∧ ⌜(fseq_recode_m (𝒞 := kpair_convention_l))⌝ₚ(⌜d⌝ₛ,⌜p⌝ₛ,e) ∧
    ⌜(fseq_recode_m (𝒞 := kpair_convention_l))⌝ₚ(⌜h⌝ₛ,⌜p⌝ₛ,u) ∧
    ⌜cl_node_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜T⌝ₛ,⌜J⌝ₛ,⌜K⌝ₛ,n,e,u)⟫
derive_free_closed cl_word_m

theorem cl_word_sat_l {a} (ρ : Env M a) (ω X T J K Y d h p : Term a) :
    Formula.satisfies ρ (cl_word_m ω X T J K Y d h p) ↔
      Cl_word_d hZF (ω.eval ρ) (X.eval ρ) (T.eval ρ) (J.eval ρ) (K.eval ρ) (Y.eval ρ) (d.eval ρ) (h.eval ρ) (p.eval ρ) := by
  simp only [cl_word_m,Cl_word_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1,fseq_recode_sat_l I,cl_node_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem cl_tree_exists_l {ω X T J K Y d h F : M.Domain}
    (fd : M.IsSetFunctionFromTo I d Y X) (fh : M.IsSetFunctionFromTo I h Y ω)
    (space : Fseq_space_d I ω Y F) : ∃ A, Tree_d F A ∧
      ∀ p, M.mem p A ↔ Cl_word_d hZF ω X T J K Y d h p := by
  let ρ : Env M 8 := ⟨fun i => [ω,X,T,J,K,Y,d,h].get i,fun _ => ω⟩
  let φ : UnarySchema 8 := {
    body := cl_word_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) .newest }
  have sat p : φ.denote ρ p ↔ Cl_word_d hZF ω X T J K Y d h p := cl_word_sat_l hZF ..
  obtain ⟨A,sep⟩ := ZF.separation_exists_d hZF φ ρ F
  have nodes p : M.mem p A ↔ Cl_word_d hZF ω X T J K Y d h p := by
    rw [sep p]
    change (M.mem p F ∧ φ.denote ρ p) ↔ _
    rw [sat p]
    exact ⟨And.right,fun ⟨n,e,u,fp,de,hu,node⟩ =>
      ⟨(space p).mpr ⟨n,node.natural,fn0_function_l (ZF.modelsKP hZF) fp⟩,n,e,u,fp,de,hu,node⟩⟩
  refine ⟨A,⟨fun p hp => ((sep p).mp hp).1,fun p hp q hq sub => ?_⟩,nodes⟩
  obtain ⟨n,e,u,_,de,hu,node⟩ := (nodes p).mp hp
  obtain ⟨m,hm,fq⟩ := (space q).mp hq
  obtain ⟨e',fe',de'⟩ := ZF.fseq_compose_l I hZF fd fq
  obtain ⟨u',fu',hu'⟩ := ZF.fseq_compose_l I hZF fh fq
  exact (nodes q).mpr ⟨m,e',u',fn0_of_function_l (ZF.modelsKP hZF) fq,de',hu',
    node.prefix_l hm (fn0_of_function_l (ZF.modelsKP hZF) fe') (fn0_of_function_l (ZF.modelsKP hZF) fu')
      (de'.mono_l I de sub) (hu'.mono_l I hu sub)⟩

/-- 实际树枝恢复两个总图，以及一个真正可数且对原运算图闭合的值域。 -/
theorem cl_tree_closed_l {ω X T Q D J K Y d h F A f : M.Domain} (hw : M.IsOmega ω)
    (params : Fseq_space_d I ω ω Q) (tasks : M.IsCartesianProduct I D T Q)
    (index : Fn0_d D ω J) (operations : M.IsSetFunction I K)
    (fd : M.IsSetFunctionFromTo I d Y X) (fh : M.IsSetFunctionFromTo I h Y ω)
    (space : Fseq_space_d I ω Y F)
    (nodes : ∀ p, M.mem p A ↔ Cl_word_d hZF ω X T J K Y d h p)
    (ff : M.IsSetFunctionFromTo I f ω Y) (branch : Branch_d F A f) :
    ∃ e u N, Fn0_d ω X e ∧ Fn0_d ω ω u ∧ Fseq_recode_d I d f e ∧ Fseq_recode_d I h f u ∧
      M.IsRangeOf I N e ∧ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧ Fc_closed_d I ω T K N := by
  obtain ⟨e,fe,de⟩ := ZF.fseq_compose_l I hZF fd ff
  obtain ⟨u,fu,hu⟩ := ZF.fseq_compose_l I hZF fh ff
  have finite n (hn : M.mem n ω) : ∃ p q, Cl_node_d ω X T J K n p q ∧
      M.IsRestrictionOf I p e n ∧ M.IsRestrictionOf I q u n := by
    obtain ⟨s,fs,cut,_⟩ := ds_prefix_l I hZF hw ff hn
    have sub := (ds_restrict_iff_l I fs ff.1).mp cut
    obtain ⟨m,p,q,fm,dp,hq,node⟩ := (nodes s).mp (branch s ((space s).mpr ⟨n,hn,fs⟩) sub)
    have eq := fm.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fs)
    subst m
    exact ⟨p,q,node,(ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) node.enumeration) fe.1).mpr (dp.mono_l I de sub),
      (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) node.witnesses) fu.1).mpr (hq.mono_l I hu sub)⟩
  obtain ⟨N,range,sub,count,closed⟩ := cl_branch_closed_l hZF hw params tasks index operations
    (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fu) finite
  exact ⟨e,u,N,fn0_of_function_l (ZF.modelsKP hZF) fe,fn0_of_function_l (ZF.modelsKP hZF) fu,de,hu,range,sub,count,closed⟩

/-- 已完成的两个总图的每个有限前缀都通过原树检查。 -/
theorem cl_tree_branch_l {ω X T J K Y d h F A f e u : M.Domain}
    (fd : M.IsSetFunctionFromTo I d Y X) (fh : M.IsSetFunctionFromTo I h Y ω)
    (space : Fseq_space_d I ω Y F) (nodes : ∀ p, M.mem p A ↔ Cl_word_d hZF ω X T J K Y d h p)
    (ff : M.IsSetFunctionFromTo I f ω Y) (de : Fseq_recode_d I d f e) (hu : Fseq_recode_d I h f u)
    (run : Cl_at_d ω X T J K ω e u) : Branch_d F A f := by
  have fe := de.function_l I hZF fd ff
  intro p hp sub
  obtain ⟨n,hn,fp⟩ := (space p).mp hp
  obtain ⟨g,fg,dg⟩ := ZF.fseq_compose_l I hZF fd fp
  obtain ⟨v,fv,hv⟩ := ZF.fseq_compose_l I hZF fh fp
  exact (nodes p).mpr ⟨n,g,v,fn0_of_function_l (ZF.modelsKP hZF) fp,dg,hv,hn,
    fn0_of_function_l (ZF.modelsKP hZF) fg,fn0_of_function_l (ZF.modelsKP hZF) fv,
    run.prefix_l (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fg)
      (dg.mono_l I de sub) (hv.mono_l I hu sub)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 枚举值与见证位置的实际配对字母

构造两张坐标图，并将任意同长度的两个图合成一条配对字母列。
前缀与总枝使用同一构造，后续添加实数和泛型坐标时仍可复用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cl_pair_maps_l {X W Y : M.Domain} (pair : M.IsCartesianProduct I Y X W) :
    ∃ d h, M.IsSetFunctionFromTo I d Y X ∧ M.IsSetFunctionFromTo I h Y W ∧
      ∀ v x l, M.mem v Y → KPair_d M v x l → Rd_entry_d v x d ∧ Rd_entry_d v l h := by
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => Y⟩
  let φ (b : Bool) : BinarySchema 0 := {
    body := .existsE (if b then kpair0_m (.bound 2) (.bound 1) .newest else kpair0_m (.bound 2) .newest (.bound 1))
    freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have sat b v x : (φ b).denote ρ v x ↔ ∃ y, if b then KPair_d M v x y else KPair_d M v y x := by
    cases b <;> simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Bool.false_eq_true,↓reduceIte,kpair0_sat_l hZF.1] <;> rfl
  have make b : ∃ d, M.IsSetFunctionFromTo I d Y (if b then X else W) ∧
      ∀ v x, Rd_entry_d v x d ↔ M.mem v Y ∧ (φ b).denote ρ v x := by
    apply ZF.exists_setFunctionFromTo_of_denote hZF I (φ b) ρ
    · intro v hv
      obtain ⟨x,_,y,_,xy⟩ := (pair v).mp hv
      cases b
      · exact ⟨y,(sat false v y).mpr ⟨x,xy⟩⟩
      · exact ⟨x,(sat true v x).mpr ⟨y,xy⟩⟩
    · intro v _ x y hx hy
      obtain ⟨a,ha⟩ := (sat b v x).mp hx
      obtain ⟨c,hc⟩ := (sat b v y).mp hy
      cases b
      · exact (kpair_injective_l M ha hc).2
      · exact (kpair_injective_l M ha hc).1
    · intro v x hv hx
      obtain ⟨a,ha,c,hc,ac⟩ := (pair v).mp hv
      obtain ⟨y,xy⟩ := (sat b v x).mp hx
      cases b
      · exact (kpair_injective_l M ac xy).2 ▸ hc
      · exact (kpair_injective_l M ac xy).1 ▸ ha
  obtain ⟨d,fd,ed⟩ := make true
  obtain ⟨h,fh,eh⟩ := make false
  exact ⟨d,h,fd,fh,fun v x l hv pair =>
    ⟨(ed v x).mpr ⟨hv,(sat true v x).mpr ⟨l,pair⟩⟩,(eh v l).mpr ⟨hv,(sat false v l).mpr ⟨x,pair⟩⟩⟩⟩

theorem cl_pair_word_l {X W Y d h n e u : M.Domain} (pair : M.IsCartesianProduct I Y X W)
    (fd : M.IsSetFunctionFromTo I d Y X) (fh : M.IsSetFunctionFromTo I h Y W)
    (read : ∀ v x l, M.mem v Y → KPair_d M v x l → Rd_entry_d v x d ∧ Rd_entry_d v l h)
    (fe : Fn0_d n X e) (fu : Fn0_d n W u) :
    ∃ f, M.IsSetFunctionFromTo I f n Y ∧ Fseq_recode_d I d f e ∧ Fseq_recode_d I h f u := by
  let ρ : Env M 2 := ⟨Fin.cases e (fun _ => u),fun _ => e⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ x l,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,x,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,l,⌜(.bound 3 : Term 4)⌝ₛ) ∧
    ⌜kpair0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,x,l)⟫ }
  have sat i v : φ.denote ρ i v ↔ ∃ x l, Rd_entry_d i x e ∧ Rd_entry_d i l u ∧ KPair_d M v x l := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,kpair0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨f,ff,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := Y)
    (fun i hi => by
      obtain ⟨x,_,ix⟩ := fe.2.1 i hi
      obtain ⟨l,_,il⟩ := fu.2.1 i hi
      obtain ⟨v,xy⟩ := (I).total x l
      exact ⟨v,(sat i v).mpr ⟨x,l,ix,il,xy⟩⟩)
    (fun i _ v w hv hw => by
      obtain ⟨x,l,ix,il,pv⟩ := (sat i v).mp hv
      obtain ⟨y,k,iy,ik,pw⟩ := (sat i w).mp hw
      have ex := (fn0_function_l (ZF.modelsKP hZF) fe).1.2 i y x iy ix
      have el := (fn0_function_l (ZF.modelsKP hZF) fu).1.2 i k l ik il
      subst y k
      exact kpair_unique_l M hZF.1 pv pw)
    (fun i v _ hv => by
      obtain ⟨x,l,ix,il,pv⟩ := (sat i v).mp hv
      exact (pair v).mpr ⟨x,(fe.bound_l ix).2,l,(fu.bound_l il).2,pv⟩)
  have lift i x l (ix : Rd_entry_d i x e) (il : Rd_entry_d i l u) :
      ∃ v, Rd_entry_d i v f ∧ Rd_entry_d v x d ∧ Rd_entry_d v l h := by
    obtain ⟨v,pv⟩ := (I).total x l
    have iv := (entries i v).mpr ⟨(fe.bound_l ix).1,(sat i v).mpr ⟨x,l,ix,il,pv⟩⟩
    exact ⟨v,iv,read v x l (ff.output_mem_of_pairMember iv) pv⟩
  refine ⟨f,ff,⟨(fn0_function_l (ZF.modelsKP hZF) fe).1.1,fun i x => ⟨?_,?_⟩⟩,
    ⟨(fn0_function_l (ZF.modelsKP hZF) fu).1.1,fun i l => ⟨?_,?_⟩⟩⟩
  · intro ix
    obtain ⟨l,_,il⟩ := fu.2.1 i (fe.bound_l ix).1
    obtain ⟨v,iv,vx,_⟩ := lift i x l ix il
    exact ⟨v,iv,vx⟩
  · rintro ⟨v,iv,vx⟩
    obtain ⟨y,l,iy,il,pv⟩ := (sat i v).mp ((entries i v).mp iv).2
    exact fd.1.2 v y x (read v y l (ff.output_mem_of_pairMember iv) pv).1 vx ▸ iy
  · intro il
    obtain ⟨x,_,ix⟩ := fe.2.1 i (fu.bound_l il).1
    obtain ⟨v,iv,_,vl⟩ := lift i x l ix il
    exact ⟨v,iv,vl⟩
  · rintro ⟨v,iv,vl⟩
    obtain ⟨x,k,ix,ik,pv⟩ := (sat i v).mp ((entries i v).mp iv).2
    exact fh.1.2 v k l (read v x k (ff.output_mem_of_pairMember iv) pv).2 vl ▸ ik

end YesMetaZFC.SetTheory.Internal
