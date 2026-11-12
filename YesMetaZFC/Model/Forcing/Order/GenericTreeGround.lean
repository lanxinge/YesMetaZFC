import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.SetTheory.Card.PowerBound
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.Model.SetTheory.EnumeratedChoice
import YesMetaZFC.SetTheory.FunctionCoordinates
import YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative
import YesMetaZFC.Model.SetTheory.Internal.ClosureLetters
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 全部旧全局稠密集的实际集合与幂集编码

从条件域的幂集分离稠密集族；条件域的单射经直接像提升为幂集单射。
编码界针对旧稠密集族，不涉及扩张中新产生的稠密集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include hZF

theorem dense_family_l (Q T z : M.Domain) : ∃ D, ∀ E, M.mem E D ↔ Dense_set_d M Q T z E := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF Q
  let ρ : Env M 3 := ⟨fun i => [Q,T,z].get i,fun _ => Q⟩
  let φ : UnarySchema 3 := { body := dense_set_m (.bound 1) (.bound 2) (.bound 3) .newest }
  have sat E : φ.denote ρ E ↔ Dense_set_d M Q T z E := dense_set_sat_l M hZF.1 ..
  obtain ⟨D,read⟩ := ZF.separation_exists_d hZF φ ρ P
  exact ⟨D,fun E => (read E).trans ⟨fun h => (sat E).mp h.2,
    fun h => ⟨(power E).mpr (fun q hq => (h.1 q hq).1),(sat E).mpr h⟩⟩⟩

theorem dense_family_bound_l {Q T z D δ P : M.Domain}
    (family : ∀ E, M.mem E D → Dense_set_d M Q T z E)
    (power : M.IsPowerSetOf P δ) (small : M.CardinalLessOrEqual I Q δ) : M.CardinalLessOrEqual I D P := by
  obtain ⟨W,sets⟩ := ZF.exists_powerSet hZF Q
  obtain ⟨i,fi⟩ := ZF.exists_inclusionInjection hZF I
    (fun E hE => (sets E).mpr (fun q hq => ((family E hE).1 q hq).1))
  obtain ⟨f,ff⟩ := small
  obtain ⟨g,fg⟩ := ZF.power_injection_l I hZF sets power ff
  exact ZF.exists_compositionInjection hZF I fi fg

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部递降条件列生成的实际滤子

先用可定义关系的内部归纳传播全部加强关系，再分离上闭包。
指定集合族被原列命中时，生成滤子对该同一族满足泛型集合公式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem sequence_filter_l {ω Q T D f : M.Domain} (O : Cond_order_d M Q T Q)
    (hw : M.IsOmega ω) (ff : M.IsSetFunctionFromTo I f ω Q)
    (step : ∀ i j p q, M.SuccessorOf j i → Entry_d M i p f → Entry_d M j q f → Entry_d M q p T)
    (hits : ∀ E, M.mem E D → ∃ i p, Entry_d M i p f ∧ M.mem p E) :
    ∃ H, (∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ i q, Entry_d M i q f ∧ Entry_d M q p T) ∧
      Gset_d Q T Q D H ∧
      ∀ p q, M.mem p H → M.mem q H → ∃ i r, Entry_d M i r f ∧ Entry_d M r p T ∧ Entry_d M r q T := by
  let ρ : Env M 1 := ⟨fun _ => T,fun _ => T⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have sat p q : φ.denote ρ p q ↔ Entry_d M q p T := entry_sat_l M hZF.1 ..
  have chain i j p q (ij : M.mem i j) (ip : Entry_d M i p f) (jq : Entry_d M j q f) : Entry_d M q p T :=
    (sat p q).mp (ZF.rel_chain_l I hZF φ ρ hw ff
      (fun p q r hp hq hr pq qr => (sat p r).mpr (O.trans r q p hr hq hp ((sat q r).mp qr) ((sat p q).mp pq)))
      (fun i j p q succ ip jq => (sat p q).mpr (step i j p q succ ip jq)) i j p q ij ip jq)
  have merge {i j p q} (ip : Entry_d M i p f) (jq : Entry_d M j q f) :
      ∃ k r, Entry_d M k r f ∧ Entry_d M r p T ∧ Entry_d M r q T := by
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i (ff.input_mem_of_pairMember ip)
        j (ff.input_mem_of_pairMember jq) with eq | ij | ji
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      have eq := ff.1.2 i q p jq ip
      subst q
      exact ⟨i,p,ip,O.refl p (ff.output_mem_of_pairMember ip),O.refl p (ff.output_mem_of_pairMember ip)⟩
    · exact ⟨j,q,jq,chain i j p q ij ip jq,O.refl q (ff.output_mem_of_pairMember jq)⟩
    · exact ⟨i,p,ip,O.refl p (ff.output_mem_of_pairMember ip),chain j i q p ji jq ip⟩
  let η : Env M 2 := ⟨Fin.cases f (fun _ => T),fun _ => f⟩
  let ψ : UnarySchema 2 := { body := set[3] ⟪∃ i q,
    ⌜entry_m⌝ₚ(i,q,⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜entry_m⌝ₚ(q,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have spec p : ψ.denote η p ↔ ∃ i q, Entry_d M i q f ∧ Entry_d M q p T := by
    simp only [UnarySchema.denote,ψ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨H,sep⟩ := ZF.separation_exists_d hZF ψ η Q
  have members p := (sep p).trans (and_congr_right fun _ => spec p)
  have includes {i p} (ip : Entry_d M i p f) : M.mem p H :=
    (members p).mpr ⟨ff.output_mem_of_pairMember ip,i,p,ip,O.refl p (ff.output_mem_of_pairMember ip)⟩
  -- 公共加强仍是原列中的实际一项，后续可将它登记回同一个初等壳。
  have generated p q (hp : M.mem p H) (hq : M.mem q H) :
      ∃ i r, Entry_d M i r f ∧ Entry_d M r p T ∧ Entry_d M r q T := by
    obtain ⟨hp,i,r,ir,rp⟩ := (members p).mp hp
    obtain ⟨hq,j,s,js,sq⟩ := (members q).mp hq
    obtain ⟨k,t,kt,tr,ts⟩ := merge ir js
    exact ⟨k,t,kt,
      O.trans t r p (ff.output_mem_of_pairMember kt) (ff.output_mem_of_pairMember ir) hp tr rp,
      O.trans t s q (ff.output_mem_of_pairMember kt) (ff.output_mem_of_pairMember js) hq ts sq⟩
  refine ⟨H,members,⟨?_,?_,?_,?_,?_⟩,generated⟩
  · intro p hp
    exact ⟨((members p).mp hp).1,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ ((members p).mp hp).1)⟩
  · obtain ⟨i,_,hi⟩ := hw.1.1
    obtain ⟨p,_,ip⟩ := ff.2.2 i hi
    exact ⟨p,includes ip⟩
  · intro p q hp hq pq
    obtain ⟨hp,i,r,ir,rp⟩ := (members p).mp hp
    exact (members q).mpr ⟨hq,i,r,ir,O.trans r p q (ff.output_mem_of_pairMember ir) hp hq rp pq⟩
  · intro p q hp hq
    obtain ⟨k,t,kt,tp,tq⟩ := generated p q hp hq
    exact ⟨t,includes kt,tp,tq⟩
  · intro _ _ E hE _
    obtain ⟨i,p,ip,pE⟩ := hits E hE
    exact ⟨p,includes ip,pE⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部可数稠密集族的实际滤子

DC 作用于 (轮号,条件) 的集合状态。实际一阶公式的内部归纳识别轮号，
稠密对象在下一步命中，其他对象允许原条件不变。保留整条递降列和逐轮
命中方程，再由上闭包构造原可数稠密族的实际滤子。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem countable_run_l {ω Q T X e p₀ : M.Domain} (O : Cond_order_d M Q T Q)
    (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (ef : M.IsSetFunctionFromTo I e ω X) (hp₀ : M.mem p₀ Q) :
    ∃ f, M.IsSetFunctionFromTo I f ω Q ∧
      (∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀ f) ∧
      ∀ i j p q, M.SuccessorOf j i → Entry_d M i p f → Entry_d M j q f →
        Entry_d M q p T ∧ ∀ E, Entry_d M i E e → Dense_set_d M Q T Q E → M.mem q E := by
  let ρ : Env M 2 := ⟨fun i => [Q,T].get i,fun _ => Q⟩
  let φ : UnarySchema 4 := {
    body := .conj (entry_m .newest (.bound 2) (.bound 4))
      (.imp (dense_set_m (.bound 3) (.bound 4) (.bound 3) (.bound 1)) (.mem .newest (.bound 1))) }
  have sat p a q : φ.denote ((ρ.push p).push a) q ↔
      Entry_d M q p T ∧ (Dense_set_d M Q T Q a → M.mem q a) := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,entry_sat_l M hZF.1,dense_set_sat_l M hZF.1]
    rfl
  obtain ⟨f,ff,zero,step⟩ := dc.parameter_l I hZF hw φ ρ ef hp₀ (by
    intro p a hp _
    rcases Classical.em (Dense_set_d M Q T Q a) with dense | no
    · obtain ⟨q,qp,qa⟩ := dense.2 p hp (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hp))
      exact ⟨q,qp.1,(sat p a q).mpr ⟨qp.2.2,fun _ => qa⟩⟩
    · exact ⟨p,hp,(sat p a p).mpr ⟨O.refl p hp,fun h => (no h).elim⟩⟩)
  refine ⟨f,ff,zero,fun i j p q succ ip jq => ?_⟩
  obtain ⟨a,_,ia⟩ := ef.2.2 i (ff.input_mem_of_pairMember ip)
  exact ⟨((sat p a q).mp (step i j p q succ ip jq a ia)).1,
    fun E iE => ((sat p E q).mp (step i j p q succ ip jq E iE)).2⟩

theorem countable_filter_l {ω Q T D e p₀ : M.Domain} (O : Cond_order_d M Q T Q)
    (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (dense : ∀ E, M.mem E D → Dense_set_d M Q T Q E)
    (ef : M.IsSetFunctionFromTo I e ω D) (onto : M.IsSetSurjectiveOnto I e ω D)
    (hp₀ : M.mem p₀ Q) : ∃ H, M.mem p₀ H ∧ Gset_d Q T Q D H := by
  obtain ⟨f,ff,zero,step⟩ := countable_run_l hZF O hw dc ef hp₀
  obtain ⟨H,members,filter,_⟩ := sequence_filter_l hZF O hw ff
    (fun i j p q succ ip jq => (step i j p q succ ip jq).1) (by
      intro E hE
      obtain ⟨i,hi,iE⟩ := onto E hE
      obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
      obtain ⟨p,_,ip⟩ := ff.2.2 i hi
      obtain ⟨q,_,jq⟩ := ff.2.2 j hj
      exact ⟨j,q,jq,(step i j p q succ ip jq).2 E iE (dense E hE)⟩)
  obtain ⟨o,empty,_⟩ := hw.1.1
  exact ⟨H,(members p₀).mpr ⟨hp₀,o,p₀,zero o empty,O.refl p₀ hp₀⟩,filter⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 递降条件和稠密命中位置的有限尝试

枚举 e 可包含任意对象。u(i) 指定第 i 项的命中位置；仅在 i 与 u(i) 都可见时
检查稠密要求。有限节点严格保持前缀，而每个任务在总枝上最终受检。
DC 的实际运行给出相同格式的见证，采用下一轮作为命中位置。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

structure Gn_at_d (Q T n e f u : M.Domain) : Prop where
  decreasing : ∀ i j p q, M.mem i n → M.mem j n → M.SuccessorOf j i →
    Entry_d M i p f → Entry_d M j q f → Entry_d M q p T
  hits : ∀ i k D p, M.mem i n → M.mem k n → Entry_d M i D e → Entry_d M i k u →
    Entry_d M k p f → Dense_set_d M Q T Q D → M.mem p D

def gn_at_m {a} (Q T n e f u : Term a) : Formula 1 a := .conj
  (set[a] ⟪∀ i j p q, i ∈ ⌜n⌝ₛ → j ∈ ⌜n⌝ₛ → ⌜Formula.isSuccessor⌝ₚ(j,i) →
    ⌜entry_m⌝ₚ(i,p,⌜f⌝ₛ) → ⌜entry_m⌝ₚ(j,q,⌜f⌝ₛ) → ⌜entry_m⌝ₚ(q,p,⌜T⌝ₛ)⟫)
  (set[a] ⟪∀ i k D p, i ∈ ⌜n⌝ₛ → k ∈ ⌜n⌝ₛ → ⌜entry_m⌝ₚ(i,D,⌜e⌝ₛ) →
    ⌜entry_m⌝ₚ(i,k,⌜u⌝ₛ) → ⌜entry_m⌝ₚ(k,p,⌜f⌝ₛ) → ⌜dense_set_m⌝ₚ(⌜Q⌝ₛ,⌜T⌝ₛ,⌜Q⌝ₛ,D) → p ∈ D⟫)
derive_free_closed gn_at_m

theorem gn_at_sat_l (hE : Extensional M) {a} (ρ : Env M a) (Q T n e f u : Term a) :
    Formula.satisfies ρ (gn_at_m Q T n e f u) ↔ Gn_at_d (Q.eval ρ) (T.eval ρ) (n.eval ρ) (e.eval ρ) (f.eval ρ) (u.eval ρ) := by
  simp only [gn_at_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,entry_sat_l M hE,dense_set_sat_l M hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b⟩ => ⟨a,b⟩,fun h => ⟨h.decreasing,h.hits⟩⟩

structure Gn_node_d (ω X Q T n e f u : M.Domain) : Prop where
  natural : M.mem n ω
  enumeration : Fn0_d n X e
  conditions : Fn0_d n Q f
  witnesses : Fn0_d n ω u
  check : Gn_at_d Q T n e f u

def gn_node_m {a} (ω X Q T n e f u : Term a) : Formula 1 a :=
  .conj (.mem n ω) (.conj (fn0_m n X e) (.conj (fn0_m n Q f) (.conj (fn0_m n ω u) (gn_at_m Q T n e f u))))
derive_free_closed gn_node_m

theorem gn_node_sat_l (hE : Extensional M) {a} (ρ : Env M a) (ω X Q T n e f u : Term a) :
    Formula.satisfies ρ (gn_node_m ω X Q T n e f u) ↔
      Gn_node_d (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (n.eval ρ) (e.eval ρ) (f.eval ρ) (u.eval ρ) := by
  simp only [gn_node_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,fn0_sat_l hE,gn_at_sat_l hE]
  exact ⟨fun ⟨a,b,c,d,h⟩ => ⟨a,b,c,d,h⟩,fun h => ⟨h.natural,h.enumeration,h.conditions,h.witnesses,h.check⟩⟩

theorem Gn_at_d.prefix_l {Q T n m e f u e' f' u' : M.Domain} (h : Gn_at_d Q T m e f u)
    (sub : M.MemberSubset n m) (ee : M.MemberSubset e' e) (ff : M.MemberSubset f' f) (uu : M.MemberSubset u' u) :
    Gn_at_d Q T n e' f' u' := by
  have move {F G a b : M.Domain} (sub : M.MemberSubset F G) (ab : Entry_d M a b F) : Entry_d M a b G :=
    ab.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  exact ⟨fun i j p q hi hj succ ip jq => h.decreasing i j p q (sub i hi) (sub j hj) succ (move ff ip) (move ff jq),
    fun i k D p hi hk iD ik kp dense => h.hits i k D p (sub i hi) (sub k hk) (move ee iD) (move uu ik) (move ff kp) dense⟩

theorem Gn_node_d.prefix_l {ω X Q T n m e f u e' f' u' : M.Domain} (h : Gn_node_d ω X Q T m e f u)
    (hn : M.mem n ω) (en : Fn0_d n X e') (fn : Fn0_d n Q f') (un : Fn0_d n ω u')
    (ee : M.MemberSubset e' e) (ff : M.MemberSubset f' f) (uu : M.MemberSubset u' u) : Gn_node_d ω X Q T n e' f' u' := by
  have sub : M.MemberSubset n m := fun i hi => by
    obtain ⟨x,_,p,pair,hp⟩ := en.2.1 i hi
    exact (h.enumeration.bound_l ⟨p,pair,ee p hp⟩).1
  exact ⟨hn,en,fn,un,h.check.prefix_l sub ee ff uu⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个命中位置均为内部自然数，所以一个足够长的节点核验该稠密任务。 -/
theorem gn_branch_run_l {ω X Q T e f u : M.Domain} (hw : M.IsOmega ω)
    (branch : ∀ n, M.mem n ω → ∃ a b c, Gn_node_d ω X Q T n a b c ∧
      M.IsRestrictionOf I a e n ∧ M.IsRestrictionOf I b f n ∧ M.IsRestrictionOf I c u n) :
    Gn_at_d Q T ω e f u := by
  constructor
  · intro i j p q hi hj succ ip jq
    obtain ⟨n,hn,hin,hjn⟩ := at_upper_l hZF hw hi hj
    obtain ⟨a,b,c,node,_,cut,_⟩ := branch n hn
    exact node.check.decreasing i j p q hin hjn succ ((cut.2 i p).mpr ⟨hin,ip⟩) ((cut.2 j q).mpr ⟨hjn,jq⟩)
  · intro i k D p hi hk iD ik kp dense
    obtain ⟨n,hn,hin,hkn⟩ := at_upper_l hZF hw hi hk
    obtain ⟨a,b,c,node,ce,cf,cu⟩ := branch n hn
    exact node.check.hits i k D p hin hkn ((ce.2 i D).mpr ⟨hin,iD⟩)
      ((cu.2 i k).mpr ⟨hin,ik⟩) ((cf.2 k p).mpr ⟨hkn,kp⟩) dense

/-- 实际逐轮命中方程产生内部自然数命中表，采用下一轮为截止位置。 -/
theorem gn_deadline_l {ω Q T e f : M.Domain} (hw : M.IsOmega ω) (ff : M.IsSetFunctionFromTo I f ω Q)
    (step : ∀ i j p q, M.SuccessorOf j i → Entry_d M i p f → Entry_d M j q f →
      Entry_d M q p T ∧ ∀ E, Entry_d M i E e → Dense_set_d M Q T Q E → M.mem q E) :
    ∃ u, Fn0_d ω ω u ∧ Gn_at_d Q T ω e f u := by
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  let φ : BinarySchema 0 := { body := Formula.isSuccessor .newest (.bound 1) }
  have sat i k : φ.denote ρ i k ↔ M.SuccessorOf k i := Formula.satisfies_isSuccessor_iff ..
  obtain ⟨u,fu,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun i hi => (hw.1.2 i hi).imp fun k hk => (sat i k).mpr hk.1)
    (fun _ _ _ _ a b => ((sat ..).mp a).eq hZF.1 ((sat ..).mp b))
    (fun i k hi hk => by
      obtain ⟨l,succ,hl⟩ := hw.1.2 i hi
      exact succ.eq hZF.1 ((sat i k).mp hk) ▸ hl)
  refine ⟨u,fn0_of_function_l (ZF.modelsKP hZF) fu,⟨?_,?_⟩⟩
  · exact fun i j p q _ _ succ ip jq => (step i j p q succ ip jq).1
  · intro i k D p hi _ iD ik kp dense
    obtain ⟨q,_,iq⟩ := ff.2.2 i hi
    exact (step i k q p ((sat i k).mp ((entries i k).mp ik).2) iq kp).2 D iD dense

/-- 原 DC 工厂直接生产合法总列和命中表，不假定调度成功。 -/
theorem gn_run_exists_l {ω X Q T e p₀ : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (O : Cond_order_d M Q T Q) (fe : M.IsSetFunctionFromTo I e ω X) (hp₀ : M.mem p₀ Q) :
    ∃ f u, Fn0_d ω Q f ∧ Fn0_d ω ω u ∧ Gn_at_d Q T ω e f u ∧
      ∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀ f := by
  obtain ⟨f,ff,zero,step⟩ := countable_run_l hZF O hw dc fe hp₀
  obtain ⟨u,fu,run⟩ := gn_deadline_l hZF hw ff step
  exact ⟨f,u,fn0_of_function_l (ZF.modelsKP hZF) ff,fu,run,zero⟩

/-- 对枚举值域中的全部全局稠密集同时泛型；输出稠密族和滤子都是实际集合。 -/
theorem gn_run_filter_l {ω X Q T e f u : M.Domain} (hw : M.IsOmega ω) (O : Cond_order_d M Q T Q)
    (fe : Fn0_d ω X e) (ff : Fn0_d ω Q f) (fu : Fn0_d ω ω u) (run : Gn_at_d Q T ω e f u) :
    ∃ N D H, M.IsRangeOf I N e ∧ (∀ E, M.mem E D ↔ M.mem E N ∧ Dense_set_d M Q T Q E) ∧
      (∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ i q, Entry_d M i q f ∧ Entry_d M q p T) ∧ Gset_d Q T Q D H ∧
      ∀ p q, M.mem p H → M.mem q H → ∃ i r, Entry_d M i r f ∧ Entry_d M r p T ∧ Entry_d M r q T := by
  have fe := fn0_function_l (ZF.modelsKP hZF) fe
  obtain ⟨N,range⟩ := ZF.exists_range_of_setFunction hZF I fe.1 fe.2.1
  let ρ : Env M 2 := ⟨fun i => [Q,T].get i,fun _ => Q⟩
  let φ : UnarySchema 2 := { body := dense_set_m (.bound 1) (.bound 2) (.bound 1) .newest }
  obtain ⟨D,sep⟩ := ZF.separation_exists_d hZF φ ρ N
  have members E : M.mem E D ↔ M.mem E N ∧ Dense_set_d M Q T Q E :=
    (sep E).trans (and_congr_right fun _ => dense_set_sat_l M hZF.1 ..)
  obtain ⟨H,filter,gen,generated⟩ := sequence_filter_l hZF O hw (fn0_function_l (ZF.modelsKP hZF) ff)
    (fun i j p q succ ip jq => run.decreasing i j p q (ff.bound_l ip).1 (ff.bound_l jq).1 succ ip jq) (D := D) (by
      intro E hE
      obtain ⟨hE,dense⟩ := (members E).mp hE
      obtain ⟨i,iE⟩ := (range E).mp hE
      obtain ⟨k,hk,ik⟩ := fu.2.1 i (fe.input_mem_of_pairMember iE)
      obtain ⟨p,_,kp⟩ := ff.2.1 k hk
      exact ⟨k,p,kp,run.hits i k E p (fe.input_mem_of_pairMember iE) hk iE ik kp dense⟩)
  exact ⟨N,D,H,range,members,filter,gen,generated⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 枚举、递降条件和命中位置组成的实际树

字母为 X × (Q × ω)，四张实际投影图读取三个坐标。原节点公式经分离生成树，
无限枝的每项稠密任务最终受检；DC 工厂反向产生具有指定枚举坐标的合法枝。
这里尚不要求条件属于枚举值域，该要求须在子模型泛型树中另行登记。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Gn_word_d (ω X Q T Y d h l r p : M.Domain) : Prop := ∃ n e b f u,
  Fn0_d n Y p ∧ Fseq_recode_d I d p e ∧ Fseq_recode_d I h p b ∧
    Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u ∧ Gn_node_d ω X Q T n e f u

def gn_word_m {a} (ω X Q T Y d h l r p : Term a) : Formula 1 a := set[a] ⟪∃ n e b f u,
  ⌜fn0_m⌝ₚ(n,⌜Y⌝ₛ,⌜p⌝ₛ) ∧ ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜d⌝ₛ,⌜p⌝ₛ,e) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜h⌝ₛ,⌜p⌝ₛ,b) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜l⌝ₛ,b,f) ∧ ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜r⌝ₛ,b,u) ∧
  ⌜gn_node_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,n,e,f,u)⟫
derive_free_closed gn_word_m

theorem gn_word_sat_l {a} (ρ : Env M a) (ω X Q T Y d h l r p : Term a) :
    Formula.satisfies ρ (gn_word_m ω X Q T Y d h l r p) ↔
      Gn_word_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (Y.eval ρ)
        (d.eval ρ) (h.eval ρ) (l.eval ρ) (r.eval ρ) (p.eval ρ) := by
  simp only [gn_word_m,Gn_word_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1,fseq_recode_sat_l I,gn_node_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

structure Gn_tree_d (ω X Q T Z Y d h l r F A : M.Domain) : Prop where
  inner : M.IsCartesianProduct I Z Q ω
  outer : M.IsCartesianProduct I Y X Z
  left : M.IsSetFunctionFromTo I d Y X
  right : M.IsSetFunctionFromTo I h Y Z
  condition : M.IsSetFunctionFromTo I l Z Q
  witness : M.IsSetFunctionFromTo I r Z ω
  inner_read : ∀ v p k, M.mem v Z → KPair_d M v p k → Entry_d M v p l ∧ Entry_d M v k r
  outer_read : ∀ v x b, M.mem v Y → KPair_d M v x b → Entry_d M v x d ∧ Entry_d M v b h
  sequences : Fseq_space_d I ω Y F
  tree : Tree_d F A
  nodes : ∀ p, M.mem p A ↔ Gn_word_d hZF ω X Q T Y d h l r p

theorem gn_tree_exists_l {ω : M.Domain} (hw : M.IsOmega ω) (X Q T : M.Domain) :
    ∃ Z Y d h l r F A, Gn_tree_d hZF ω X Q T Z Y d h l r F A := by
  obtain ⟨Z,inner⟩ := ZF.exists_cartesianProduct hZF I Q ω
  obtain ⟨Y,outer⟩ := ZF.exists_cartesianProduct hZF I X Z
  obtain ⟨l,r,fl,fr,read₁⟩ := cl_pair_maps_l hZF inner
  obtain ⟨d,h,fd,fh,read₂⟩ := cl_pair_maps_l hZF outer
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw Y
  let ρ : Env M 9 := ⟨fun i => [ω,X,Q,T,Y,d,h,l,r].get i,fun _ => ω⟩
  let φ : UnarySchema 9 := {
    body := gn_word_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest }
  have sat p : φ.denote ρ p ↔ Gn_word_d hZF ω X Q T Y d h l r p := gn_word_sat_l hZF ..
  obtain ⟨A,sep⟩ := ZF.separation_exists_d hZF φ ρ F
  have nodes p : M.mem p A ↔ Gn_word_d hZF ω X Q T Y d h l r p := by
    rw [sep p]
    change (M.mem p F ∧ φ.denote ρ p) ↔ _
    rw [sat p]
    exact ⟨And.right,fun ⟨n,e,b,f,u,fp,de,hb,lf,ru,node⟩ =>
      ⟨(space p).mpr ⟨n,node.natural,fn0_function_l (ZF.modelsKP hZF) fp⟩,n,e,b,f,u,fp,de,hb,lf,ru,node⟩⟩
  refine ⟨Z,Y,d,h,l,r,F,A,inner,outer,fd,fh,fl,fr,read₁,read₂,space,⟨fun p hp => ((sep p).mp hp).1,?_⟩,nodes⟩
  intro p hp q hq sub
  obtain ⟨_,e,b,f,u,_,de,hb,lf,ru,node⟩ := (nodes p).mp hp
  obtain ⟨n,hn,fq⟩ := (space q).mp hq
  obtain ⟨e',fe',de'⟩ := ZF.fseq_compose_l I hZF fd fq
  obtain ⟨b',fb',hb'⟩ := ZF.fseq_compose_l I hZF fh fq
  obtain ⟨f',ff',lf'⟩ := ZF.fseq_compose_l I hZF fl fb'
  obtain ⟨u',fu',ru'⟩ := ZF.fseq_compose_l I hZF fr fb'
  have bb := hb'.mono_l I hb sub
  exact (nodes q).mpr ⟨n,e',b',f',u',fn0_of_function_l (ZF.modelsKP hZF) fq,de',hb',lf',ru',
    node.prefix_l hn (fn0_of_function_l (ZF.modelsKP hZF) fe') (fn0_of_function_l (ZF.modelsKP hZF) ff')
      (fn0_of_function_l (ZF.modelsKP hZF) fu') (de'.mono_l I de sub) (lf'.mono_l I lf bb) (ru'.mono_l I ru bb)⟩

/-- 新无限枝逐坐标给出真实总图，并自动完成全部已枚举稠密任务。 -/
theorem Gn_tree_d.run_l {ω X Q T Z Y d h l r F A p : M.Domain}
    (tree : Gn_tree_d hZF ω X Q T Z Y d h l r F A) (hw : M.IsOmega ω)
    (fp : M.IsSetFunctionFromTo I p ω Y) (branch : Branch_d F A p) :
    ∃ e b f u, Fn0_d ω X e ∧ Fn0_d ω Q f ∧ Fn0_d ω ω u ∧ Fseq_recode_d I d p e ∧
      Fseq_recode_d I h p b ∧ Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u ∧ Gn_at_d Q T ω e f u := by
  obtain ⟨e,fe,de⟩ := ZF.fseq_compose_l I hZF tree.left fp
  obtain ⟨b,fb,hb⟩ := ZF.fseq_compose_l I hZF tree.right fp
  obtain ⟨f,ff,lf⟩ := ZF.fseq_compose_l I hZF tree.condition fb
  obtain ⟨u,fu,ru⟩ := ZF.fseq_compose_l I hZF tree.witness fb
  refine ⟨e,b,f,u,fn0_of_function_l (ZF.modelsKP hZF) fe,fn0_of_function_l (ZF.modelsKP hZF) ff,
    fn0_of_function_l (ZF.modelsKP hZF) fu,de,hb,lf,ru,gn_branch_run_l hZF (X := X) hw ?_⟩
  intro n hn
  obtain ⟨q,fq,cut,_⟩ := ds_prefix_l I hZF hw fp hn
  have sub := (ds_restrict_iff_l I fq fp.1).mp cut
  obtain ⟨m,a,b',g,v,fm,da,hb',lg,rv,node⟩ := (tree.nodes q).mp
    (branch q ((tree.sequences q).mpr ⟨n,hn,fq⟩) sub)
  have eq := fm.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fq)
  subst m
  have bb := hb'.mono_l I hb sub
  exact ⟨a,g,v,node,(ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) node.enumeration) fe.1).mpr (da.mono_l I de sub),
    (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) node.conditions) ff.1).mpr (lg.mono_l I lf bb),
    (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) node.witnesses) fu.1).mpr (rv.mono_l I ru bb)⟩

/-- 任意实际合法总运行都能编码成原树的枝，枚举坐标逐点不变。 -/
theorem Gn_tree_d.of_run_l {ω X Q T Z Y d h l r F A e f u : M.Domain}
    (tree : Gn_tree_d hZF ω X Q T Z Y d h l r F A)
    (fe : Fn0_d ω X e) (ff : Fn0_d ω Q f) (fu : Fn0_d ω ω u) (run : Gn_at_d Q T ω e f u) :
    ∃ p b, M.IsSetFunctionFromTo I p ω Y ∧ Branch_d F A p ∧ Fseq_recode_d I d p e ∧
      Fseq_recode_d I h p b ∧ Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u := by
  obtain ⟨b,fb,lf,ru⟩ := cl_pair_word_l hZF tree.inner tree.condition tree.witness tree.inner_read ff fu
  obtain ⟨p,fp,de,hb⟩ := cl_pair_word_l hZF tree.outer tree.left tree.right tree.outer_read fe (fn0_of_function_l (ZF.modelsKP hZF) fb)
  refine ⟨p,b,fp,?_,de,hb,lf,ru⟩
  intro q hq sub
  obtain ⟨n,hn,fq⟩ := (tree.sequences q).mp hq
  obtain ⟨a,fa,da⟩ := ZF.fseq_compose_l I hZF tree.left fq
  obtain ⟨b',fb',hb'⟩ := ZF.fseq_compose_l I hZF tree.right fq
  obtain ⟨g,fg,lg⟩ := ZF.fseq_compose_l I hZF tree.condition fb'
  obtain ⟨v,fv,rv⟩ := ZF.fseq_compose_l I hZF tree.witness fb'
  have bb := hb'.mono_l I hb sub
  have ee := da.mono_l I de sub
  have nω : M.MemberSubset n ω := fun i hi => by
    obtain ⟨x,_,s,pair,hs⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fa).2.1 i hi
    exact (fe.bound_l ⟨s,pair,ee s hs⟩).1
  exact (tree.nodes q).mpr ⟨n,a,b',g,v,fn0_of_function_l (ZF.modelsKP hZF) fq,da,hb',lg,rv,
    hn,fn0_of_function_l (ZF.modelsKP hZF) fa,fn0_of_function_l (ZF.modelsKP hZF) fg,
    fn0_of_function_l (ZF.modelsKP hZF) fv,run.prefix_l nω ee (lg.mono_l I lf bb) (rv.mono_l I ru bb)⟩

theorem Gn_tree_d.branch_exists_l {ω X Q T Z Y d h l r F A e p₀ : M.Domain}
    (tree : Gn_tree_d hZF ω X Q T Z Y d h l r F A) (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (O : Cond_order_d M Q T Q) (fe : M.IsSetFunctionFromTo I e ω X) (hp₀ : M.mem p₀ Q) :
    ∃ p b f u, M.IsSetFunctionFromTo I p ω Y ∧ Branch_d F A p ∧ Fseq_recode_d I d p e ∧
      Fseq_recode_d I h p b ∧ Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u ∧
        ∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀ f := by
  obtain ⟨f,u,ff,fu,run,zero⟩ := gn_run_exists_l hZF hw dc O fe hp₀
  obtain ⟨p,b,fp,branch,de,hb,lf,ru⟩ := tree.of_run_l hZF (fn0_of_function_l (ZF.modelsKP hZF) fe) ff fu run
  exact ⟨p,b,f,u,fp,branch,de,hb,lf,ru,zero⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际任务树分支给出原可数源上的完整泛型

枚举源载体便覆盖源内全部全局稠密集。原稠密族的像包含于实际被命中的族，
局部稠密要求由既有全局化定理恢复。最后由源的可数性实际构造枚举、树、枝
及包含指定条件的泛型；不用背景外部枚举代替内部函数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Gn_tree_d.ground_generic_l {ω c X R Z Y d h l r F A p b e f : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {Q T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q)
    (tree : Gn_tree_d hZF ω X Q.val T.val Z Y d h l r F A) (hw : M.IsOmega ω)
    (fp : M.IsSetFunctionFromTo I p ω Y) (branch : Branch_d F A p)
    (de : Fseq_recode_d I d p e) (hb : Fseq_recode_d I h p b) (lf : Fseq_recode_d I l b f)
    (onto : M.IsSetSurjectiveOnto I e ω X) :
    ∃ H, M.MemberSubset H Q.val ∧ (∀ i q, Entry_d M i q f → M.mem q H) ∧
      Generic_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q (fun q => M.mem q.val H) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have order := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O
  obtain ⟨e₀,b₀,f₀,u,fe,ff,fu,de₀,hb₀,lf₀,_,run⟩ := tree.run_l hZF hw fp branch
  have eq := de₀.unique_l I hZF.1 de
  subst e₀
  have eq := hb₀.unique_l I hZF.1 hb
  subst b₀
  have eq := lf₀.unique_l I hZF.1 lf
  subst f₀
  obtain ⟨V,D,H,range,dense,members,filter,_⟩ := gn_run_filter_l hZF hw order fe ff fu run
  obtain ⟨C,family⟩ := dense_family_l native Q T Q
  have sub : M.MemberSubset C.val D := by
    intro E hE
    obtain ⟨E₀,hE₀,rfl⟩ := (full C E).mp hE
    obtain ⟨i,_,iE⟩ := onto E₀.val E₀.property
    exact (dense E₀.val).mpr ⟨(range E₀.val).mpr ⟨i,iE⟩,
      image_global_dense_l native hZF.1 Subtype.val inj full ((family E₀).mp hE₀)⟩
  have filter' : Gset_d Q.val T.val Q.val C.val H :=
    ⟨filter.proper,filter.inhabited,filter.upward,filter.directed,
      fun p hp E hE => filter.meets p hp E (sub E hE)⟩
  exact ⟨H,fun q hq => (filter.proper q hq).1,
    fun i q iq => (members q).mpr ⟨(ff.bound_l iq).2,i,q,iq,order.refl q (ff.bound_l iq).2⟩,
    filter'.ground_global_l native hZF.1 Subtype.val inj full O (fun E hE => (family E).mpr hE)⟩

/-- 可数传递源、DC 及指定正条件实际产生整套树见证和原源上的泛型。 -/
theorem gn_source_branch_l {ω c X R : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (count : M.CardinalLessOrEqual I X ω)
    (Q T p₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q)
    (hp₀ : (smdl_structure_l I (R := R) source.1.2.1).mem p₀ Q) :
    ∃ Z Y d h l r F A, Gn_tree_d hZF ω X Q.val T.val Z Y d h l r F A ∧
      ∃ p b e f u H, M.IsSetFunctionFromTo I p ω Y ∧ Branch_d F A p ∧
        Fseq_recode_d I d p e ∧ M.IsSetSurjectiveOnto I e ω X ∧ Fseq_recode_d I h p b ∧
        Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u ∧ M.MemberSubset H Q.val ∧ M.mem p₀.val H ∧
        Generic_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q (fun q => M.mem q.val H) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  obtain ⟨ι,fi⟩ := count
  obtain ⟨e,fe,back⟩ := ZF.injection_retract_l I hZF fi (fun _ h => h) p₀.property
  have onto : M.IsSetSurjectiveOnto I e ω X := fun x hx => by
    obtain ⟨i,hi,xi⟩ := fi.1.2.2 x hx
    exact ⟨i,hi,back x i xi⟩
  obtain ⟨Z,Y,d,h,l,r,F,A,tree⟩ := gn_tree_exists_l hZF hw X Q.val T.val
  obtain ⟨p,b,f,u,fp,branch,de,hb,lf,ru,zero⟩ := tree.branch_exists_l hZF hw dc
    (image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O) fe
    ((image_member_l Subtype.val inj full).mpr hp₀)
  obtain ⟨H,sub,contains,generic⟩ := tree.ground_generic_l hZF source trans native O hw fp branch de hb lf onto
  obtain ⟨o,empty,_⟩ := hw.1.1
  exact ⟨Z,Y,d,h,l,r,F,A,tree,p,b,e,f,u,H,fp,branch,de,onto,hb,lf,ru,sub,contains o p₀.val (zero o empty),generic⟩

end YesMetaZFC.Model.Forcing.Internal
