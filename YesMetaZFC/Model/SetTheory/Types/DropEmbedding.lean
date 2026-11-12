import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 裸类型的原语法投影与 dcp

投影是实际查询重编码的逆像，公式自然数码保持不变。定义适用于任意
查询集合，不把语义实现或真值保持作为投影条件；dcp 取紧邻的前缀元数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Td_query_d (n m p q : M.Domain) : Prop := ∃ z E F,
  I.Codes p z E ∧ I.Codes q z F ∧ Td_column_d I n m E F

def td_query_m {d} (n m p q : Term d) : Formula 1 d := set[d] ⟪∃ z E F,
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ, z, E) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ, z, F) ∧
    ⌜td_column_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, E, F)⟫
derive_free_closed td_query_m

theorem td_query_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m p q : Term d) :
    Formula.satisfies ρ (td_query_m n m p q) ↔ Td_query_d I (n.eval ρ) (m.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [td_query_m, Td_query_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, td_column_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem Td_query_d.unique_l (hE : Extensional M) {n m p q r : M.Domain}
    (h : Td_query_d I n m p q) (k : Td_query_d I n m p r) : q = r := by
  obtain ⟨z, E, F, cp, cq, cf⟩ := h
  obtain ⟨z', E', F', cp', cr, cf'⟩ := k
  obtain ⟨ez, ee⟩ := I.injective cp' cp
  subst z' E'
  exact I.unique cq (cf'.unique_l I hE cf ▸ cr)

theorem td_query_exists_l (hZF : M.Models ZF) {ω n m U D P p : M.Domain}
    (sub : M.MemberSubset n m) (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω m U P) (hp : M.mem p D) :
    ∃ q, M.mem q P ∧ Td_query_d I n m p q := by
  obtain ⟨N, E, names, seq, prod⟩ := small
  obtain ⟨N', E', names', seq', prod'⟩ := large
  obtain ⟨z, hz, f, hf, cp⟩ := (prod p).mp hp
  obtain ⟨b, hb, ff⟩ := (seq f).mp hf
  obtain ⟨g, cg, fg⟩ := td_column_exists_l I hZF sub names names' ff
  obtain ⟨q, cq⟩ := I.total z g
  exact ⟨q, (prod' q).mpr ⟨z, hz, g, (seq' g).mpr ⟨b, hb, fg⟩, cq⟩, z, f, g, cp, cq, cg⟩

def Td_project_d (n m D t u : M.Domain) : Prop :=
  ∀ p, M.mem p u ↔ M.mem p D ∧ ∃ q, Td_query_d I n m p q ∧ M.mem q t

def td_project_m {d} (n m D t u : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜u⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ (∃ q, ⌜td_query_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, p, q) ∧ q ∈ ⌜t⌝ₛ)⟫
derive_free_closed td_project_m

theorem td_project_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m D t u : Term d) :
    Formula.satisfies ρ (td_project_m n m D t u) ↔
      Td_project_d I (n.eval ρ) (m.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [td_project_m, Td_project_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    td_query_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem td_project_exists_l (hZF : M.Models ZF) (n m D t : M.Domain) : ∃ u, Td_project_d I n m D t u := by
  let φ : UnarySchema 3 := {
    body := set[4] ⟪∃ q, ⌜td_query_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ, ⌜(.bound 2 : Term 4)⌝ₛ,
      ⌜(.newest : Term 4)⌝ₛ, q) ∧ q ∈ ⌜(.bound 1 : Term 4)⌝ₛ⟫ }
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases m (fun _ => n)), fun _ => n⟩
  obtain ⟨u, sep⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨u, fun p => (sep p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    td_query_sat_l I hZF.1, Formula.satisfies_mem_iff]
  rfl

theorem Td_project_d.unique_l (hE : Extensional M) {n m D t u v : M.Domain}
    (h : Td_project_d I n m D t u) (k : Td_project_d I n m D t v) : u = v :=
  hE.eq_of_same_members u v (fun p => (h p).trans (k p).symm)

def Td_dcp_d (n m D t u : M.Domain) : Prop := M.SuccessorOf m n ∧ Td_project_d I n m D t u

def td_dcp_m {d} (n m D t u : Term d) : Formula 1 d :=
  .conj (Formula.isSuccessor m n) (td_project_m n m D t u)
derive_free_closed td_dcp_m

theorem td_dcp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m D t u : Term d) :
    Formula.satisfies ρ (td_dcp_m n m D t u) ↔
      Td_dcp_d I (n.eval ρ) (m.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [td_dcp_m, Td_dcp_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, td_project_sat_l I hE]

theorem Td_dcp_d.unique_l (hE : Extensional M) {n m D t u v : M.Domain}
    (h : Td_dcp_d I n m D t u) (k : Td_dcp_d I n m D t v) : u = v := h.2.unique_l I hE k.2

end YesMetaZFC.SetTheory.Internal

/-! ## 投影查询与原完整满足关系一致

同一程序使用同一实际赋值。名字重编码只改变指定常量的元数标记，
前缀变量和全部集合常量的值原样保留，故结论覆盖全部内部公式码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Td_name_d.value_l (hKP : M.Models KP) {n m U X s r δ a b : M.Domain}
    (h : Td_name_d n m a b) (on : M.IsOrdinal n) (om : M.IsOrdinal m)
    (fs : Fn0_d n X s) (fr : Fn0_d m X r) (point : M.mem δ X) (constants : M.MemberSubset U X)
    (kept : ∀ i x, Rd_entry_d i x s → Rd_entry_d i x r) (ha : Tn_name_d n U a) (x : M.Domain) :
    Tn_value_d n s δ a x ↔ Tn_value_d m r δ b x := by
  have go y (hy : Tn_value_d n s δ a y) : Tn_value_d m r δ b y := by
    rcases h with ⟨rfl, rfl⟩ | ⟨ne, rfl⟩
    · have eq := tn_value_unique_l hKP on fs hy (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact eq.symm ▸ Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact hy.elim (fun h => Or.inl (kept _ _ h))
        (fun h => h.elim (fun h => (ne h.1).elim) (fun h => Or.inr (Or.inr h)))
  refine ⟨go x, fun hx => ?_⟩
  obtain ⟨y, _, hy⟩ := tn_value_exists_l hKP fs point constants ha
  exact (tn_value_unique_l hKP om fr hx (go y hy)).symm ▸ hy

theorem Td_column_d.domain_l (I : kpair_convention_l.Interpretation M) {n m b E F : M.Domain}
    (h : Td_column_d I n m E F) (dom : M.IsDomainOf I b E) : M.IsDomainOf I b F := by
  intro i
  refine ⟨fun hi => ?_, fun ⟨x, hx⟩ => ?_⟩
  · obtain ⟨a, ha⟩ := (dom i).mp hi
    obtain ⟨x, hx⟩ := td_name_exists_l n m a
    exact ⟨x, (h.2 i x).mpr ⟨a, ha, hx⟩⟩
  · obtain ⟨a, ha, _⟩ := (h.2 i x).mp hx
    exact (dom i).mpr ⟨a, ha⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_column_d.assign_l {n m U X N b E F s r δ v : M.Domain}
    (h : Td_column_d I n m E F) (on : M.IsOrdinal n) (om : M.IsOrdinal m)
    (fs : Fn0_d n X s) (fr : Fn0_d m X r) (point : M.mem δ X) (constants : M.MemberSubset U X)
    (kept : ∀ i x, Rd_entry_d i x s → Rd_entry_d i x r) (names : Tn_names_d n U N)
    (col : M.IsSetFunctionFromTo I E b N) (assign : Tn_assign_d n s δ E v) : Tn_assign_d m r δ F v := by
  refine ⟨assign.1, fun i x => (assign.2 i x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨b, hb⟩ := td_name_exists_l n m a
    exact ⟨b, (h.2 i b).mpr ⟨a, ha, hb⟩,
      (hb.value_l (ZF.modelsKP hZF) on om fs fr point constants kept ((names a).mp (col.output_mem_of_pairMember ha)) x).mp hx⟩
  · rintro ⟨b, hb, hx⟩
    obtain ⟨a, ha, ab⟩ := (h.2 i b).mp hb
    exact ⟨a, ha,
      (ab.value_l (ZF.modelsKP hZF) on om fs fr point constants kept ((names a).mp (col.output_mem_of_pairMember ha)) x).mpr hx⟩

theorem Td_query_d.read_l {ω c X R n m U D P s r δ t p q : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (type : Tt_realized_d I ω c X R m r δ U P t)
    (fs : Fn0_d n X s) (kept : ∀ i x, Rd_entry_d i x s → Rd_entry_d i x r)
    (pool : Tt_pool_d I ω n U D) (hp : M.mem p D) (code : Td_query_d I n m p q) :
    Tt_query_d I ω c n s δ p ↔ Tt_query_d I ω c m r δ q := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z, hz, f, hf, cp⟩ := (prod p).mp hp
  obtain ⟨b, hb, ff⟩ := (seq f).mp hf
  obtain ⟨z', f', g, cp', cq, column⟩ := code
  obtain ⟨ez, ef⟩ := (I).injective cp' cp
  subst z' f'
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have om := hω.members_areOrdinals (ZF.modelsKP hZF) m type.finite
  obtain ⟨v, assign, fv⟩ := tn_assign_exists_l hZF on fs type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) ff)
  obtain ⟨h, fill, _⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fv) type.point
  have assign' := column.assign_l hZF on om fs type.tuple type.point type.constants kept names ff assign
  exact (tt_query_decode_l I (ZF.modelsKP hZF) cp hz hb ff.2.1 assign fill).trans
    (tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb (column.domain_l I ff.2.1) assign' fill).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 删除末位后仍为原前缀的完整类型

先用分离构造裸查询集合的语法逆像，再证明其由实际限制元组实现。
dcp 保留原秩层、指定点与常量域；它与下降一个秩层的 minus 分开。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_realized_d.project_l {ω c X R n m U D P r δ t : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (sub : M.MemberSubset n m)
    (type : Tt_realized_d I ω c X R m r δ U P t) (pool : Tt_pool_d I ω n U D) :
    ∃ s u, M.IsRestrictionOf I s r n ∧ Td_project_d I n m D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨s, cut⟩ := ZF.exists_restriction hZF I r n
  have fs := fn0_of_function_l (ZF.modelsKP hZF) (cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) type.tuple) sub)
  have kept i x (hx : Rd_entry_d i x s) : Rd_entry_d i x r := ((cut.2 i x).mp hx).2
  obtain ⟨u, project⟩ := td_project_exists_l I hZF n m D t
  refine ⟨s, u, cut, project, ⟨type.model, hn, fs, type.point, type.constants, pool, fun p => ?_⟩⟩
  refine (project p).trans (and_congr_right fun hp => ⟨?_, ?_⟩)
  · rintro ⟨q, code, hq⟩
    exact (code.read_l hZF hω hn type fs kept pool hp).mpr ((type.truth q).mp hq).2
  · intro truth
    obtain ⟨q, hq, code⟩ := td_query_exists_l I hZF sub pool type.pool hp
    exact ⟨q, code, (type.truth q).mpr ⟨hq, (code.read_l hZF hω hn type fs kept pool hp).mp truth⟩⟩

/-- 原 5.8 的 dcp：内部后继元数的末位删除，结果字面唯一。 -/
theorem Tt_realized_d.dcp_l {ω c X R n m U D P r δ t : M.Domain}
    (hω : M.IsOmega ω) (succ : M.SuccessorOf m n)
    (type : Tt_realized_d I ω c X R m r δ U P t) (pool : Tt_pool_d I ω n U D) :
    ∃ s u, M.IsRestrictionOf I s r n ∧ Td_dcp_d I n m D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨s, u, cut, project, small⟩ := type.project_l hZF hω
    (hω.transitive (ZF.modelsKP hZF) m type.finite n succ.predecessor_mem) (fun i hi => (succ i).mpr (Or.inl hi)) pool
  exact ⟨s, u, cut, ⟨succ, project⟩, small⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 实际增加末位与 dcp 互逆

由一个完整前缀类型和一个源内对象自动构造更长元组及完整类型。
重新删除末位所得集合字面等于原类型，为弹性前缀提供真实实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_realized_d.append_l {ω c X R n m s δ U D P t x : M.Domain}
    (hω : M.IsOmega ω) (succ : M.SuccessorOf m n) (type : Tt_realized_d I ω c X R n s δ U D t)
    (hx : M.mem x X) (pool : Tt_pool_d I ω m U P) :
    ∃ r u, Tt_realized_d I ω c X R m r δ U P u ∧ Td_dcp_d I n m D u t ∧
      (∀ i y, M.mem i n → (Rd_entry_d i y r ↔ Rd_entry_d i y s)) ∧ Rd_entry_d n x r := by
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n type.finite
  obtain ⟨m', hm', hmω⟩ := hω.1.2 n type.finite
  have hm : M.mem m ω := (hm'.eq hZF.1 succ) ▸ hmω
  obtain ⟨r, fn, kept, last⟩ := tt_column_append_l hZF on succ (fn0_function_l (ZF.modelsKP hZF) type.tuple) hx
  obtain ⟨u, truth, _⟩ := tt_truth_exists_l I hZF ω c m r δ P
  have full : Tt_realized_d I ω c X R m r δ U P u :=
    ⟨type.model, hm, fn0_of_function_l (ZF.modelsKP hZF) fn, type.point, type.constants, pool, truth⟩
  obtain ⟨s', t', cut, drop, small⟩ := full.dcp_l hZF hω succ type.pool
  have eqs : s' = s := Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := I) hZF.1 cut.1
    (fn0_function_l (ZF.modelsKP hZF) type.tuple).1.1 (fun i y => (cut.2 i y).trans
      ⟨fun h => (kept i y h.1).mp h.2, fun h =>
        ⟨(type.tuple.bound_l h).1, (kept i y (type.tuple.bound_l h).1).mpr h⟩⟩)
  subst s'
  have eqt := hZF.1.eq_of_same_members t' t (fun p => (small.truth p).trans (type.truth p).symm)
  exact ⟨r, u, full, eqt ▸ drop, kept, last⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原语法 dcp 在传递源中的绝对读取

重编码只改变指定常量的名字。两张已有列中的坐标、查询对和投影见证
都由传递性收回源；不要求源模型满足 ZF，也不要求类型先有语义实现。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  {X : M.Domain} (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "N" => rt_model_l X nx
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hX nx hE pair

private theorem rt_td_name_l (n m a b : (N).Domain) : Td_name_d n m a b ↔ Td_name_d n.val m.val a.val b.val := by
  have eq (x y : (N).Domain) : x = y ↔ x.val = y.val := ⟨congrArg Subtype.val, Subtype.ext⟩
  exact or_congr (and_congr (eq a n) (eq b m)) (and_congr (not_congr (eq a n)) (eq b a))

theorem rt_td_column_l (n m E F : (N).Domain) : Td_column_d J n m E F ↔ Td_column_d I n.val m.val E.val F.val := by
  have ent := rt_entry_l hX nx hE
  constructor
  · rintro ⟨rel, read⟩
    refine ⟨(rt_relation_l hE hP hX nx pair F).mp rel, fun i b => ⟨?_, ?_⟩⟩
    · intro hib
      have ib := rd_entry_transitive_l hX F.property hib
      obtain ⟨a, hia, name⟩ := (read ⟨i, ib.1⟩ ⟨b, ib.2⟩).mp ((ent ..).mpr hib)
      exact ⟨a.val, (ent ..).mp hia, (rt_td_name_l nx ..).mp name⟩
    · rintro ⟨a, hia, name⟩
      have ia := rd_entry_transitive_l hX E.property hia
      have hb : M.mem b X := name.elim (fun h => h.2.symm ▸ m.property) (fun h => h.2.symm ▸ ia.2)
      exact (ent ..).mp ((read ⟨i, ia.1⟩ ⟨b, hb⟩).mpr ⟨⟨a, ia.2⟩, (ent ..).mpr hia, (rt_td_name_l nx ..).mpr name⟩)
  · rintro ⟨rel, read⟩
    refine ⟨(rt_relation_l hE hP hX nx pair F).mpr rel, fun i b => ⟨?_, ?_⟩⟩
    · intro hib
      obtain ⟨a, hia, name⟩ := (read i.val b.val).mp ((ent ..).mp hib)
      exact ⟨⟨a, (rd_entry_transitive_l hX E.property hia).2⟩, (ent ..).mpr hia, (rt_td_name_l nx ..).mpr name⟩
    · rintro ⟨a, hia, name⟩
      exact (ent ..).mpr ((read i.val b.val).mpr ⟨a.val, (ent ..).mp hia, (rt_td_name_l nx ..).mp name⟩)

theorem rt_td_query_l (n m p q : (N).Domain) : Td_query_d J n m p q ↔ Td_query_d I n.val m.val p.val q.val := by
  have cp := rt_kpair_l hE hP hX nx pair
  constructor
  · rintro ⟨z, E, F, hp, hq, col⟩
    exact ⟨z.val, E.val, F.val, (cp ..).mp hp, (cp ..).mp hq, (rt_td_column_l hE hP hX nx pair ..).mp col⟩
  · rintro ⟨z, E, F, hp, hq, col⟩
    have zE := hp.mem_l M hX p.property
    have zF := hq.mem_l M hX q.property
    exact ⟨⟨z, zE.1⟩, ⟨E, zE.2⟩, ⟨F, zF.2⟩, (cp ..).mpr hp, (cp ..).mpr hq,
      (rt_td_column_l hE hP hX nx pair ..).mpr col⟩

theorem rt_td_project_l (n m D t v : (N).Domain) :
    Td_project_d J n m D t v ↔ Td_project_d I n.val m.val D.val t.val v.val := by
  constructor
  · intro h p
    constructor
    · intro hp
      obtain ⟨hd, q, code, hq⟩ := (h ⟨p, hX v.val v.property p hp⟩).mp hp
      exact ⟨hd, q.val, (rt_td_query_l hE hP hX nx pair ..).mp code, hq⟩
    · rintro ⟨hd, q, code, hq⟩
      exact (h ⟨p, hX D.val D.property p hd⟩).mpr ⟨hd, ⟨q, hX t.val t.property q hq⟩,
        (rt_td_query_l hE hP hX nx pair ..).mpr code, hq⟩
  · intro h p
    exact (h p.val).trans (and_congr_right fun _ =>
      ⟨fun ⟨q, code, hq⟩ => ⟨⟨q, hX t.val t.property q hq⟩, (rt_td_query_l hE hP hX nx pair ..).mpr code, hq⟩,
        fun ⟨q, code, hq⟩ => ⟨q.val, (rt_td_query_l hE hP hX nx pair ..).mp code, hq⟩⟩)

include hX pair in
theorem td_dcp_source_l {d} (ρ : Env N d) (n m D t v : Term d) :
    Formula.satisfies ρ (td_dcp_m n m D t v) ↔
      Td_dcp_d I (n.eval ρ).val (m.eval ρ).val (D.eval ρ).val (t.eval ρ).val (v.eval ρ).val :=
  (td_dcp_sat_l J (rt_model_ext_l hE hX nx) ρ n m D t v).trans
    (and_congr (rt_successor_l hX nx hE ..) (rt_td_project_l hE hP hX nx pair ..))

include hX in
/-- 原投影在源内由相对分离实际产生，重编码见证由传递性绝对读取。 -/
theorem td_project_source_exists_l (hZF : M.Models ZF) {ω c R n m D t : M.Domain}
    (hω : M.IsOmega ω) (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hn : M.mem n X) (hm : M.mem m X) (hD : M.mem D X) (ht : M.mem t X) :
    ∃ v, M.mem v X ∧ Td_project_d (kp_pair_l (ZF.modelsKP hZF)) n m D t v := by
  obtain ⟨x, hx⟩ := model.1.2.1
  let nc : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  let K₀ := kp_pair_l (ZF.modelsKP hZF)
  let P := rt_pair_l hX nc hZF.1 (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair
  let φ : UnarySchema 3 := { body := .existsE (.conj
    (td_query_m (.bound 4) (.bound 3) (.bound 1) .newest) (.mem .newest (.bound 2))) }
  let ρ : Env (rt_model_l X nc) 3 :=
    ⟨Fin.cases ⟨t, ht⟩ (Fin.cases ⟨m, hm⟩ (fun _ => ⟨n, hn⟩)), fun _ => ⟨n, hn⟩⟩
  have read (p : (rt_model_l X nc).Domain) : φ.denote ρ p ↔
      ∃ q, Td_query_d K₀ n m p.val q ∧ M.mem q t := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      td_query_sat_l P (rt_model_ext_l hZF.1 hX nc), Formula.satisfies_mem_iff]
    exact ⟨fun ⟨q, code, hq⟩ => ⟨q.val,
      (rt_td_query_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nc (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair ..).mp code, hq⟩,
      fun ⟨q, code, hq⟩ => ⟨⟨q, hX t ht q hq⟩,
        (rt_td_query_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nc (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair ..).mpr code, hq⟩⟩
  obtain ⟨v, hv, sub, sep⟩ := sc_separate_relative_l K₀ hZF hω hX model theory nc φ ρ hD
  exact ⟨v, hv, fun p => ⟨fun hp => ⟨sub p hp,
    (read ⟨p, hX v hv p hp⟩).mp ((sep ⟨p, hX v hv p hp⟩).mp hp).2⟩,
    fun hp => (sep ⟨p, hX D hD p hp.1⟩).mpr ⟨hp.1, (read ⟨p, hX D hD p hp.1⟩).mpr hp.2⟩⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原 dcp 与实际初等像交换

运输的是原查询重编码与逆像等式；两侧都按同一 dcp 定义读取。
所需源闭包仅为传递与配对，没有把像类型的投影作为额外不变量假定。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.type_dcp_l {ω c d X R Y S j n m D t v n' m' D' t' v' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (px : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (py : ∀ a b, M.mem a Y → M.mem b Y → ∃ p, M.mem p Y ∧ Pair_d M p a b)
    (hh : Rd_entry_d n n' j) (hk : Rd_entry_d m m' j) (hD : Rd_entry_d D D' j)
    (ht : Rd_entry_d t t' j) (hv : Rd_entry_d v v' j) :
    Td_dcp_d I n m D t v ↔ Td_dcp_d I n' m' D' t' v' := by
  have inside {x y} (h : Rd_entry_d x y j) := hj.1.1.input_mem_of_pairMember h
  have outside {x y} (h : Rd_entry_d x y j) := hj.1.1.output_mem_of_pairMember h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨v, inside hv⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨v', outside hv⟩⟩
  let ρ : Env (rt_model_l X nx) 5 := ⟨Fin.cases ⟨v, inside hv⟩ (Fin.cases ⟨t, inside ht⟩
    (Fin.cases ⟨D, inside hD⟩ (Fin.cases ⟨m, inside hk⟩ (fun _ => ⟨n, inside hh⟩)))), fun _ => ⟨v, inside hv⟩⟩
  let η : Env (rt_model_l Y ny) 5 := ⟨Fin.cases ⟨v', outside hv⟩ (Fin.cases ⟨t', outside ht⟩
    (Fin.cases ⟨D', outside hD⟩ (Fin.cases ⟨m', outside hk⟩ (fun _ => ⟨n', outside hh⟩)))), fun _ => ⟨v', outside hv⟩⟩
  let φ : Formula 1 5 := td_dcp_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny φ
    (by simp -implicitDefEqProofs [φ]) ρ η (Fin.cases hv (Fin.cases ht (Fin.cases hD (Fin.cases hk (fun _ => hh)))))
  exact (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nx px ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    (tr.trans (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hY ny py η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))

end YesMetaZFC.SetTheory.Internal
