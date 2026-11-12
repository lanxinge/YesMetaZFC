import YesMetaZFC.Model.SetTheory.Types.MoveQuote
import YesMetaZFC.Model.SetTheory.Types.CanonicalSatisfaction
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.CumulativeProduct
import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 实现元组的完整内部类型

一个查询是 (自然数公式码,有限名字列)。名字列把变量、指定常量 δ 和集合常量
同时送入原满足关系；真值量化全部内部码。类型就是查询域中的真查询集合，
由分离实际构造，参数域缩小时投影为交集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tt_query_d (ω c n s δ p : M.Domain) : Prop := ∃ z b e r f,
  I.Codes p z e ∧ M.mem z ω ∧ M.mem b ω ∧ M.IsDomainOf I b e ∧
    Tn_assign_d n s δ e r ∧ Senv_fill_d I ω δ b r f ∧ Sc_sat_d I ω c z f

def tt_query_m {d} (ω c n s δ p : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (kpair_convention_l.code p.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
      (.conj (.mem (.bound 4) ω.weaken.weaken.weaken.weaken.weaken)
        (.conj (.mem (.bound 3) ω.weaken.weaken.weaken.weaken.weaken)
          (.conj (Formula.isDomain kpair_convention_l (.bound 3) (.bound 2))
            (.conj (tn_assign_m n.weaken.weaken.weaken.weaken.weaken s.weaken.weaken.weaken.weaken.weaken
              δ.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
              (.conj (senv_fill_m (𝒞 := kpair_convention_l) ω.weaken.weaken.weaken.weaken.weaken
                δ.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
                (sc_sat_m (𝒞 := kpair_convention_l) ω.weaken.weaken.weaken.weaken.weaken
                  c.weaken.weaken.weaken.weaken.weaken (.bound 4) .newest)))))))))))
derive_free_closed tt_query_m

theorem tt_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c n s δ p : Term d) :
    Formula.satisfies ρ (tt_query_m ω c n s δ p) ↔
      Tt_query_d I (ω.eval ρ) (c.eval ρ) (n.eval ρ) (s.eval ρ) (δ.eval ρ) (p.eval ρ) := by
  simp only [tt_query_m, Tt_query_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_mem_iff, Formula.satisfies_isDomain_iff I,
    tn_assign_sat_l hKP, senv_fill_sat_l I hKP.1, sc_sat_formula_l I hKP.1, Definitional.Term.eval_weaken]
  rfl

/-- 码、名字列和实际赋值固定后，查询精确等价于原完整满足关系。 -/
theorem tt_query_decode_l (hKP : M.Models KP) {ω c n s δ p z b e r f : M.Domain}
    (hp : I.Codes p z e) (hz : M.mem z ω) (hb : M.mem b ω) (he : M.IsDomainOf I b e)
    (hr : Tn_assign_d n s δ e r) (hf : Senv_fill_d I ω δ b r f) :
    Tt_query_d I ω c n s δ p ↔ Sc_sat_d I ω c z f := by
  refine ⟨?_, fun h => ⟨z, b, e, r, f, hp, hz, hb, he, hr, hf, h⟩⟩
  rintro ⟨z', b', e', r', f', hp', _, _, he', hr', hf', truth⟩
  obtain ⟨ez, ee⟩ := I.injective hp' hp
  subst z' e'
  have eb := he'.eq hKP.1 he
  subst b'
  have er := tn_assign_unique_l hKP hr' hr
  subst r'
  exact senv_fill_unique_l I hKP.1 hf' hf ▸ truth

def Tt_pool_d (ω n U D : M.Domain) : Prop := ∃ N E,
  Tn_names_d n U N ∧ Fseq_space_d I ω N E ∧ M.IsCartesianProduct I D ω E

theorem tt_pool_exists_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) (n U : M.Domain) :
    ∃ D, Tt_pool_d I ω n U D := by
  obtain ⟨N, names⟩ := tn_names_exists_l hZF n U
  obtain ⟨E, seq⟩ := ZF.fseq_space_exists_l I hZF hω N
  obtain ⟨D, prod⟩ := ZF.exists_cartesianProduct hZF I ω E
  exact ⟨D, N, E, names, seq, prod⟩

theorem Tt_pool_d.mono_l {ω n U V D E : M.Domain} (hD : Tt_pool_d I ω n U D)
    (hE : Tt_pool_d I ω n V E) (hUV : M.MemberSubset U V) : M.MemberSubset D E := by
  obtain ⟨N, S, names, seq, prod⟩ := hD
  obtain ⟨N', S', names', seq', prod'⟩ := hE
  have sub : M.MemberSubset N N' := by
    intro a ha
    apply (names' a).mpr
    rcases (names a).mp ha with ha | ha | ⟨x, hx, hp⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ⟨x, hUV x hx, hp⟩)
  intro p hp
  obtain ⟨z, hz, e, he, code⟩ := (prod p).mp hp
  obtain ⟨b, hb, fn⟩ := (seq e).mp he
  exact (prod' p).mpr ⟨z, hz, e, (seq' e).mpr ⟨b, hb, fn.1, fn.2.1,
    fun i hi => (fn.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩, code⟩

def Tt_truth_d (ω c n s δ D t : M.Domain) : Prop :=
  ∀ p, M.mem p t ↔ M.mem p D ∧ Tt_query_d I ω c n s δ p

/-- 完整类型由实际集合结构中的有限元组实现，常量域亦包含在该结构中。 -/
structure Tt_realized_d (ω c Z R n s δ U D t : M.Domain) : Prop where
  model : Smdl_d I c Z R
  finite : M.mem n ω
  tuple : Fn0_d n Z s
  point : M.mem δ Z
  constants : M.MemberSubset U Z
  pool : Tt_pool_d I ω n U D
  truth : Tt_truth_d I ω c n s δ D t

theorem tt_truth_exists_l (hZF : M.Models ZF) (ω c n s δ D : M.Domain) :
    ∃ t, Tt_truth_d I ω c n s δ D t ∧ M.IsSetRelation I t := by
  let φ : UnarySchema 5 := { body := tt_query_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let ρ : Env M 5 := ⟨Fin.cases δ (Fin.cases s (Fin.cases n (Fin.cases c (fun _ => ω)))), fun _ => ω⟩
  obtain ⟨t, sep⟩ := ZF.separation_exists_d hZF φ ρ D
  have truth : Tt_truth_d I ω c n s δ D t := fun p => (sep p).trans
    (and_congr_right fun _ => tt_query_sat_l I (ZF.modelsKP hZF) ..)
  refine ⟨t, truth, fun p hp => ?_⟩
  obtain ⟨z, _, e, _, _, code, _⟩ := ((truth p).mp hp).2
  exact ⟨z, e, code⟩

theorem Tt_truth_d.project_l {ω c n s δ D E t u : M.Domain}
    (ht : Tt_truth_d I ω c n s δ D t) (hu : Tt_truth_d I ω c n s δ E u)
    (hDE : M.MemberSubset D E) : ∀ p, M.mem p t ↔ M.mem p D ∧ M.mem p u := by
  intro p
  exact (ht p).trans ⟨fun hh => ⟨hh.1, (hu p).mpr ⟨hDE p hh.1, hh.2⟩⟩,
    fun hh => ⟨hh.1, ((hu p).mp hh.2).2⟩⟩

/-- 任意内部有限实现元组、指定常量和参数域都产生实际类型。 -/
theorem tt_type_exists_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) (c n s δ U : M.Domain) :
    ∃ D t, Tt_pool_d I ω n U D ∧ Tt_truth_d I ω c n s δ D t ∧ M.IsSetRelation I t := by
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨t, truth, rel⟩ := tt_truth_exists_l I hZF ω c n s δ D
  exact ⟨D, t, pool, truth, rel⟩

/-- 每个合法查询的中间赋值均可自动构造；类型成员等价于该实际赋值的真值。 -/
theorem Tt_pool_d.realize_l (hZF : M.Models ZF) {ω c n s δ U Z D p : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hs : Fn0_d n Z s) (hδ : M.mem δ Z)
    (hU : M.MemberSubset U Z) (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) ω n U D) (hp : M.mem p D) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ z b e r f, I.Codes p z e ∧ M.mem z ω ∧ M.mem b ω ∧ M.IsDomainOf I b e ∧
      Tn_assign_d n s δ e r ∧ Senv_fill_d I ω δ b r f ∧ Fn0_d ω Z f ∧
        (Tt_query_d I ω c n s δ p ↔ Sc_sat_d I ω c z f) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z, hz, e, he, code⟩ := (prod p).mp hp
  obtain ⟨b, hb, fn⟩ := (seq e).mp he
  obtain ⟨r, hr, fnr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n hn)
    hs hδ hU names (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨f, hf, fnf⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fnr) hδ
  exact ⟨z, b, e, r, f, code, hz, hb, fn.2.1, hr, hf, fn0_of_function_l (ZF.modelsKP hZF) fnf,
    tt_query_decode_l I (ZF.modelsKP hZF) code hz hb fn.2.1 hr hf⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原变量前缀与有限参数表的统一名字列

内部 n 个变量保持原位置；固定模板的参数逐项追加。返回实际槽位表供
程序编译与名字求值共同使用，不依赖 n 在外部是否标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_column_append_l {f l m N x : M.Domain} (hl : M.IsOrdinal l) (hs : M.SuccessorOf m l)
    (hf : M.IsSetFunctionFromTo I f l N) (hx : M.mem x N) :
    ∃ g, M.IsSetFunctionFromTo I g m N ∧
      (∀ i y, M.mem i l → (Rd_entry_d i y g ↔ Rd_entry_d i y f)) ∧ Rd_entry_d l x g := by
  obtain ⟨g, hg, graph⟩ := Structure.IsSequenceOfLength.exists_append (ZF.modelsKP hZF) I ⟨hl, hf.1, hf.2.1⟩
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hl hs) hs
  have bound i y (h : Rd_entry_d i y g) : M.mem y N :=
    ((graph i y).mp h).elim (fun h => hf.output_mem_of_pairMember h) (fun h => h.2.symm ▸ hx)
  exact ⟨g, ⟨hg.2.1, hg.2.2, fun i hi => ((hg.2.2 i).mp hi).imp fun y hy => ⟨bound i y hy, hy⟩⟩,
    fun i y hi => (graph i y).trans ⟨fun h => h.elim id (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) l (h.1 ▸ hi)).elim), Or.inl⟩,
    (graph l x).mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem tt_column_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) (k : Nat) :
    ∃ b, ∃ σ : Fin k → M.Domain, M.mem b ω ∧ M.MemberSubset n b ∧ (∀ i, M.mem (σ i) b) ∧
      (∀ i, M.mem i b → M.mem i n ∨ ∃ j, i = σ j) ∧
      ∀ U N, Tn_names_d n U N → ∀ a : Fin k → M.Domain, (∀ i, M.mem (a i) N) →
        ∃ C, M.IsSetFunctionFromTo I C b N ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧
          ∀ i, Rd_entry_d (σ i) (a i) C := by
  induction k with
  | zero =>
    refine ⟨n, Fin.elim0, hn, fun _ h => h, fun i => Fin.elim0 i,
      fun _ h => Or.inl h, fun U N names a ha => ?_⟩
    let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
    let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
    have sat i x : φ.denote ρ i x ↔ x = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
    obtain ⟨C, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
      (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
      (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
      (fun i x hi hx => ((sat i x).mp hx).symm ▸ (names i).mpr (Or.inl hi))
    exact ⟨C, fn, fun i hi => (graph i i).mpr ⟨hi, (sat i i).mpr rfl⟩, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨b, σ, hb, nb, bound, cover, build⟩ := ih
    obtain ⟨d, hd, hdω⟩ := hω.1.2 b hb
    refine ⟨d, Fin.cases b σ, hdω, fun i hi => (hd i).mpr (Or.inl (nb i hi)),
      Fin.cases hd.predecessor_mem (fun i => (hd (σ i)).mpr (Or.inl (bound i))), ?_, fun U N names a ha => ?_⟩
    · intro i hi
      rcases (hd i).mp hi with hi | hi
      · exact (cover i hi).elim Or.inl (fun ⟨j, hj⟩ => Or.inr ⟨j.succ, hj⟩)
      · exact Or.inr ⟨0, hZF.1.eq_of_same_members i b hi⟩
    obtain ⟨C, fn, old, values⟩ := build U N names (fun i => a i.succ) (fun i => ha i.succ)
    obtain ⟨C', fn', kept, last⟩ := tt_column_append_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) b hb) hd fn (ha 0)
    exact ⟨C', fn',
      fun i hi => (kept i i (nb i hi)).mpr (old i hi),
      Fin.cases last (fun i => (kept (σ i) (a i.succ) (bound i)).mpr (values i))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 类型投影的名字重编码

保留前 n 个变量时，它们的编号与集合常量不变；指定常量 δ 的名字
由 n 改为原元数 m。列变换由原公式替换构造，不选择宿主函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Td_name_d (n m a b : M.Domain) : Prop := (a = n ∧ b = m) ∨ (a ≠ n ∧ b = a)

def td_name_m {d} (n m a b : Term d) : Formula 1 d := set[d] ⟪
  (⌜a⌝ₛ = ⌜n⌝ₛ ∧ ⌜b⌝ₛ = ⌜m⌝ₛ) ∨ (¬ (⌜a⌝ₛ = ⌜n⌝ₛ) ∧ ⌜b⌝ₛ = ⌜a⌝ₛ)⟫
derive_free_closed td_name_m

theorem td_name_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m a b : Term d) :
    Formula.satisfies ρ (td_name_m n m a b) ↔ Td_name_d (n.eval ρ) (m.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [td_name_m, Td_name_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE]

theorem td_name_exists_l (n m a : M.Domain) : ∃ b, Td_name_d n m a b := by
  by_cases h : a = n
  · exact ⟨m, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨a, Or.inr ⟨h, rfl⟩⟩

theorem Td_name_d.unique_l {n m a b c : M.Domain} (h : Td_name_d n m a b) (k : Td_name_d n m a c) : b = c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ne, rfl⟩ <;> rcases k with ⟨eq, rfl⟩ | ⟨ne', rfl⟩
  · rfl
  · exact (ne' rfl).elim
  · exact (ne eq).elim
  · rfl

theorem Td_name_d.name_l {n m U a b : M.Domain} (h : Td_name_d n m a b)
    (sub : M.MemberSubset n m) (ha : Tn_name_d n U a) : Tn_name_d m U b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ne, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact ha.elim (fun h => Or.inl (sub _ h)) (fun h => h.elim (fun eq => (ne eq).elim) (fun h => Or.inr (Or.inr h)))

variable (I : kpair_convention_l.Interpretation M)

def Td_column_d (n m E F : M.Domain) : Prop := M.IsSetRelation I F ∧ ∀ i b,
  M.PairMember I i b F ↔ ∃ a, M.PairMember I i a E ∧ Td_name_d n m a b

def td_column_m {d} (n m E F : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜F⌝ₛ) ∧ (∀ i b,
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, b, ⌜F⌝ₛ) ↔
      (∃ a, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, a, ⌜E⌝ₛ) ∧ ⌜td_name_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, a, b)))⟫
derive_free_closed td_column_m

theorem td_column_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m E F : Term d) :
    Formula.satisfies ρ (td_column_m n m E F) ↔ Td_column_d I (n.eval ρ) (m.eval ρ) (E.eval ρ) (F.eval ρ) := by
  simp only [td_column_m, Td_column_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, td_name_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Td_column_d.unique_l (hE : Extensional M) {n m E F G : M.Domain}
    (h : Td_column_d I n m E F) (k : Td_column_d I n m E G) : F = G :=
  Structure.IsSetRelation.eq_of_pairMember_iff hE h.1 k.1 (fun i x => (h.2 i x).trans (k.2 i x).symm)

theorem td_column_exists_l (hZF : M.Models ZF) {n m U N P b E : M.Domain}
    (sub : M.MemberSubset n m) (names : Tn_names_d n U N) (newNames : Tn_names_d m U P)
    (fn : M.IsSetFunctionFromTo I E b N) :
    ∃ F, Td_column_d I n m E F ∧ M.IsSetFunctionFromTo I F b P := by
  let φ : BinarySchema 3 := {
    body := set[5] ⟪∃ a, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, a, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
      ⌜td_name_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, a, ⌜(.newest : Term 5)⌝ₛ)⟫ }
  let ρ : Env M 3 := ⟨Fin.cases E (Fin.cases m (fun _ => n)), fun _ => n⟩
  have read i x : φ.denote ρ i x ↔ ∃ a, M.PairMember I i a E ∧ Td_name_d n m a x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, td_name_sat_l hZF.1]
    rfl
  obtain ⟨F, ff, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => by
      obtain ⟨a, _, ha⟩ := fn.2.2 i hi
      obtain ⟨x, hx⟩ := td_name_exists_l n m a
      exact ⟨x, (read i x).mpr ⟨a, ha, hx⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨a, ha, hx⟩ := (read i x).mp hx
      obtain ⟨a', ha', hy⟩ := (read i y).mp hy
      exact hx.unique_l (fn.1.2 i a' a ha' ha ▸ hy))
    (fun i x _ hx => by
      obtain ⟨a, ha, hx⟩ := (read i x).mp hx
      exact (newNames x).mpr (hx.name_l sub ((names a).mp (fn.output_mem_of_pairMember ha))))
  exact ⟨F, ⟨ff.1.1, fun i x => (graph i x).trans ((and_congr_right fun _ => read i x).trans
    ⟨And.right, fun h => ⟨h.elim (fun _ h => fn.input_mem_of_pairMember h.1), h⟩⟩)⟩, ff⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 定义域查询的实际名字列

列依次读取全部原变量、指定常量 δ 和集合常量 κ。只增加两个坐标，
长度仍是模型内部的自然数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_guard_code_d (n κ U l z p : M.Domain) : Prop := ∃ b k C N,
  M.SuccessorOf b n ∧ M.SuccessorOf l b ∧ Tn_names_d n U N ∧ Fn0_d l N C ∧
    KPair_d M k κ κ ∧ KPair_d M p z C ∧ (∀ i, M.mem i b → Rd_entry_d i i C) ∧ Rd_entry_d b k C

theorem tg_column_l {ω n κ U N : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.mem κ U) (names : Tn_names_d n U N) : ∃ b l k e,
      M.SuccessorOf b n ∧ M.SuccessorOf l b ∧ M.mem l ω ∧ (I).Codes k κ κ ∧
      M.IsSetFunctionFromTo I e l N ∧
        ∀ i a, Rd_entry_d i a e ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
  obtain ⟨b, hb, hbω⟩ := hω.1.2 n hn
  obtain ⟨l, hl, hlω⟩ := hω.1.2 b hbω
  obtain ⟨k, hk⟩ := (I).total κ κ
  have small i (hi : M.mem i b) : M.mem i N := by
    apply (names i).mpr
    rcases (hb i).mp hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl (hZF.1.eq_of_same_members i n hi))
  have large := (names k).mpr (Or.inr (Or.inr ⟨κ, hκ, hk⟩))
  let ρ : Env M 2 := ⟨Fin.cases k (fun _ => b), fun _ => n⟩
  let φ : BinarySchema 2 := { body := (.disj (.conj (.mem (.bound 1) (.bound 3)) (Formula.extensionalEq .newest (.bound 1)))
    (.conj (Formula.extensionalEq (.bound 1) (.bound 3)) (Formula.extensionalEq .newest (.bound 2)))) }
  have read i a : φ.denote ρ i a ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨e, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := l) (target := N) (by
    intro i hi
    rcases (hl i).mp hi with hi | hi
    · exact ⟨i, (read i i).mpr (Or.inl ⟨hi, rfl⟩)⟩
    · exact ⟨k, (read i k).mpr (Or.inr ⟨hZF.1.eq_of_same_members i b hi, rfl⟩)⟩) (by
      intro i _ a c ha hc
      rcases (read i a).mp ha with ⟨hi, ha⟩ | ⟨hi, ha⟩ <;>
        rcases (read i c).mp hc with ⟨hi', hc⟩ | ⟨hi', hc⟩
      · exact ha.trans hc.symm
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) b (hi' ▸ hi)).elim
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) b (hi ▸ hi')).elim
      · exact ha.trans hc.symm) (by
        intro i a _ ha
        rcases (read i a).mp ha with ⟨hi, ha⟩ | ⟨_, ha⟩
        · exact ha.symm ▸ small i hi
        · exact ha.symm ▸ large)
  refine ⟨b, l, k, e, hb, hl, hlω, hk, fn, fun i a => (graph i a).trans ?_⟩
  exact ⟨fun h => (read i a).mp h.2, fun h => ⟨h.elim
    (fun h => (hl i).mpr (Or.inl h.1)) (fun h => h.1.symm ▸ hl.predecessor_mem), (read i a).mpr h⟩⟩

/-- 指定名字列的全部赋值恰由原元组、δ、κ 三部分组成。 -/
theorem tg_column_values_l {ω n b l k κ e Y X s δ a f : M.Domain}
    (hω : M.IsOmega ω) (hb : M.SuccessorOf b n) (hl : M.SuccessorOf l b)
    (hlω : M.mem l ω) (hk : (I).Codes k κ κ)
    (column : ∀ i z, Rd_entry_d i z e ↔ (M.mem i b ∧ z = i) ∨ (i = b ∧ z = k))
    (tuple : Fn0_d n Y s) (assign : Tn_assign_d n s δ e a) (fill : Senv_fill_d I ω δ l a f)
    (fn : M.IsSetFunctionFromTo I f ω Y) :
    (∀ i y, M.mem i l → Rd_entry_d i y f → M.mem y X) ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X := by
  have nbl i (hi : M.mem i n) : M.mem i l := (hl i).mpr (Or.inl ((hb i).mpr (Or.inl hi)))
  have nlt : M.mem n l := (hl n).mpr (Or.inl hb.predecessor_mem)
  have read i z y (hi : M.mem i l) (he : Rd_entry_d i z e) (value : Tn_value_d n s δ z y) : Rd_entry_d i y f :=
    (fill.2 i y).mpr ⟨hω.transitive (ZF.modelsKP hZF) l hlω i hi, Or.inl ⟨hi, (assign.2 i y).mpr ⟨z, he, value⟩⟩⟩
  have old i y (he : Rd_entry_d i y s) : Rd_entry_d i y f :=
    read i i y (nbl i (tuple.bound_l he).1)
      ((column i i).mpr (Or.inl ⟨(hb i).mpr (Or.inl (tuple.bound_l he).1), rfl⟩)) (Or.inl he)
  have point := read n n δ nlt ((column n n).mpr (Or.inl ⟨hb.predecessor_mem, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have constant := read b k κ hl.predecessor_mem ((column b k).mpr (Or.inr ⟨rfl, rfl⟩)) (Or.inr (Or.inr hk))
  constructor
  · intro h
    have st := fn0_function_l (ZF.modelsKP hZF) tuple
    exact ⟨fn0_of_function_l (ZF.modelsKP hZF) ⟨st.1, st.2.1, fun i hi =>
      (st.2.2 i hi).imp fun y hy => ⟨h i y (nbl i hi) (old i y hy.2), hy.2⟩⟩,
      h n δ nlt point, h b κ hl.predecessor_mem constant⟩
  · rintro ⟨small, hδ, hκ⟩ i y hi he
    rcases (hl i).mp hi with hi | hi
    · rcases (hb i).mp hi with hi | hi
      · obtain ⟨x, hx, hix⟩ := small.2.1 i hi
        exact fn.1.2 i y x he (old i x hix) ▸ hx
      · have eq := hZF.1.eq_of_same_members i n hi
        subst i
        exact fn.1.2 n y δ he point ▸ hδ
    · have eq := hZF.1.eq_of_same_members i b hi
      subst i
      exact fn.1.2 b y κ he constant ▸ hκ

end YesMetaZFC.SetTheory.Internal

/-! ## 类型查询域的实际秩界

变量名来自内部有限序数，常量名只加固定次数的配对。有限列空间整体属于
任意包含参数域和 ω 的极限秩层；类型再由分离取得，亦属于同一秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

section
variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem Tn_names_d.rank_mem_l {ω θ X n U N : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X) (hn : M.mem n ω)
    (hU : M.mem U X) (hN : Tn_names_d n U N) : M.mem N X := by
  obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
  obtain ⟨P, hPX, hP⟩ := KP.v_product_exists_l hKP hX hθ hU hU
  have hmX := v_transitive_l I hX ω hωX m hmω
  obtain ⟨B, hBX, hmB, hPB⟩ := v_joint_bound_l I hX hmX hPX
  apply v_subset_mem_l I hX hBX
  intro a ha
  rcases (hN a).mp ha with ha | ha | ⟨x, hx, code⟩
  · exact hmB a ((hm a).mpr (Or.inl ha))
  · exact hmB a ((hm a).mpr (Or.inr (ha ▸ fun _ => Iff.rfl)))
  · exact hPB a ((hP a).mpr ⟨x, hx, x, hx, code⟩)

theorem Tt_pool_d.rank_mem_l {ω θ X n U D : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X) (hn : M.mem n ω)
    (hU : M.mem U X) (pool : Tt_pool_d I ω n U D) : M.mem D X := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  have hN := names.rank_mem_l hKP hω hX hθ hωX hn hU
  obtain ⟨Y,hY,wy,ny⟩ := v_joint_bound_l I hX hωX hN
  have hE : M.mem E X := v_relations_mem_l I hX hθ hY (fun f hf p hp => by
    obtain ⟨n,hn,fn⟩ := (seq f).mp hf
    obtain ⟨a,b,pair⟩ := fn.1.1 p hp
    exact ⟨a,wy a (hω.transitive hKP n hn a (fn.input_mem_of_pairMember ⟨p,pair,hp⟩)),
      b,ny b (fn.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
  obtain ⟨Z,hZ,wz,ez⟩ := v_joint_bound_l I hX hωX hE
  exact v_relation_mem_l I hX hθ hZ (fun p hp =>
    (prod p).mp hp |>.elim fun a ha => ha.2.elim fun b hb => ⟨a,wz a ha.1,b,ez b hb.1,hb.2⟩)

end

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- κ 型的常量域恰为 Vκ∪{κ}，并实际属于任意更高的极限秩层。 -/
theorem tt_constants_exists_l {θ X κ : M.Domain} (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ)
    (hκ : M.mem κ θ) : ∃ B U, V_d I κ B ∧ M.mem U X ∧ ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ := by
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF (hθ.1.mem hκ)
  obtain ⟨a, ha⟩ := KP.exists_pair (ZF.modelsKP hZF) κ κ
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B a
  have spec x : M.mem x U ↔ M.mem x B ∨ x = κ := (hU x).trans
    (or_congr Iff.rfl ((ha x).trans ⟨fun hh => hh.elim id id, Or.inl⟩))
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  have hPX := v_power_mem_l I hX hθ (ZF.v_mem_l I hZF hB hX hκ) hP
  refine ⟨B, U, hB, v_subset_mem_l I hX hPX (fun x hx => (hP x).mpr ?_), spec⟩
  rcases (spec x).mp hx with hx | rfl
  · exact v_transitive_l I hB x hx
  · exact ZF.v_ordinal_subset_l I hZF hB

end YesMetaZFC.SetTheory.Internal

/-! ## 原类型查询域的有界识别

名字表逐项核验变量、指定常量和集合常量，并要求这些名字全部出现。
有限名字列空间由实际秩界回收，再用原 Kuratowski 乘积构造完整查询域。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tn_names0_m {d} (n U N : Term d) : Formula 1 d := set[d] ⟪
  (∀ a ∈ ⌜N⌝ₛ, ⌜tn_name_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, a)) ∧ ⌜n⌝ₛ ⊆ ⌜N⌝ₛ ∧ ⌜n⌝ₛ ∈ ⌜N⌝ₛ ∧
  (∀ x ∈ ⌜U⌝ₛ, ∃ a ∈ ⌜N⌝ₛ, ⌜kpair0_m⌝ₚ(a, x, x))⟫
derive_free_closed tn_names0_m

theorem tn_names0_delta_l {d} (n U N : Term d) : (tn_names0_m n U N).IsDelta0 :=
  .conj (.forallMem _ (tn_name_delta_l ..)) (.conj (.atom ..)
    (.conj (.mem ..) (.forallMem _ (.existsMem _ (kpair0_delta_l ..)))))

theorem tn_names0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (n U N : Term d) :
    Formula.satisfies ρ (tn_names0_m n U N) ↔ Tn_names_d (n.eval ρ) (U.eval ρ) (N.eval ρ) := by
  simp only [tn_names0_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff,
    tn_name_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨valid, vars, point, constants⟩ a
    refine ⟨valid a, ?_⟩
    rintro (hi | rfl | ⟨x, hx, pair⟩)
    · exact vars a hi
    · exact point
    · obtain ⟨b, hb, code⟩ := constants x hx
      exact kpair_unique_l M hKP.1 code pair ▸ hb
  · intro names
    refine ⟨fun a => (names a).mp, fun a ha => (names a).mpr (Or.inl ha),
      (names (n.eval ρ)).mpr (Or.inr (Or.inl rfl)), fun x hx => ?_⟩
    obtain ⟨a, pair⟩ := (kp_pair_l hKP).total x x
    exact ⟨a, (names a).mpr (Or.inr (Or.inr ⟨x, hx, pair⟩)), pair⟩

def tt_pool0_m {d} (ω X n U D : Term d) : Formula 1 d := set[d] ⟪∃ N ∈ ⌜X⌝ₛ, ∃ E ∈ ⌜X⌝ₛ,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, N, E) ∧
  ⌜rd_graph_m .prod⌝ₚ(⌜ω⌝ₛ, E, ⌜ω⌝ₛ, ⌜D⌝ₛ)⟫
derive_free_closed tt_pool0_m

theorem tt_pool0_delta_l {d} (ω X n U D : Term d) : (tt_pool0_m ω X n U D).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (tn_names0_delta_l ..) (.conj (fs_space0_delta_l ..) (rd_graph_delta_l ..))))

theorem tt_pool0_rank_l (hZF : M.Models ZF) {d δ} (ρ : Env M d) (ω X n U D : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ (X.eval ρ))
    (hδ : M.IsLimitOrdinal δ) (hωX : M.mem (ω.eval ρ) (X.eval ρ))
    (hn : M.mem (n.eval ρ) (ω.eval ρ)) (hU : M.mem (U.eval ρ) (X.eval ρ)) :
    Formula.satisfies ρ (tt_pool0_m ω X n U D) ↔
      Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := v_transitive_l I hX
  have product E : Rd_fun_d .prod (ω.eval ρ) E (ω.eval ρ) (D.eval ρ) ↔
      M.IsCartesianProduct I (D.eval ρ) (ω.eval ρ) E := by
    exact ⟨fun h p => (h p).trans ⟨fun ⟨a, b, ha, hb, pair⟩ => ⟨a, ha, b, hb, pair⟩,
      fun ⟨a, ha, b, hb, pair⟩ => ⟨a, b, ha, hb, pair⟩⟩,
      fun h p => (h p).trans ⟨fun ⟨a, ha, b, hb, pair⟩ => ⟨a, b, ha, hb, pair⟩,
        fun ⟨a, b, ha, hb, pair⟩ => ⟨a, ha, b, hb, pair⟩⟩⟩
  have spaces N E E₀ (seq : Fseq_space_d I (ω.eval ρ) N E₀) (hE : M.mem E₀ (X.eval ρ)) :
      Formula.satisfies ((ρ.push N).push E) (fs_space0_m ω.weaken.weaken X.weaken.weaken Term.newest.weaken .newest) ↔ E = E₀ := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := E₀) ((ρ.push N).push E)
        ω.weaken.weaken X.weaken.weaken Term.newest.weaken .newest
        (by simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
        (by simpa only [Definitional.Term.eval_weaken, Structure.MemberSubset] using trans E₀ hE)
  simp only [tt_pool0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l (ZF.modelsKP hZF), rd_graph_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, product]
  constructor
  · rintro ⟨N, hN, E, _, names, matrix, prod⟩
    obtain ⟨E₀, seq⟩ := ZF.fseq_space_exists_l I hZF hω N
    have hE₀ := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hN seq
    exact ⟨N, E, names, ((spaces N E E₀ seq hE₀).mp matrix).symm ▸ seq, prod⟩
  · rintro ⟨N, E, names, seq, prod⟩
    have hN := names.rank_mem_l (ZF.modelsKP hZF) hω hX hδ hωX hn hU
    have hE := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hN seq
    exact ⟨N, hN, E, hE, names, (spaces N E E seq hE).mpr rfl, prod⟩

end YesMetaZFC.SetTheory.Internal

/-! ## κ 型的固定常量域

常量域恰为 Vκ 与单个 κ 的并；该条件是有界公式。
在任意更高极限秩层中，实际域与全部查询均自动满足所需秩界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tt_constants0_m {d} (κ B U : Term d) : Formula 1 d := set[d] ⟪
  ⌜B⌝ₛ ⊆ ⌜U⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜U⌝ₛ ∧ (∀ x ∈ ⌜U⌝ₛ, x ∈ ⌜B⌝ₛ ∨ x = ⌜κ⌝ₛ)⟫
derive_free_closed tt_constants0_m

theorem tt_constants0_delta_l {d} (κ B U : Term d) : (tt_constants0_m κ B U).IsDelta0 :=
  .conj (.atom ..) (.conj (.mem ..) (.forallMem _ (.disj (.mem ..) (.atom ..))))

theorem tt_constants0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ B U : Term d) :
    Formula.satisfies ρ (tt_constants0_m κ B U) ↔
      ∀ x, M.mem x (U.eval ρ) ↔ M.mem x (B.eval ρ) ∨ x = κ.eval ρ := by
  simp only [tt_constants0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨sub, point, all⟩ x => ⟨all x, fun h => h.elim (sub x) (fun eq => eq.symm ▸ point)⟩,
    fun h => ⟨fun x hx => (h x).mpr (Or.inl hx), (h (κ.eval ρ)).mpr (Or.inr rfl), fun x => (h x).mp⟩⟩

theorem tt_constants_rank_l (hZF : M.Models ZF) {δ Z κ B U : M.Domain}
    (hZ : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hδ : M.IsLimitOrdinal δ) (hκ : M.mem κ δ)
    (hB : V_d (kp_pair_l (ZF.modelsKP hZF)) κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) : M.mem U Z := by
  obtain ⟨B', U', hB', hU', spec⟩ := tt_constants_exists_l hZF hZ hδ hκ
  have eqB := ZF.v_unique_l _ hZF hB' hB
  subst B'
  exact hZF.1.eq_of_same_members U' U (fun x => (spec x).trans (constants x).symm) ▸ hU'

theorem Tt_pool_d.unique_l (hE : Extensional M) (I : kpair_convention_l.Interpretation M)
    {ω n U D E : M.Domain} (h : Tt_pool_d I ω n U D) (k : Tt_pool_d I ω n U E) : D = E :=
  hE.eq_of_same_members D E (fun p => ⟨h.mono_l I k (fun _ h => h) p, k.mono_l I h (fun _ h => h) p⟩)

/-- 非零极限域已有 ω 与每个内部自然数的合法常量名字。 -/
theorem tt_constants_finite_l (hZF : M.Models ZF) {ω κ n B U : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.IsLimitOrdinal κ) (hB : V_d (kp_pair_l (ZF.modelsKP hZF)) κ B) (hc : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) :
    M.mem ω U ∧ M.mem n U := by
  have sub := hω.subset_limitOrdinal (ZF.modelsKP hZF) hκ
  refine ⟨(hc ω).mpr ?_, (hc n).mpr (Or.inl (ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hZF)) hZF hB (sub n hn)))⟩
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).trichotomy hZF.1 hκ.1 (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
  · exact Or.inr (hZF.1.eq_of_same_members ω κ eq)
  · exact Or.inl (ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hZF)) hZF hB lt)
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ (sub κ gt)).elim

end YesMetaZFC.SetTheory.Internal

/-! ## 原公式在完整类型中的实际查询码

给原公式每个参数一个合法名字，就自动编译出类型查询。名字可以重复或置换，
并可同时引用实现元组、指定常量和参数域中的任意集合常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原模板的自然数程序先于任何常量和名字列取定。 -/
structure Tt_program_d (ω z : M.Domain) {d : Nat} (φ : Formula 1 d) : Prop where
  natural : M.mem z ω
  read : ∀ c Z R f (model : Smdl_d I c Z R) (ρ : Env (smdl_structure_l I (R := R) model.2.1) d),
    M.IsSetFunctionFromTo I f ω Z →
    (∀ i x, Num_d i.val x → Rd_entry_d x (ρ.bound i).val f) →
      (Sc_sat_d I ω c z f ↔ Formula.satisfies ρ φ)

theorem tt_program_l {ω : M.Domain} (hω : M.IsOmega ω) {d : Nat}
    (φ : Formula 1 d) (hc : φ.FreeClosed) : ∃ z, ∃ v : Fin d → M.Domain,
      (∀ i, Num_d i.val (v i)) ∧ Tt_program_d hZF ω z φ := by
  obtain ⟨a, m, F, k, v, form, nums, compile⟩ := source_compile_l I hZF hω φ hc
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  refine ⟨z, v, nums, sc_num_natural_l I hZF hω code, fun c Z R f model ρ fn values => ?_⟩
  obtain ⟨E, space⟩ := ZF.exists_functionSpace hZF I ω Z
  exact (sc_sat_decode_l I hZF hω code).trans ((satisfies_decode_l I hZF.1 model form space).trans
    (compile Z R model.2.1 E space f ((space f).mpr fn) ρ (fun i => values i (v i) (nums i))))

/-- 自然数程序与实际名字列组成原查询；证书不包含语义假设。 -/
def Tt_code_d {d : Nat} (n U z p : M.Domain) (a : Fin d → M.Domain) : Prop :=
  ∃ N C b, Tn_names_d n U N ∧ Num_d d b ∧ Fn0_d b N C ∧ KPair_d M p z C ∧
    ∀ i x, Num_d i.val x → Rd_entry_d x (a i) C

theorem tt_code_l {ω n U D z : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D)
    (hz : M.mem z ω) {d : Nat} (v a : Fin d → M.Domain) (hv : ∀ i, Num_d i.val (v i))
    (names : ∀ i, Tn_name_d n U (a i)) : ∃ p, M.mem p D ∧ Tt_code_d n U z p a := by
  obtain ⟨N, E, hN, hE, hD⟩ := pool
  obtain ⟨b, hb⟩ := num_exists_l (ZF.modelsKP hZF) d
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF I b N
  have injective : Function.Injective v := fun i j eq =>
    Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (eq.symm ▸ hv j))
  obtain ⟨e, heB, params⟩ := senv_params_l I hZF hB ⟨n, (hN n).mpr (Or.inr (Or.inl rfl))⟩ v a injective
    (fun i => num_lt_l hZF.1 (hv i) hb i.isLt) (fun i => (hN (a i)).mpr (names i))
  have he := (hB e).mp heB
  obtain ⟨p, hp⟩ := (I).total z e
  have hbω := num_mem_l hZF.1 hω hb
  exact ⟨p, (hD p).mpr ⟨z, hz, e, (hE e).mpr ⟨b, hbω, he⟩, hp⟩,
    N, e, b, hN, hb, fn0_of_function_l (ZF.modelsKP hZF) he, hp,
    fun i x hx => (num_unique_l hZF.1 (hv i) hx) ▸ params i⟩

theorem Tt_code_d.read_l {ω n U D z p : M.Domain} (hω : M.IsOmega ω) (hzω : M.mem z ω)
    {d : Nat} {a : Fin d → M.Domain}
    (pool : Tt_pool_d I ω n U D) (code : Tt_code_d n U z p a) : M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) →
        ∃ f, M.IsSetFunctionFromTo I f ω Z ∧ (∀ i x, Num_d i.val x → Rd_entry_d x (ρ.bound i).val f) ∧
          (M.mem p t ↔ Sc_sat_d I ω c z f) := by
  obtain ⟨N, e, b, hN, hb, fn, hp, params⟩ := code
  obtain ⟨N', E, hN', hE, hD⟩ := pool
  have eq := hZF.1.eq_of_same_members N' N (fun x => (hN' x).trans (hN x).symm)
  subst N'
  have he := fn0_function_l (ZF.modelsKP hZF) fn
  have hbω := num_mem_l hZF.1 hω hb
  have hpD := (hD p).mpr ⟨z, hzω, e, (hE e).mpr ⟨b, hbω, he⟩, hp⟩
  refine ⟨hpD, fun c Z R s δ t h ρ values => ?_⟩
  obtain ⟨r, hr, fnr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n h.finite)
    h.tuple h.point h.constants hN (fn0_of_function_l (ZF.modelsKP hZF) he)
  obtain ⟨f, hf, fnf⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fnr) h.point
  have match_params i x (hx : Num_d i.val x) : Rd_entry_d x (ρ.bound i).val f :=
    (hf.2 x (ρ.bound i).val).mpr ⟨num_mem_l hZF.1 hω hx, Or.inl
      ⟨num_lt_l hZF.1 hx hb i.isLt, (hr.2 x (ρ.bound i).val).mpr ⟨a i, params i x hx, values i⟩⟩⟩
  exact ⟨f, fnf, match_params, (h.truth p).trans ((and_iff_right hpD).trans
    (tt_query_decode_l I (ZF.modelsKP hZF) hp hzω hbω he.2.1 hr hf))⟩

theorem Tt_program_d.query_l {ω n U D z p : M.Domain} (hω : M.IsOmega ω)
    {d : Nat} {φ : Formula 1 d} {a : Fin d → M.Domain} (program : Tt_program_d hZF ω z φ)
    (pool : Tt_pool_d I ω n U D) (code : Tt_code_d n U z p a) : M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) → (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨hp, read⟩ := code.read_l hZF hω program.natural pool
  refine ⟨hp, fun c Z R s δ t h ρ values => ?_⟩
  obtain ⟨f, fn, params, truth⟩ := read c Z R s δ t h ρ values
  exact truth.trans (program.read c Z R f h.model ρ fn params)

/-- 查询在任何类型及实现出现之前固定；同一程序和实际名字列供全部模型读取。 -/
theorem tt_fixed_query_l {ω n U D : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D)
    {d : Nat} (φ : Formula 1 d) (hφ : φ.FreeClosed) (a : Fin d → M.Domain)
    (names : ∀ i, Tn_name_d n U (a i)) : ∃ p, M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) → (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨z, v, nums, program⟩ := tt_program_l hZF hω φ hφ
  obtain ⟨p, hp, code⟩ := tt_code_l hZF hω pool program.natural v a nums names
  exact ⟨p, hp, (program.query_l hZF hω pool code).2⟩

theorem tt_source_l {ω c Z R n s δ U D t : M.Domain}
    (hω : M.IsOmega ω) (h : Tt_realized_d I ω c Z R n s δ U D t)
    {d : Nat} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d) (a : Fin d → M.Domain)
    (names : ∀ i, Tn_name_d n U (a i)) (values : ∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨p, hp, read⟩ := tt_fixed_query_l hZF hω h.pool φ hφ a names
  exact ⟨p, hp, read c Z R s δ t h ρ values⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 有限历史中完整类型的原公式

把已有查询域、真值集合及实现关系写回原语言，供集合内分离合法局面。
原元数和名字列仍取遍内部自然数，不用宿主有限列表代替历史。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def tt_pool_m {d} (ω n U D : Term d) : Formula 1 d := set[d] ⟪∃ N E,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, N, E) ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜D⌝ₛ, ⌜ω⌝ₛ, E)⟫
derive_free_closed tt_pool_m

theorem tt_pool_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n U D : Term d) :
    Formula.satisfies ρ (tt_pool_m ω n U D) ↔ Tt_pool_d I (ω.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) := by
  simp only [tt_pool_m, Tt_pool_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l hKP, fseq_space_sat_l I hKP.1, Formula.satisfies_isCartesianProduct_iff I,
    Definitional.Term.eval_weaken]
  rfl

def tt_truth_m {d} (ω c n s δ D t : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜t⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ ⌜tt_query_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, p)⟫
derive_free_closed tt_truth_m

theorem tt_truth_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c n s δ D t : Term d) :
    Formula.satisfies ρ (tt_truth_m ω c n s δ D t) ↔
      Tt_truth_d I (ω.eval ρ) (c.eval ρ) (n.eval ρ) (s.eval ρ) (δ.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [tt_truth_m, Tt_truth_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, tt_query_sat_l I hKP, Definitional.Term.eval_weaken]
  rfl

def tt_realized0_m : Formula 1 10 :=
  let p : Fin 10 → Term 10 := Term.bound
  set[10] ⟪⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ) ∧ ⌜p 4⌝ₛ ∈ ⌜p 0⌝ₛ ∧
    ⌜fn0_m⌝ₚ(⌜p 4⌝ₛ, ⌜p 2⌝ₛ, ⌜p 5⌝ₛ) ∧ ⌜p 6⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 7⌝ₛ ⊆ ⌜p 2⌝ₛ ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 4⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ) ∧
    ⌜tt_truth_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ)⟫

theorem tt_realized0_closed_l : tt_realized0_m.FreeClosed := by
  simp -implicitDefEqProofs [tt_realized0_m, Definitional.Formula.FreeClosed]

def tt_realized_m {d} (ω c X R n s δ U D t : Term d) : Formula 1 d :=
  tt_realized0_m.bind (fun i => [ω, c, X, R, n, s, δ, U, D, t].get i)

@[simp] theorem tt_realized_closed_l {d} (ω c X R n s δ U D t : Term d)
    (hw : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hn : n.freeSupport = []) (hs : s.freeSupport = []) (hδ : δ.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (ht : t.freeSupport = []) :
    (tt_realized_m ω c X R n s δ U D t).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tt_realized0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hc, hX, hR, hn, hs, hδ, hU, hD, ht, fun i => Fin.elim0 i⟩

theorem tt_realized_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c X R n s δ U D t : Term d) :
    Formula.satisfies ρ (tt_realized_m ω c X R n s δ U D t) ↔
      Tt_realized_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (n.eval ρ) (s.eval ρ)
        (δ.eval ρ) (U.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_mem_iff, fn0_sat_l hKP.1, Formula.satisfies_subset_iff,
    tt_pool_sat_l I hKP, tt_truth_sat_l I hKP]
  exact ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
    fun h => ⟨h.model, h.finite, h.tuple, h.point, h.constants, h.pool, h.truth⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源中实际构造完整名字域

在 n∪{n} 与 U×U 的并中作原名字谓词的有界分离。
因此名字域属于源，无须源满足 KP 或把背景幂集放入源。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tn_names_source_l {ω c X R n U : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : M.mem n X) (hU : M.mem U X) : ∃ N, M.mem N X ∧ Tn_names_d n U N := by
  obtain ⟨m, hm, succ⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).insert_l hn hn
  obtain ⟨P, hP, prod⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).product U U hU hU
  obtain ⟨B, hB, pair⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair m P hm hP
  obtain ⟨D, hD, un⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).union B hB
  have cover a (name : Tn_name_d n U a) : M.mem a D := by
    apply (un a).mpr
    rcases name with hi | rfl | ⟨x, hx, cp⟩
    · exact ⟨m, (pair m).mpr (Or.inl rfl), (succ a).mpr (Or.inl hi)⟩
    · exact ⟨m, (pair m).mpr (Or.inl rfl), (succ a).mpr (Or.inr rfl)⟩
    · exact ⟨P, (pair P).mpr (Or.inr rfl), (prod a).mpr ⟨x, hx, x, hx, cp⟩⟩
  let φ : UnarySchema 2 := { body := tn_name_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 2 := ⟨Fin.cases n (fun _ => U), fun _ => n⟩
  obtain ⟨N, hN, sep⟩ := sc_separate_source_l I hZF hω hX model theory φ (tn_name_delta_l ..)
    ρ (Fin.cases hn (fun _ => hU)) hD
  refine ⟨N, hN, fun a => (sep a).trans ?_⟩
  have read : φ.denote ρ a ↔ Tn_name_d n U a := tn_name_sat_l hZF.1 ..
  exact ⟨fun h => read.mp h.2, fun h => ⟨cover a h, read.mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 像查询域覆盖新的低秩参数

名字域、有限列空间和查询对的定义依次由初等性搬运。目标中的任意实际
有限名字列只需属于目标载体，不必来自旧列的逐点像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 名字、有限列空间与查询乘积的像由同一映射同时读取。 -/
theorem Smap_d.type_frame_l {ω θ X R Y S c d j n U U' D D' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hnω : M.mem n ω) (hnj : Rd_entry_d n n j)
    (hUX : M.mem U X) (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j)
    (pool : Tt_pool_d I ω n U D) :
    ∃ N T N' T', Tn_names_d n U N ∧ Fseq_space_d I ω N T ∧ M.IsCartesianProduct I D ω T ∧
      Rd_entry_d N N' j ∧ Rd_entry_d T T' j ∧
      (∀ a, M.mem a Y → (M.mem a N' ↔ Tn_name_d n U' a)) ∧
      (∀ e, M.mem e Y → (M.mem e T' ↔ ∃ b, M.mem b ω ∧ Fn0_d b N' e)) ∧
      (∀ p, M.mem p Y → (M.mem p D' ↔ ∃ z, M.mem z ω ∧ ∃ e, M.mem e T' ∧ KPair_d M p z e)) := by
  have ht := v_transitive_l I hX
  have hωj := hj.omega_l I hZF hω ht hY hm hn hωX
  obtain ⟨N, T, names, seq, prod⟩ := pool
  have hNX := names.rank_mem_l (ZF.modelsKP hZF) hω hX hθ hωX hnω hUX
  have hTX := ZF.v_fseq_mem_l I hZF hX hθ hω hωX hNX seq
  obtain ⟨N', _, hN⟩ := hj.1.1.2.2 N hNX
  obtain ⟨T', _, hT⟩ := hj.1.1.2.2 T hTX
  -- 名字域中的新常量由 j(U) 决定，变量名仍是同一个内部 n。
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (tn_name_m (.bound 3) (.bound 2) .newest)
  have tr := hj.forall_delta_l hZF hω ht hY hm hn φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (tn_name_delta_l ..))
    ⟨Fin.cases N (Fin.cases U (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases N' (Fin.cases U' (fun _ => n)), fun _ => n⟩ (Fin.cases hN (Fin.cases hU (fun _ => hnj)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, tn_name_sat_l hZF.1] at tr
  have names' : ∀ a, M.mem a Y → (M.mem a N' ↔ Tn_name_d n U' a) := tr.mp (fun a _ => names a)
  -- 同一全称公式覆盖目标中的所有有限列，包括不在旧列像中的列。
  let ψ : Formula 1 4 := .iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))
  have tr := hj.forall_delta_l hZF hω ht hY hm hn ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (.existsMem _ (fn0_delta_l ..)))
    ⟨Fin.cases T (Fin.cases N (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases T' (Fin.cases N' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hT (Fin.cases hN (fun _ => hωj)))
  simp only [ψ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1] at tr
  have seq' : ∀ e, M.mem e Y → (M.mem e T' ↔ ∃ b, M.mem b ω ∧ Fn0_d b N' e) :=
    tr.mp (fun e _ => (seq e).trans (exists_congr fun b => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩))
  let χ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (Formula.existsMem (.bound 3)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := hj.forall_delta_l hZF hω ht hY hm hn χ (by simp -implicitDefEqProofs [χ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases D (Fin.cases T (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases D' (Fin.cases T' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hD (Fin.cases hT (fun _ => hωj)))
  simp only [χ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have prod' : ∀ p, M.mem p Y → (M.mem p D' ↔ ∃ z, M.mem z ω ∧ ∃ e, M.mem e T' ∧ KPair_d M p z e) :=
    tr.mp (fun p _ => prod p)
  exact ⟨N, T, N', T', names, seq, prod, hN, hT, names', seq', prod'⟩

theorem Smap_d.type_pool_cover_l {ω θ X R Y S c d j n U U' D D' V E : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hnω : M.mem n ω) (hnj : Rd_entry_d n n j)
    (hUX : M.mem U X) (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j)
    (pool : Tt_pool_d I ω n U D) (pool' : Tt_pool_d I ω n V E)
    (hVU : M.MemberSubset V U') (hEY : M.MemberSubset E Y) : M.MemberSubset E D' := by
  obtain ⟨N, T, N', T', _, _, _, _, _, names', seq', prod'⟩ :=
    hj.type_frame_l hZF hω hX hθ hωX hY hm hn hnω hnj hUX hU hD pool
  obtain ⟨N₀, T₀, names₀, seq₀, prod₀⟩ := pool'
  intro p hp
  have hpY := hEY p hp
  obtain ⟨z, hz, e, he, code⟩ := (prod₀ p).mp hp
  have heY := (code.mem_l M hY hpY).2
  obtain ⟨b, hb, fn⟩ := (seq₀ e).mp he
  have name_image a i (hia : Rd_entry_d i a e) : M.mem a N' := by
    obtain ⟨q, hq, hqe⟩ := hia
    have haY := (hq.mem_l M hY (hY e heY q hqe)).2
    apply (names' a haY).mpr
    rcases (names₀ a).mp (fn.output_mem_of_pairMember ⟨q, hq, hqe⟩) with ha | ha | ⟨x, hx, pair⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ⟨x, hVU x hx, pair⟩)
  have fn' : M.IsSetFunctionFromTo I e b N' := ⟨fn.1, fn.2.1,
    fun i hi => (fn.2.2 i hi).imp fun a ha => ⟨name_image a i ha.2, ha.2⟩⟩
  exact (prod' p hpY).mpr ⟨z, hz, e, (seq' e heY).mpr ⟨b, hb, fn0_of_function_l (ZF.modelsKP hZF) fn'⟩, code⟩

/-- 目标覆盖 V_L 且 L≤j(κ) 时，j(Vκ) 包含整个实际 V_L。 -/
theorem Smap_d.type_constants_cover_l {ω θ X R Y S c d j κ κ' B U U' L V : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hκ : M.mem κ θ)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hκj : Rd_entry_d κ κ' j) (hU : Rd_entry_d U U' j)
    (hB : V_d I κ B) (hBU : M.MemberSubset B U) (hV : V_d I L V)
    (cover : M.MemberSubset V Y) (bound : M.MemberSubset L κ') : M.MemberSubset V U' := by
  classical
  have ht := v_transitive_l I hX
  have hBX := ZF.v_mem_l I hZF hB hX hκ
  obtain ⟨B', hB'Y, hBB⟩ := hj.1.1.2.2 B hBX
  obtain ⟨P, F, hP, hF, cert, _⟩ := vr_source_l hZF hX hθ hκ hB
  have rank : Vr_d Y κ' B' := (hj.hierarchy_l hZF hω ht hY hm hn hκj hBB).mp
    ⟨P, F, hP, hF, fun t _ => cert t⟩
  have hκ' := hj.ordinal_l hZF hω ht hY hm hn hκj (hθ.1.mem hκ)
  have hκ'Y := hj.1.1.output_mem_of_pairMember hκj
  have hLY : M.mem L Y := by
    by_cases eq : L = κ'
    · exact eq ▸ hκ'Y
    · exact hY κ' hκ'Y L (Structure.IsOrdinal.mem_of_properSubset hZF.1 (v_ordinal_l I hV) hκ'
        ⟨bound, fun hh => eq (hZF.1.eq_of_same_members L κ' hh)⟩ (KP.difference_exists_d (ZF.modelsKP hZF) L κ'))
  have hierarchy := (sc_hierarchy_iff_l hZF hω ht hY hm hn hj).mp (sc_v_hierarchy_l hZF hθ hX)
  obtain ⟨W, hWY, hW⟩ := hierarchy L hLY (v_ordinal_l I hV)
  have eq := vr_agree_l hZF hY hWY hV cover hW
  subst W
  have sub := (rank.compare_l hZF hY hB'Y hWY hW bound).1
  have into := (hj.subset_l hZF hω ht hY hm hn hBB hU).mp hBU
  exact fun x hx => into x (sub x hx)

end YesMetaZFC.SetTheory.Internal
