import YesMetaZFC.Model.SetTheory.Internal.TypeNames
import YesMetaZFC.Model.SetTheory.Internal.CanonicalSatisfaction
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable

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
  obtain ⟨r, hr, fnr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n hn)
    hs hδ hU names (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨f, hf, fnf⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fnr) hδ
  exact ⟨z, b, e, r, f, code, hz, hb, fn.2.1, hr, hf, fn0_of_function_l (ZF.modelsKP hZF) fnf,
    tt_query_decode_l I (ZF.modelsKP hZF) code hz hb fn.2.1 hr hf⟩

end YesMetaZFC.SetTheory.Internal
