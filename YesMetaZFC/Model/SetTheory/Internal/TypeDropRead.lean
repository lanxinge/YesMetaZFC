import YesMetaZFC.Model.SetTheory.Internal.TypeDropSyntax

/-! # 投影查询与原完整满足关系一致

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
  have on := hω.members_areOrdinals hZF n hn
  have om := hω.members_areOrdinals hZF m type.finite
  obtain ⟨v, assign, fv⟩ := tn_assign_exists_l hZF on fs type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) ff)
  obtain ⟨h, fill, _⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fv) type.point
  have assign' := column.assign_l hZF on om fs type.tuple type.point type.constants kept names ff assign
  exact (tt_query_decode_l I (ZF.modelsKP hZF) cp hz hb ff.2.1 assign fill).trans
    (tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb (column.domain_l I ff.2.1) assign' fill).symm

end YesMetaZFC.SetTheory.Internal
