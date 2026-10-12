import YesMetaZFC.Model.SetTheory.Internal.TransitiveCofinalFormula
import YesMetaZFC.Model.SetTheory.Internal.SourcePower

/-! # 所属模型中的原始不可达性

正则性使用原始共尾度定义，强极限性使用原始幂集基数定义。
任意包含 κ 的秩层直接回收共尾图与单射图；不要求该秩层满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_inaccessible_m {d} (ω κ : Term d) : Formula 1 d := .conj (.mem ω κ)
  (.conj (Formula.isRegularCardinal kpair_convention_l κ) (Formula.isStrongLimitCardinal kpair_convention_l κ))
derive_free_closed sc_inaccessible_m

def Sc_inaccessible_d (ω X κ : M.Domain) : Prop :=
  ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X, Formula.satisfies
    (⟨Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩), fun _ => ⟨ω, hω⟩⟩ : Env (rt_model_l X ⟨⟨ω, hω⟩⟩) 2)
    (sc_inaccessible_m (.bound 1) .newest)

theorem sc_inaccessible_sat_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (ω κ : Term d) :
    Formula.satisfies ρ (sc_inaccessible_m ω κ) ↔ Sc_inaccessible_d (ω.eval ρ).val X (κ.eval ρ).val := by
  let J := rt_pair_l hX nx hE hp
  simp only [Sc_inaccessible_d, sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hE hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hE hX nx)]
  exact ⟨fun h => ⟨(ω.eval ρ).property, (κ.eval ρ).property, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- 内部正则性的实际共尾见证保证该序数在背景中也是极限序数。 -/
theorem Sc_inaccessible_d.limit_l (hKP : M.Models KP) {ω X κ : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (h : Sc_inaccessible_d ω X κ) : M.IsLimitOrdinal κ := by
  obtain ⟨hω, hκ, h⟩ := h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let J := rt_pair_l hX nx hKP.1 hp
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hKP.1 hX nx)] at h
  exact (rt_limit_l hX nx hKP ⟨κ, hκ⟩).mp h.2.1.isLimitOrdinal

/-- 完整初等图传输原始公式，不把目标内部不可达性提升为背景不可达性。 -/
theorem Sc_inaccessible_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ κ' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hκ : Rd_entry_d κ κ' j)
    (h : Sc_inaccessible_d ω X κ) : Sc_inaccessible_d ω Y κ' := by
  obtain ⟨hωX, hκX, h⟩ := h
  have hωj := hj.omega_l _ hZF hω hX hY hm hn hωX
  have hωY := hj.1.1.output_mem_of_pairMember hωj
  have hκY := hj.1.1.output_mem_of_pairMember hκ
  let ρ : Env (rt_model_l X ⟨⟨ω, hωX⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ, hκX⟩ (fun _ => ⟨ω, hωX⟩), fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ', hκY⟩ (fun _ => ⟨ω, hωY⟩), fun _ => ⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact ⟨hωY, hκY, (spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩
    ⟨⟨ω, hωX⟩⟩ ⟨⟨ω, hωY⟩⟩ (sc_inaccessible_m (.bound 1) .newest) (by simp -implicitDefEqProofs)
    ρ η (Fin.cases hκ (fun _ => hωj))).mp h⟩

/-- 极限 Vκ 中的坐标编码仍在 Vκ，故整个函数图属于任意包含 κ 的秩层。 -/
theorem sc_rank_graph_l (hZF : M.Models ZF) {δ X κ K A B f : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hκ : M.mem κ X)
    (limit : M.IsLimitOrdinal κ) (hK : V_d (kp_pair_l (ZF.modelsKP hZF)) κ K)
    (hA : M.MemberSubset A K) (hB : M.MemberSubset B K)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f A B) : M.mem f X := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hKX := ZF.v_mem_l I hZF hK hX (ZF.v_ordinal_height_l hZF hX limit.1 hκ)
  have pair := sc_v_pair_l hZF limit hK
  apply ZF.v_subset_mem_l I hZF hX hKX
  intro p hp
  obtain ⟨a, b, code⟩ := hf.1.1 p hp
  have ha := hA a (hf.input_mem_of_pairMember ⟨p, code, hp⟩)
  have hb := hB b (hf.output_mem_of_pairMember ⟨p, code, hp⟩)
  obtain ⟨s, hs, ps⟩ := pair a a ha ha
  obtain ⟨t, ht, pt⟩ := pair a b ha hb
  obtain ⟨q, hq, pq⟩ := pair s t hs ht
  have cp : KPair_d M q a b := ⟨s, t, fun z => (ps z).trans ⟨fun h => h.elim id id, Or.inl⟩, pt, pq⟩
  exact kpair_unique_l M hZF.1 cp code ▸ hq
/-- 任意包含 κ 的秩层都正确读取其不可达性；无需层高为极限。
    图中每个有序对属于 Vκ，故整张图属于外层。 -/
theorem sc_v_inaccessible_l (hZF : M.Models ZF) {δ X ω κ : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hκ : M.mem κ X) (above : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP hZF)) κ) : Sc_inaccessible_d ω X κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  have hω := ht κ hκ ω above
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  let ρ : Env N 2 := ⟨Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩), fun _ => ⟨ω, hω⟩⟩
  obtain ⟨K, hK⟩ := ZF.v_exists_l I hZF hr.1.1
  have kt := ZF.v_transitive_l I hZF hK
  have graph {A B f} := @sc_rank_graph_l M hZF δ X κ K A B f hX hκ hr.isLimitOrdinal hK
  have cardinal := rt_cardinal_formula_l (ZF.modelsKP hZF) ht nx ρ (.bound 0) hr.1
  refine ⟨hω, hκ, ?_⟩
  change Formula.satisfies ρ (sc_inaccessible_m (.bound 1) .newest)
  simp only [sc_inaccessible_m, Formula.isRegularCardinal, Formula.isCofinality,
    Formula.isStrongLimitCardinal, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.hasCofinalOrdinalSequence, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 ht nx),
    rt_cofinal_formula_l (ZF.modelsKP hZF) ht nx, Formula.satisfies_forallMem_iff,
    Formula.satisfies_isPowerSet_iff, Formula.cardinalLess, Formula.cardinalLessOrEqual,
    Formula.equinumerous, Formula.satisfies_neg_iff,
    rt_injection_formula_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    rt_bijection_formula_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push,
    Term.eval_bound_one_push]
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    have hf := graph (ZF.v_ordinal_subset_l I hZF hK) (ZF.v_ordinal_subset_l I hZF hK) cf.isSetFunctionFromTo
    obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
    exact ⟨⟨f, hf⟩, cf, R, ZF.v_subset_mem_l I hZF hX hκ (cf.range_isCofinalSubset hZF.1 range).2.1, range⟩
  · rintro μ ⟨f, hf, _⟩
    exact (hr.2.2 μ.val ⟨f.val, hf⟩).imp Subtype.ext id
  · intro a ha P power
    have pow : M.IsPowerSetOf P.val a.val := by
      intro B
      refine ⟨fun hb x hx => ?_, fun sub => ?_⟩
      · exact (power ⟨B, ht P.val P.property B hb⟩).mp hb ⟨x, ht B (ht P.val P.property B hb) x hx⟩ hx
      · exact (power ⟨B, ZF.v_subset_mem_l I hZF hX a.property sub⟩).mpr (fun x hx => sub x.val hx)
    have hPK := ZF.v_power_mem_l I hZF hK hr.isLimitOrdinal (ZF.v_ordinal_mem_l I hZF hK ha) pow
    obtain ⟨⟨f, hf⟩, not_bij⟩ := hs.2 a.val ha P.val pow
    exact ⟨⟨⟨f, graph (kt P.val hPK) (ZF.v_ordinal_subset_l I hZF hK) hf.1⟩, hf⟩,
      fun ⟨g, hg⟩ => not_bij ⟨g.val, hg⟩⟩

end YesMetaZFC.SetTheory.Internal