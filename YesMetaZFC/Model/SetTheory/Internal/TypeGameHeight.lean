import YesMetaZFC.Model.SetTheory.Internal.TypeGameMax

/-! # 规则 (7) 的末位加二最大序数

原公式在源中构造两个后继，再检查最大序数。查询精确等价于
实现高度等于末位加三；所有后继对象均实际回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_height_d (α η : M.Domain) : Prop :=
  ∃ β γ, M.SuccessorOf β α ∧ M.SuccessorOf γ β ∧ M.SuccessorOf η γ

/-- α<ν 且 ν+1<α+3 时，ν 必为 α+1。 -/
theorem Tg_height_d.gap_l (hE : Extensional M) (hirr : ∀ x, ¬ M.mem x x) {α η ν ρ : M.Domain}
    (h : Tg_height_d α η) (oη : M.IsOrdinal η) (hαν : M.mem α ν)
    (succ : M.SuccessorOf ρ ν) (gap : M.mem ρ η) : M.SuccessorOf ν α := by
  obtain ⟨β, γ, hb, hg, last⟩ := h
  have oγ := oη.mem last.predecessor_mem
  have oν := oη.mem (oη.transitive ρ gap ν succ.predecessor_mem)
  have hnγ : M.mem ν γ := by
    rcases (last ρ).mp gap with lt | eq
    · exact oγ.transitive ρ lt ν succ.predecessor_mem
    · exact (eq ν).mp succ.predecessor_mem
  rcases (hg ν).mp hnγ with lt | eq
  · rcases (hb ν).mp lt with lt | eq
    · exact (hirr ν (oν.transitive α hαν ν lt)).elim
    · exact (hirr ν ((hE.eq_of_same_members ν α eq).symm ▸ hαν)).elim
  · exact (hE.eq_of_same_members ν β eq).symm ▸ hb

def tg_height_m {d} (α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ (∃ β γ, ⌜Formula.isSuccessor⌝ₚ(β, ⌜α⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(γ, β) ∧ ⌜sv_max_m⌝ₚ(γ))⟫
derive_free_closed tg_height_m

def Tg_height_query_d (I : kpair_convention_l.Interpretation M) (ω l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ η X c R r δ T α, V_d I η X → Smem_d I c X R →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d l α r → (M.mem q T ↔ Tg_height_d α η)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_height_source_l {η X : M.Domain} (hX : V_d I η X) (nx : Nonempty {x // M.mem x X})
    {d} (ρ : Env (rt_model_l X nx) d) (α : Term d) :
    Formula.satisfies ρ (tg_height_m α) ↔ Tg_height_d (α.eval ρ).val η := by
  have trans := ZF.v_transitive_l I hZF hX
  simp only [tg_height_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    rt_ordinal_iff_l trans nx (ZF.modelsKP hZF), Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, rt_successor_l trans nx hZF.1, sv_max_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨_, β, γ, hb, hg, last⟩
    exact ⟨β.val, γ.val, hb, hg, sv_max_successor_l hZF hX nx γ last⟩
  · rintro ⟨β, γ, hb, hg, last⟩
    have og := (v_ordinal_l I hX).mem last.predecessor_mem
    have ob := og.mem hg.predecessor_mem
    have oa := ob.mem hb.predecessor_mem
    have hγX := ZF.v_ordinal_mem_l I hZF hX last.predecessor_mem
    have hβX := trans γ hγX β hg.predecessor_mem
    let b : (rt_model_l X nx).Domain := ⟨β, hβX⟩
    let g : (rt_model_l X nx).Domain := ⟨γ, hγX⟩
    refine ⟨oa, b, g, hb, hg, rt_ordinal_l trans nx g og, fun a ha x hx => ?_⟩
    have oa' := (rt_ordinal_iff_l trans nx (ZF.modelsKP hZF) a).mp ha
    rcases (last a.val).mp (ZF.v_ordinal_height_l hZF hX oa' a.property) with lt | eq
    · exact og.transitive a.val lt x.val hx
    · exact (eq x.val).mp hx

theorem tt_height_query_l {ω l n U D : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l n) (pool : Tt_pool_d I ω n U D) : ∃ q, Tg_height_query_d I ω l n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (tg_height_m .newest)
    (tg_height_m_freeClosed _ rfl) (fun _ : Fin 1 => l) (fun _ => Or.inl hl)
  refine ⟨q, hq, fun η X c R r δ T α hX model type rα => ?_⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨α, (type.tuple.bound_l rα).2⟩⟩
  let ρ : Env (rt_model_l X nx) 1 :=
    ⟨fun _ => ⟨α, (type.tuple.bound_l rα).2⟩, fun _ => ⟨α, (type.tuple.bound_l rα).2⟩⟩
  let ξ : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨ρ.bound, ρ.free⟩
  exact (read c X R r δ T type ξ (fun _ => Or.inl rα)).trans
    ((smem_formula_l I model nx (tg_height_m .newest) ρ).symm.trans (tg_height_source_l hZF hX nx ρ .newest))

end YesMetaZFC.SetTheory.Internal
