import YesMetaZFC.Model.SetTheory.Internal.SubtypeUp
import YesMetaZFC.Model.SetTheory.Internal.TypeMinusMatrix

/-! # 子类型查询的有界闭包性质

只固定自然数程序码、列长度和 ω 的槽位；其余名字任意变化。
量词全部有界，故这条统一闭包性质可由实际成员满嵌入运输。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_up_d (I : kpair_convention_l.Interpretation M) (ω b v z N E D u : M.Domain) : Prop :=
  ∀ C, M.mem C E → Fn0_d b N C →
    (∃ e, M.mem e N ∧ KPair_d M e ω ω ∧ Rd_entry_d v e C) →
    ∀ p, M.mem p D → ∀ r, M.mem r D → KPair_d M p z C → Tm_query_d I ω p r → M.mem r u → M.mem p u

def ts_up0_m {d} (ω b v z B N E D u : Term d) : Formula 1 d := set[d] ⟪
  ∀ C ∈ ⌜E⌝ₛ, ⌜fn0_m⌝ₚ(⌜b⌝ₛ, ⌜N⌝ₛ, C) →
    (∃ e ∈ ⌜N⌝ₛ, ⌜kpair0_m⌝ₚ(e, ⌜ω⌝ₛ, ⌜ω⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, e, C)) →
    ∀ p ∈ ⌜D⌝ₛ, ∀ r ∈ ⌜D⌝ₛ, ⌜kpair0_m⌝ₚ(p, ⌜z⌝ₛ, C) →
      ⌜tm_link0_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, p, r) → r ∈ ⌜u⌝ₛ → p ∈ ⌜u⌝ₛ⟫
derive_free_closed ts_up0_m

theorem ts_up0_delta_l {d} (ω b v z B N E D u : Term d) : (ts_up0_m ω b v z B N E D u).IsDelta0 :=
  .forallMem _ (.imp (fn0_delta_l ..) (.imp (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.imp (tm_link0_delta_l ..) (.imp (.mem ..) (.mem ..))))))))

theorem ts_up0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω b v z B N E D u : Term d)
    (table : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (ts_up0_m ω b v z B N E D u) ↔
      Ts_up_d (kp_pair_l hKP) (ω.eval ρ) (b.eval ρ) (v.eval ρ) (z.eval ρ)
        (N.eval ρ) (E.eval ρ) (D.eval ρ) (u.eval ρ) := by
  have link C p r := tm_link0_sat_l hKP (((ρ.push C).push p).push r) ω.weaken.weaken.weaken B.weaken.weaken.weaken
    (Term.newest : Term (d+2)).weaken .newest (by simpa only [Definitional.Term.eval_weaken] using table)
  simp only [ts_up0_m, Ts_up_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, link, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.closure_l {ω n b a z ν μ X Y c R d S s δ U N E D u : M.Domain}
    (hω : M.IsOmega ω) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (hs : M.SuccessorOf μ ν)
    (lower : Smem_d Q c X R) (upper : Smem_d Q d Y S)
    (type : Tt_realized_d Q ω d Y S n s δ U D u)
    (tuple : Fn0_d n X s) (point : M.mem δ X) (constants : M.MemberSubset U X) (names : Tn_names_d n U N) :
    Ts_up_d Q ω b (σ 6) z N E D u := by
  intro C _ column ⟨e, _, codeω, edgeω⟩ p hp r _ pair tm hr
  have fc := fn0_function_l (ZF.modelsKP hZF) column
  have hz := sc_num_natural_l Q hZF hω prog.code
  obtain ⟨t, assign, ft⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n prog.finite)
    tuple point constants names column
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) ft) point
  have restrict := tm.sat_l hZF hω lower upper (ZF.v_transitive_l Q hZF hY)
    (sr_top_power_l (ZF.v_successor_l Q hZF hX hY hs)) pair hz prog.length fc.2.1 assign fill
    (fn0_of_function_l (ZF.modelsKP hZF) ff)
  have decode : Tt_query_d Q ω c n s δ p ↔ Satisfies_d Q ω c a f :=
    (tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length fc.2.1 assign fill).trans
    (sc_sat_decode_l Q hZF hω prog.code)
  have truth := decode.mp (restrict.mpr ((type.truth r).mp hr).2)
  have fw : Rd_entry_d (σ 6) ω f := (fill.2 (σ 6) ω).mpr
    ⟨hω.transitive hZF b prog.length (σ 6) (prog.slots 6),
      Or.inl ⟨fc.input_mem_of_pairMember edgeω, (assign.2 (σ 6) ω).mpr ⟨e, edgeω, Or.inr (Or.inr codeω)⟩⟩⟩
  have raised := prog.up_l hZF hω hX hY (fun x hx => (hs x).mpr (Or.inl hx)) lower upper ff fw truth
  exact (type.truth p).mpr ⟨hp, (tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length fc.2.1 assign fill).mpr
    ((sc_sat_decode_l Q hZF hω prog.code).mpr raised)⟩

end YesMetaZFC.SetTheory.Internal
