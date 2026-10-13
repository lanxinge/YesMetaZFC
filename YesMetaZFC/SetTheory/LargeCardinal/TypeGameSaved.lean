import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRound
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 历轮回答的完整原模型记录

记录先保存 ω 和共同秩段，再保存原轮的五十四个坐标。域、常量域、查询域
和完整回答都属于该共同层；原实现、弹性和任意排列证书仍在原反射层内。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_saved_record0_m : Formula 1 56 := .conj
  (tg_round0_m.rename (fun i => i.succ.succ))
  (set[56] ⟪⌜(.bound 18 : Term 56)⌝ₛ = ⌜(.bound 0 : Term 56)⌝ₛ ∧
    ⌜(.bound 17 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 15 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 14 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 13 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ⟫)

theorem tg_saved_record0_closed_l : tg_saved_record0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_saved_record0_m, Definitional.Formula.FreeClosed, tg_round0_closed_l]

def Tg_saved_code_d (ω V q : M.Domain) (v : Fin 54 → M.Domain) : Prop :=
  Rt_tuple_d (Fin.cases ω (Fin.cases V v)) q

structure Tg_saved_d (hZF : M.Models ZF) (ω Y R μ K η C L V q : M.Domain) : Prop where
  source : Ic_model_d hZF ω μ K Y R
  context : Tg_context_d ω Y η C
  limit : M.IsLimitOrdinal L
  member : M.mem V C
  rank : Vr_d Y L V
  record : Rt_record_in_d tg_saved_record0_m C q
  head : ∃ r, Rd_triple_d q ω V r

def tg_saved_m {d} (ω Y R μ K η C L V q : Term d) : Formula 1 d := .conj
  (ic_model_m ω μ K Y R) (.conj (tg_context_data_m ω Y η C) (.conj
    (set[d] ⟪⌜Formula.isLimitOrdinal⌝ₚ(⌜L⌝ₛ) ∧ ⌜V⌝ₛ ∈ ⌜C⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜L⌝ₛ, ⌜V⌝ₛ) ∧
      (∃ r, ⌜rd_triple0_m⌝ₚ(⌜q⌝ₛ, ⌜ω⌝ₛ, ⌜V⌝ₛ, r))⟫)
    (rt_record_in_m tg_saved_record0_m C q)))

@[simp] theorem tg_saved_closed_l {d} (ω Y R μ K η C L V q : Term d)
    (hw : ω.freeSupport = []) (hY : Y.freeSupport = []) (hR : R.freeSupport = [])
    (hμ : μ.freeSupport = []) (hK : K.freeSupport = []) (hη : η.freeSupport = [])
    (hC : C.freeSupport = []) (hL : L.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_saved_m ω Y R μ K η C L V q).FreeClosed := by
  simp -implicitDefEqProofs [tg_saved_m, Definitional.Formula.FreeClosed, hw, hY, hR, hμ, hK, hη, hC, hL, hV, hq]
  exact rt_record_in_closed_l _ _ _ tg_saved_record0_closed_l hC hq

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_saved_sat_l {d} (ρ : Env M d) (ω Y R μ K η C L V q : Term d) :
    Formula.satisfies ρ (tg_saved_m ω Y R μ K η C L V q) ↔
      Tg_saved_d hZF (ω.eval ρ) (Y.eval ρ) (R.eval ρ) (μ.eval ρ) (K.eval ρ) (η.eval ρ)
        (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [tg_saved_m, Formula.satisfies_conj_iff, ic_model_sat_l hZF, tg_context_data_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_mem_iff, pn_rank_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_exists_iff, rd_triple0_sat_l hZF.1, rt_record_in_sat_l _ _ _ _ tg_saved_record0_closed_l,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨s, c, ⟨l, m, v, a⟩, r⟩ => ⟨s, c, l, m, v, r, a⟩,
    fun h => ⟨h.source, h.context, ⟨h.limit, h.member, h.rank, h.head⟩, h.record⟩⟩

/-- 从原记录恢复同一完整回答；四个低坐标的值没有经过重新选择。 -/
theorem Tg_saved_d.read_l {ω Y R μ K η C L V q : M.Domain}
    (h : Tg_saved_d hZF ω Y R μ K η C L V q) (nc : Nonempty {x // M.mem x C}) :
    ∃ ρ : Env (rt_model_l C nc) 54, Tg_saved_code_d ω V q (fun i => (ρ.bound i).val) ∧
      Formula.satisfies ρ tg_round0_m ∧ (ρ.bound 16).val = ω ∧
      M.mem (ρ.bound 15).val V ∧ M.mem (ρ.bound 13).val V ∧
      M.mem (ρ.bound 12).val V ∧ M.mem (ρ.bound 11).val V := by
  have fs := (h.context.read_l hZF h.source.source).1
  obtain ⟨_, v, tuple, valid⟩ := (rt_record_in_read_l hZF tg_saved_record0_m tg_saved_record0_closed_l fs.transitive nc).mp h.record
  obtain ⟨a, ab, b, ac, tail⟩ := tuple
  obtain ⟨r, s, hs, hq⟩ := h.head
  obtain ⟨hw, eq⟩ := kpair_injective_l M ab hq
  subst s
  obtain ⟨hV, _⟩ := kpair_injective_l M ac hs
  obtain ⟨round, links⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have round := (Formula.satisfies_rename ..).mp round
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 fs.transitive nc),
    Formula.satisfies_mem_iff] at links
  exact ⟨⟨fun i => v i.succ.succ, fun _ => v 0⟩, ⟨a, hw ▸ ab, b, hV ▸ ac, tail⟩, round,
    (congrArg Subtype.val links.1).trans hw, hV ▸ links.2.1, hV ▸ links.2.2.1,
    hV ▸ links.2.2.2.1, hV ▸ links.2.2.2.2⟩

/-- 每个实际回答都能在自己的反射层内保存为一个集合。 -/
theorem Tg_context_d.save_l {ω Y R μ K η C L V : M.Domain}
    (context : Tg_context_d ω Y η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (low : M.mem (ρ.bound 15).val V ∧ M.mem (ρ.bound 13).val V ∧
      M.mem (ρ.bound 12).val V ∧ M.mem (ρ.bound 11).val V) :
    ∃ q, Tg_saved_d hZF ω Y R μ K η C L V q ∧ Tg_saved_code_d ω V q (fun i => (ρ.bound i).val) := by
  have fs := (context.read_l hZF source.source).1
  have tuple {k} (v : Fin (k+1) → (rt_model_l C nc).Domain) :
      ∃ r, M.mem r C ∧ Rt_tuple_d (fun i => (v i).val) r := by
    induction k with
    | zero => exact ⟨(v 0).val, (v 0).property, rfl⟩
    | succ k ih =>
      obtain ⟨r, hr, tail⟩ := ih (fun i => v i.succ)
      let r₀ : (rt_model_l C nc).Domain := ⟨r, hr⟩
      obtain ⟨q, pair⟩ := (rt_pair_l fs.transitive nc hZF.1 fs.pair).total (v 0) r₀
      exact ⟨q.val, q.property, r,
        (rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair q (v 0) r₀).mp pair, tail⟩
  let v : Fin 56 → (rt_model_l C nc).Domain := Fin.cases ⟨ω, context.omega⟩ (Fin.cases ⟨V, member⟩ ρ.bound)
  let ε : Env (rt_model_l C nc) 56 := ⟨v, fun _ => v 0⟩
  have same : (ε.reindex (fun i : Fin 54 => i.succ.succ)).bound = ρ.bound := rfl
  have original : Formula.satisfies (ε.reindex (fun i : Fin 54 => i.succ.succ)) tg_round0_m :=
    (Formula.closed_env_l tg_round0_m tg_round0_closed_l same).mpr valid
  obtain ⟨q, hq, code⟩ := tuple v
  have head : ∃ r, Rd_triple_d q ω V r := by
    obtain ⟨s, hs, r, hr, _⟩ := code
    exact ⟨r, s, hr, hs⟩
  refine ⟨q, ⟨source, context, limit, member, rank, ?_, head⟩, code⟩
  apply (rt_record_in_read_l hZF tg_saved_record0_m tg_saved_record0_closed_l fs.transitive nc).mpr
  refine ⟨hq, v, code, (Formula.satisfies_conj_iff ..).mpr ⟨?_, ?_⟩⟩
  · exact (Formula.satisfies_rename ε (fun i : Fin 54 => i.succ.succ) tg_round0_m).mpr original
  · simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 fs.transitive nc),
      Formula.satisfies_mem_iff]
    exact ⟨Subtype.ext hw, low⟩

/-- 实际超幂支撑已界住完整回答；其余三个低坐标由原弹性语言自动回收。 -/
theorem Tg_context_d.save_round_l {ω Y R μ K η C L V : M.Domain}
    (context : Tg_context_d ω Y η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V) :
    ∃ q, Tg_saved_d hZF ω Y R μ K η C L V q ∧ Tg_saved_code_d ω V q (fun i => (ρ.bound i).val) := by
  have hV := source.source.transitive C context.member V member
  have hτ := rank.ordinal_subset_l hZF source.source.transitive hV _ below
  have body := (Formula.satisfies_conj_iff ..).mp valid |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at body
  have language := body.2.2.2.2.2.2.1
  let f : Fin 10 → Term 54 := fun i => [.bound 16, .bound 15, .bound 24, .bound 14, .bound 13,
    .bound 12, .bound 6, .bound 5, .bound 4, .bound 3].get i
  let ε := Definitional.Env.substitute ρ f
  have language : Formula.satisfies ε ee_language0_m := (Formula.satisfies_bind ρ f ee_language0_m).mp language
  have facts := language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at facts
  have fs := (context.read_l hZF source.source).1
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp facts.2.1)
  have hω := rank.subset_mem_l source.source.transitive hV hτ source.source.omega_mem
    (source.source.omega.subset_limitOrdinal hZF hκ)
  obtain ⟨_, _, low, _⟩ := context.language_rank_l hZF nc ε source.source hV rank limit hω hτ hw language
  exact context.save_l hZF source nc ρ valid hw limit member rank ⟨hτ, low 4, low 5, answer⟩

end YesMetaZFC.SetTheory.LargeCardinal
