import YesMetaZFC.Model.SetTheory.Internal.SubtypeQuery

/-! # 定义 3.6 的固定查询码

六个集合常量使用唯一的对角名字，指定常量使用原名字 n。
列的每个位置均由原变量或固定参数槽覆盖，故给定程序后查询码字面唯一。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_names_d (ω n κ τ m w : M.Domain) (v : Fin 7 → M.Domain) : Prop :=
  KPair_d M (v 0) w w ∧ v 1 = n ∧ KPair_d M (v 2) m m ∧ KPair_d M (v 3) n n ∧
    KPair_d M (v 4) τ τ ∧ KPair_d M (v 5) κ κ ∧ KPair_d M (v 6) ω ω

structure Ts_query_d (ω n κ τ m U w b : M.Domain) (σ : Fin 7 → M.Domain) (z q : M.Domain) : Prop where
  constants : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U
  column : ∃ N C, ∃ v : Fin 7 → M.Domain, Tn_names_d n U N ∧ Fn0_d b N C ∧
    (∀ i, M.mem i n → Rd_entry_d i i C) ∧ (∀ i, Rd_entry_d (σ i) (v i) C) ∧
      Ts_names_d ω n κ τ m w v ∧ KPair_d M q z C

/-- 子类型只要求规定的查询属于 u，不要求 u 已有实现。 -/
def Ts_subtype_d (ω n κ τ m U w b : M.Domain) (σ : Fin 7 → M.Domain) (z u : M.Domain) : Prop :=
  M.mem τ κ ∧ M.MemberSubset n m ∧ ∃ q, Ts_query_d ω n κ τ m U w b σ z q ∧ M.mem q u

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.query_exists_l {ω n κ τ m U w D b a z : M.Domain}
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z) (pool : Tt_pool_d I ω n U D)
    (hc : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U) :
    ∃ q, M.mem q D ∧ Ts_query_d ω n κ τ m U w b σ z q := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨v₀, h₀⟩ := (I).total w w
  obtain ⟨v₂, h₂⟩ := (I).total m m
  obtain ⟨v₃, h₃⟩ := (I).total n n
  obtain ⟨v₄, h₄⟩ := (I).total τ τ
  obtain ⟨v₅, h₅⟩ := (I).total κ κ
  obtain ⟨v₆, h₆⟩ := (I).total ω ω
  let v : Fin 7 → M.Domain := Fin.cases v₀ (Fin.cases n (Fin.cases v₂ (Fin.cases v₃
    (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))
  have name x p (hx : M.mem x U) (hp : KPair_d M p x x) : M.mem p N :=
    (names p).mpr (Or.inr (Or.inr ⟨x, hx, hp⟩))
  have valid : ∀ i, M.mem (v i) N := Fin.cases (name w v₀ hc.1 h₀)
    (Fin.cases ((names n).mpr (Or.inr (Or.inl rfl))) (Fin.cases (name m v₂ hc.2.1 h₂)
      (Fin.cases (name n v₃ hc.2.2.1 h₃) (Fin.cases (name τ v₄ hc.2.2.2.1 h₄)
        (Fin.cases (name κ v₅ hc.2.2.2.2.1 h₅) (fun _ => name ω v₆ hc.2.2.2.2.2 h₆))))))
  obtain ⟨C, col, orig, params⟩ := prog.columns U N names v valid
  obtain ⟨q, pair⟩ := (I).total z C
  exact ⟨q, (prod q).mpr ⟨z, prog.natural, C, (seq C).mpr ⟨b, prog.length, col⟩, pair⟩,
    hc, N, C, v, names, fn0_of_function_l (ZF.modelsKP hZF) col, orig, params, ⟨h₀, rfl, h₂, h₃, h₄, h₅, h₆⟩, pair⟩

theorem Ts_query_d.unique_l {ω n κ τ m U w b a z q q' : M.Domain} {σ : Fin 7 → M.Domain}
    (prog : Ts_program_d hZF ω n b σ a z) (h : Ts_query_d ω n κ τ m U w b σ z q)
    (h' : Ts_query_d ω n κ τ m U w b σ z q') : q = q' := by
  obtain ⟨_, N, C, v, names, fc, orig, params, vals, pair⟩ := h
  obtain ⟨_, N', C', v', names', fc', orig', params', vals', pair'⟩ := h'
  have veq : v = v' := funext (Fin.cases (kpair_unique_l M hZF.1 vals.1 vals'.1)
    (Fin.cases (vals.2.1.trans vals'.2.1.symm) (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.1 vals'.2.2.1)
      (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.1 vals'.2.2.2.1)
        (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.1 vals'.2.2.2.2.1)
          (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.2.1 vals'.2.2.2.2.2.1)
            (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.2.2 vals'.2.2.2.2.2.2) (fun i => Fin.elim0 i))))))))
  subst v'
  have carry {N C C' : M.Domain} (fn : Fn0_d b N C)
      (old : ∀ i, M.mem i n → Rd_entry_d i i C) (new : ∀ i, M.mem i n → Rd_entry_d i i C')
      (pa : ∀ i, Rd_entry_d (σ i) (v i) C) (pb : ∀ i, Rd_entry_d (σ i) (v i) C') i x
      (hx : Rd_entry_d i x C) : Rd_entry_d i x C' := by
    have f := fn0_function_l (ZF.modelsKP hZF) fn
    rcases prog.cover i (fn.bound_l hx).1 with hi | ⟨j, rfl⟩
    · exact (f.1.2 i x i hx (old i hi)).symm ▸ new i hi
    · exact (f.1.2 (σ j) x (v j) hx (pa j)).symm ▸ pb j
  have eqC := (fn0_function_l (ZF.modelsKP hZF) fc).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) fc').1.1 (fun i x =>
      ⟨carry fc orig orig' params params' i x, carry fc' orig' orig params' params i x⟩)
  exact kpair_unique_l M hZF.1 pair (eqC.symm ▸ pair')

end YesMetaZFC.SetTheory.Internal
