import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax

/-! # 子类型查询的定义域参数更换

只更换名字列中较大定义域的槽位；候选类型、实际元组和排列均不变。
统一性质只在常量域、名字列空间和查询域内量化，因而可搬到超幂的新查询。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_rebound_d (ω n b z U N E D t : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∀ κ, M.mem κ U → ∀ ξ, M.mem ξ U → ∀ τ, M.mem τ U → ∀ m, M.mem m ω → ∀ w, M.mem w U →
    M.IsLimitOrdinal κ ∧ M.IsLimitOrdinal ξ ∧ M.IsLimitOrdinal τ ∧ M.mem τ κ ∧ M.mem τ ξ →
    ∀ C, M.mem C E → Ts_column_d ω n κ τ m N w b σ C →
    ∀ C', M.mem C' E → Ts_column_d ω n ξ τ m N w b σ C' →
    ∀ q, M.mem q D → ∀ q', M.mem q' D → KPair_d M q z C → KPair_d M q' z C' →
      (M.mem q t ↔ M.mem q' t)

def ts_rebound_m {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  let l₅ (x : Term d) := x.weaken.weaken.weaken.weaken.weaken
  let l₆ (x : Term d) := (l₅ x).weaken
  let l₇ (x : Term d) := (l₆ x).weaken
  let l₉ (x : Term d) := (l₇ x).weaken.weaken
  let last : Formula 1 (d+9) := .imp (kpair0_m (.bound 1) (l₉ z) (.bound 3))
    (.imp (kpair0_m .newest (l₉ z) (.bound 2)) (.iff (.mem (.bound 1) (l₉ t)) (.mem .newest (l₉ t))))
  let second : Formula 1 (d+7) := .imp
    (ts_column_m (l₇ ω) (l₇ n) (.bound 5) (.bound 4) (.bound 3) (l₇ N) (.bound 2) (l₇ b) .newest (fun i => l₇ (σ i)))
    (Formula.forallMem (l₇ D) (Formula.forallMem (l₇ D).weaken last))
  let first : Formula 1 (d+6) := .imp
    (ts_column_m (l₆ ω) (l₆ n) (.bound 5) (.bound 3) (.bound 2) (l₆ N) (.bound 1) (l₆ b) .newest (fun i => l₆ (σ i)))
    (Formula.forallMem (l₆ E) second)
  let guard : Formula 1 (d+5) := .conj (KP.limit0_m (.bound 4)) (.conj (KP.limit0_m (.bound 3))
    (.conj (KP.limit0_m (.bound 2)) (.conj (.mem (.bound 2) (.bound 4)) (.mem (.bound 2) (.bound 3)))))
  Formula.forallMem U (Formula.forallMem U.weaken (Formula.forallMem U.weaken.weaken
    (Formula.forallMem ω.weaken.weaken.weaken (Formula.forallMem U.weaken.weaken.weaken.weaken
      (.imp guard (Formula.forallMem (l₅ E) first))))))

@[simp] theorem ts_rebound_closed_l {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hU : U.freeSupport = []) (hN : N.freeSupport = []) (hE : E.freeSupport = []) (hD : D.freeSupport = [])
    (ht : t.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) : (ts_rebound_m ω n b z U N E D t σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_rebound_m, Definitional.Formula.FreeClosed, hw, hn, hb, hz, hU, hN, hE, hD, ht, hσ]

theorem ts_rebound_delta_l {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) :
    (ts_rebound_m ω n b z U N E D t σ).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (KP.limit0_delta_l ..) (.conj (KP.limit0_delta_l ..) (.conj (KP.limit0_delta_l ..) (.conj (.mem ..) (.mem ..)))))
      (.forallMem _ (.imp (ts_column_delta_l ..) (.forallMem _ (.imp (ts_column_delta_l ..)
        (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.imp (kpair0_delta_l ..) (.iff (.mem ..) (.mem ..)))))))))))))))

theorem ts_rebound_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_rebound_m ω n b z U N E D t σ) ↔ Ts_rebound_d
      (ω.eval ρ) (n.eval ρ) (b.eval ρ) (z.eval ρ) (U.eval ρ) (N.eval ρ) (E.eval ρ) (D.eval ρ) (t.eval ρ)
      (fun i => (σ i).eval ρ) := by
  simp only [ts_rebound_m, Ts_rebound_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, KP.limit0_sat_l hKP, Formula.satisfies_mem_iff, ts_column_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_iff_iff, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.rebound_l {ω n b a z η Y c R s δ U N E D t : M.Domain}
    (hω : M.IsOmega ω) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t)
    (names : Tn_names_d n U N) (hωU : M.mem ω U) (hωsub : M.MemberSubset ω U) : Ts_rebound_d ω n b z U N E D t σ := by
  intro κ hκU ξ hξU τ hτU m hm w hw ⟨hκ, hξ, hτ, hτκ, hτξ⟩ C _ col C' _ col' q _ q' _ pair pair'
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hτ.1
  obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) τ τ
  obtain ⟨V, hV⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B p
  have constants x : M.mem x V ↔ M.mem x B ∨ x = τ :=
    (hV x).trans (or_congr Iff.rfl ((hp x).trans ⟨fun h => h.elim id id, Or.inl⟩))
  obtain ⟨Q, pool⟩ := tt_pool_exists_l I hZF hω m V
  have cq := col.query_l names ⟨hw, hωsub m hm, hωsub n prog.finite, hτU, hκU, hωU⟩ pair
  have cq' := col'.query_l names ⟨hw, hωsub m hm, hωsub n prog.finite, hτU, hξU, hωU⟩ pair'
  exact (cq.read_l hZF hω prog hY model type hκ hτ hτκ hm hB constants pool).trans
    (cq'.read_l hZF hω prog hY model type hξ hτ hτξ hm hB constants pool).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 实际初等像中的完整类型查询域

名字域用有界原式运输；目标的内部有限函数闭性恢复全部新列。
结论识别完整查询域，不限于旧查询的逐点像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.type_full_l {ω θ X R Y S c d j n U U' D D' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (theory : Sc_theory_d I ω Y S) (hnω : M.mem n ω)
    (hUX : M.mem U X) (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j)
    (pool : Tt_pool_d I ω n U D) :
    ∃ N E N' E', Tn_names_d n U N ∧ Fseq_space_d I ω N E ∧ M.IsCartesianProduct I D ω E ∧
      Rd_entry_d N N' j ∧ Rd_entry_d E E' j ∧ Tn_names_d n U' N' ∧ Fseq_space_d I ω N' E' ∧ M.IsCartesianProduct I D' ω E' := by
  have trans := v_transitive_l I hX
  have fixed := hj.natural_l hZF hω trans hY hm hn hωX
  have hw := hj.omega_l I hZF hω trans hY hm hn hωX
  obtain ⟨N, E, N', E', names, seq, prod, hN, hE, _⟩ :=
    hj.type_frame_l hZF hω hX hθ hωX hY hm hn hnω (fixed n hnω) hUX hU hD pool
  have names' := smap_delta_l I hZF hω trans hY hm hn hj (n := 3)
    (tn_names0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (tn_names0_delta_l ..)
    ⟨Fin.cases N (Fin.cases U (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases N' (Fin.cases U' (fun _ => n)), fun _ => n⟩ (Fin.cases hN (Fin.cases hU (fun _ => fixed n hnω)))
  simp only [tn_names0_sat_l (ZF.modelsKP hZF)] at names'
  have prod' := smap_delta_l I hZF hω trans hY hm hn hj (n := 3)
    (rd_graph_m .prod (.bound 2) (.bound 1) (.bound 2) .newest)
    (by simp -implicitDefEqProofs) (rd_graph_delta_l ..)
    ⟨Fin.cases D (Fin.cases E (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases D' (Fin.cases E' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hD (Fin.cases hE (fun _ => hw)))
  simp only [rd_graph_sat_l (ZF.modelsKP hZF)] at prod'
  have product : M.IsCartesianProduct I D' ω E' := fun p => (prod'.mp (fun p => (prod p).trans
    ⟨fun ⟨a, ha, b, hb, cp⟩ => ⟨a, b, ha, hb, cp⟩, fun ⟨a, b, ha, hb, cp⟩ => ⟨a, ha, b, hb, cp⟩⟩) p).trans
    ⟨fun ⟨a, b, ha, hb, cp⟩ => ⟨a, ha, b, hb, cp⟩, fun ⟨a, ha, b, hb, cp⟩ => ⟨a, b, ha, hb, cp⟩⟩
  exact ⟨N, E, N', E', names, seq, prod, hN, hE, names'.mp names,
    hj.sequences_l hZF hω trans hY hm hn theory hωX hN hE seq, product⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型定义域更换的实际初等像

完整类型先满足统一的有界更换性质，再整体搬运到目标中的全部查询。
原投影查询的成员性本身保证它的常量属于像域，无须假设一个额外的秩覆盖。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.rebound_l {ω c d X R Y S j n b z U N E D t U' N' E' D' t' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j) (hωX : M.mem ω X)
    {σ : Fin 7 → M.Domain} (hnω : M.mem n ω) (hb : M.mem b ω) (hz : M.mem z ω) (hσ : ∀ i, M.mem (σ i) ω)
    (hu : Rd_entry_d U U' j) (hN : Rd_entry_d N N' j) (hE : Rd_entry_d E E' j)
    (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j) :
    Ts_rebound_d ω n b z U N E D t σ ↔ Ts_rebound_d ω n b z U' N' E' D' t' σ := by
  let ρ (U N E D t : M.Domain) : Env M 16 := ⟨Fin.cases t (Fin.cases D (Fin.cases E (Fin.cases N
    (Fin.cases U (Fin.cases z (Fin.cases b (Fin.cases n (Fin.cases ω σ)))))))), fun _ => ω⟩
  let slots : Fin 7 → Term 16 := fun i => .bound ⟨i.val + 9, by omega⟩
  let φ : Formula 1 16 := ts_rebound_m (.bound 8) (.bound 7) (.bound 6) (.bound 5)
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest slots
  have fixed := hj.natural_l hZF hω hX hY hm hn hωX
  have hw := hj.omega_l I hZF hω hX hY hm hn hωX
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ
    (by simp -implicitDefEqProofs [φ, slots]) (ts_rebound_delta_l ..) (ρ U N E D t) (ρ U' N' E' D' t')
    (Fin.cases ht (Fin.cases hD (Fin.cases hE (Fin.cases hN (Fin.cases hu (Fin.cases (fixed z hz)
      (Fin.cases (fixed b hb) (Fin.cases (fixed n hnω) (Fin.cases hw (fun i => fixed (σ i) (hσ i)))))))))))
  have read U N E D t : Formula.satisfies (ρ U N E D t) φ ↔ Ts_rebound_d ω n b z U N E D t σ := by
    dsimp only [φ]
    rw [ts_rebound_sat_l (ZF.modelsKP hZF)]
    have eq : (fun i => (slots i).eval (ρ U N E D t)) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) i
    exact eq ▸ Iff.rfl
  exact (read U N E D t).symm.trans (tr.trans (read U' N' E' D' t'))

theorem Smap_d.subtype_rebound_l {ω θ X R Y S c d j n b a z U D t U' D' t' η A c₀ R₀ r δ
    κ ξ τ m V w : M.Domain} {σ : Fin 7 → M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (theory : Sc_theory_d I ω Y S)
    (prog : Ts_program_d hZF ω n b σ a z) (hUX : M.mem U X)
    (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j)
    (hA : V_d I η A) (model : Smem_d I c₀ A R₀) (type : Tt_realized_d I ω c₀ A R₀ n r δ U D t)
    (hωU : M.mem ω U) (nat : M.MemberSubset ω U)
    (hκ : M.IsLimitOrdinal κ) (hξ : M.IsLimitOrdinal ξ) (hτ : M.IsLimitOrdinal τ)
    (hτξ : M.mem τ ξ) (hξU : M.mem ξ U') (hmm : M.mem m ω)
    (subtype : Ts_subtype_d ω n κ τ m V w b σ z t') : Ts_subtype_d ω n ξ τ m U' w b σ z t' := by
  obtain ⟨N, E, N', E', names, seq, prod, hN, hE, names', seq', prod'⟩ :=
    hj.type_full_l hZF hω hX hθ hωX hY hm hn theory prog.finite hUX hU hD type.pool
  have full : Tt_pool_d I ω n U' D' := ⟨N', E', names', seq', prod'⟩
  have closed := prog.rebound_l hZF hω hA model type names hωU nat (E := E)
  have image := (hj.rebound_l hZF hω (v_transitive_l I hX) hY hm hn hωX prog.finite prog.length
    (sc_num_natural_l I hZF hω prog.code) (fun i => hω.transitive (ZF.modelsKP hZF) b prog.length (σ i) (prog.slots i)) hU hN hE hD ht).mp closed
  have sub := (hj.subset_l hZF hω (v_transitive_l I hX) hY hm hn ht hD).mp
    (fun p hp => ((type.truth p).mp hp).1)
  obtain ⟨hτκ, nm, q, code, hq⟩ := subtype
  have code' := code.pool_l (ZF.modelsKP hZF) (hω.members_areOrdinals (ZF.modelsKP hZF) n prog.finite) full (sub q hq)
  obtain ⟨q', hq', query⟩ := prog.query_exists_l hZF full
    ⟨code'.constants.1, code'.constants.2.1, code'.constants.2.2.1, code'.constants.2.2.2.1, hξU, code'.constants.2.2.2.2.2⟩
  obtain ⟨C, col, cq⟩ := code'.column_l hZF.1 names'
  obtain ⟨C', col', cq'⟩ := query.column_l hZF.1 names'
  have truth := image κ code'.constants.2.2.2.2.1 ξ hξU τ code'.constants.2.2.2.1 m hmm w code'.constants.1
    ⟨hκ, hξ, hτ, hτκ, hτξ⟩ C ((seq' C).mpr ⟨b, prog.length, fn0_function_l (ZF.modelsKP hZF) col.1⟩) col
    C' ((seq' C').mpr ⟨b, prog.length, fn0_function_l (ZF.modelsKP hZF) col'.1⟩) col' q (sub q hq) q' hq' cq cq'
  exact ⟨hτξ, nm, q', query, truth.mp hq⟩

end YesMetaZFC.SetTheory.Internal
