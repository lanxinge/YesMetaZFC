import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyUnion

/-! # 完整复制树仍为 nice 树

扩展器及支撑逐行由原复制图搬运。实际边证书给出施加一致性；所属
秩段的原 nice 判断向完整工作模型保持；全前驱端点保证新支撑严格递增。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_move_d (H E i q : M.Domain) : Prop := ∃ X A π z Z α p κ ρ F κ' ρ' F',
  Ic_at_d H i X A π z Z α ∧ Rd_entry_d i p E ∧ It_payload_d p κ ρ F ∧
    Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π ∧ It_payload_d q κ' ρ' F'
def ic_move_m {d} (H E i q : Term d) : Formula 1 d := set[d] ⟪
  ∃ X A π z Z α p κ ρ F κ' ρ' F', ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, p, ⌜E⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p, κ, ρ, F) ∧
    ⌜rd_entry0_m⌝ₚ(κ, κ', π) ∧ ⌜rd_entry0_m⌝ₚ(ρ, ρ', π) ∧ ⌜rd_entry0_m⌝ₚ(F, F', π) ∧ ⌜it_payload_m⌝ₚ(⌜q⌝ₛ, κ', ρ', F')⟫
derive_free_closed ic_move_m
theorem ic_move_sat_l (hE : Extensional M) {d} (η : Env M d) (H E i q : Term d) :
    Formula.satisfies η (ic_move_m H E i q) ↔ Ic_move_d (H.eval η) (E.eval η) (i.eval η) (q.eval η) := by
  simp only [ic_move_m, Ic_move_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ic_at_sat_l hE, rd_entry0_sat_l hE, it_payload_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 空码按原值保留，非空码才沿所属行的真实嵌入搬运。 -/
def Ic_operation_d (H E i q : M.Domain) : Prop :=
  (Rd_entry_d i q E ∧ ∀ x, ¬ M.mem x q) ∨ Ic_move_d H E i q
def ic_operation_m {d} (H E i q : Term d) : Formula 1 d := set[d] ⟪
  (⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ⌜q⌝ₛ, ⌜E⌝ₛ) ∧ (∀ x, ¬ x ∈ ⌜q⌝ₛ)) ∨ ⌜ic_move_m⌝ₚ(⌜H⌝ₛ, ⌜E⌝ₛ, ⌜i⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed ic_operation_m
theorem ic_operation_sat_l (hE : Extensional M) {d} (η : Env M d) (H E i q : Term d) :
    Formula.satisfies η (ic_operation_m H E i q) ↔ Ic_operation_d (H.eval η) (E.eval η) (i.eval η) (q.eval η) := by
  simp only [ic_operation_m, Ic_operation_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, ic_move_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ic_operation_d.active_l {H E i q κ ρ F : M.Domain}
    (h : Ic_operation_d H E i q) (pay : It_payload_d q κ ρ F) : Ic_move_d H E i q := by
  rcases h with ⟨_, empty⟩ | h
  · obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := pay
    exact (empty u ((pair u).mpr (Or.inl rfl))).elim
  · exact h

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.nice_l {ω c T Q G E L H Q' G' o X₀ A₀ π₀ c' Z₀ α₀ : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (ho : ∀ x, ¬ M.mem x o) (initial : Ic_at_d H o X₀ A₀ π₀ c' Z₀ α₀) :
    ∃ E' L', It_pnice_d hZF ω c' ω T Q' G' E' L' ∧ ∀ i p, Rd_entry_d i p E' ↔ Ic_operation_d H E i p := by
  classical
  have hω := nice.tree.omega
  have payload (κ ρ F : M.Domain) : ∃ p, It_payload_d p κ ρ F := by
    obtain ⟨r, hr⟩ := (I).total ρ F
    obtain ⟨p, hp⟩ := (I).total κ r
    exact ⟨p, r, hp, hr⟩
  have code_unique {p q κ ρ F : M.Domain} (h : It_payload_d p κ ρ F) (g : It_payload_d q κ ρ F) : p = q := by
    obtain ⟨r, hp, hr⟩ := h
    obtain ⟨s, hq, hs⟩ := g
    exact pn_triple_unique_l hZF.1 ⟨r, hr, hp⟩ ⟨s, hs, hq⟩
  have total i (hi : M.mem i ω) : ∃ q, Ic_operation_d H E i q := by
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
    obtain ⟨p, hp⟩ := (nice.tree.move_domain i).mpr ⟨j, hjω, hj⟩
    by_cases act : ∃ κ ρ F, It_payload_d p κ ρ F
    · obtain ⟨κ, ρ, F, pay⟩ := act
      obtain ⟨c, X, A, π, z, Z, α, here, hc, _, row⟩ := hist.at_l hZF hi
      obtain ⟨R, S, V, a, _, _, _, hm, _, _, _, _, _, _, _, _, hπ⟩ := row
      have strength := (nice.exactness i p κ ρ F c X R hp pay hc hm).1
      obtain ⟨κ', _, hκ⟩ := hπ.1.1.2.2 κ strength.2.1
      obtain ⟨ρ', _, hρ⟩ := hπ.1.1.2.2 ρ strength.2.2.1
      obtain ⟨F', _, hF⟩ := hπ.1.1.2.2 F strength.2.2.2.1
      obtain ⟨q, hq⟩ := payload κ' ρ' F'
      exact ⟨q, Or.inr ⟨X, A, π, z, Z, α, p, κ, ρ, F, κ', ρ', F', here, hp, pay, hκ, hρ, hF, hq⟩⟩
    · obtain ⟨k, c, d, b, f, q, _, _, _, _, _, hq, step⟩ := nice.tree.steps i j hjω hj
      have eq := nice.tree.move_function.2 i q p hq hp
      subst q
      rcases step with ⟨empty, _⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
      · exact ⟨p, Or.inl ⟨hp, empty⟩⟩
      · exact (act ⟨κ, ρ, F, pay⟩).elim
  have read {i p q κ ρ F X A π z Z α} (here : Ic_at_d H i X A π z Z α)
      (hp : Rd_entry_d i p E) (pay : It_payload_d p κ ρ F) (move : Ic_operation_d H E i q) :
      ∃ κ' ρ' F', Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π ∧ It_payload_d q κ' ρ' F' := by
    rcases move with ⟨hq, empty⟩ | move
    · have eq := nice.tree.move_function.2 i p q hp hq
      obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
      exact (empty u ((pair u).mpr (Or.inl rfl))).elim
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, p₁, κ₁, ρ₁, F₁, κ', ρ', F', here', hp', pay', rest⟩ := move
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here'.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have ep := nice.tree.move_function.2 i p₁ p hp' hp
    subst p₁
    obtain ⟨e₁, e₂, e₃⟩ := pay'.unique_l pay
    subst κ₁ ρ₁ F₁
    exact ⟨κ', ρ', F', rest⟩
  have unique i p q (hp : Ic_operation_d H E i p) (hq : Ic_operation_d H E i q) : p = q := by
    rcases hp with ⟨hp, empty⟩ | hp
    · rcases hq with ⟨hq, _⟩ | ⟨_, _, _, _, _, _, r, κ, ρ, F, _, _, _, _, hr, pay, _⟩
      · exact nice.tree.move_function.2 i p q hp hq
      · have eq := nice.tree.move_function.2 i r p hr hp
        obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
        exact (empty u ((pair u).mpr (Or.inl rfl))).elim
    obtain ⟨X, A, π, z, Z, α, r, κ, ρ, F, κ', ρ', F', here, hr, pay, hκ, hρ, hF, hp'⟩ := hp
    obtain ⟨_, _, _, hκ', hρ', hF', hq'⟩ := read here hr pay hq
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hπ⟩ := row
    exact code_unique hp' (hπ.1.1.1.2 κ _ κ' hκ' hκ ▸ hπ.1.1.1.2 ρ _ ρ' hρ' hρ ▸ hπ.1.1.1.2 F _ F' hF' hF ▸ hq')
  let η : Env M 2 := ⟨Fin.cases E (fun _ => H), fun _ => H⟩
  let φ : BinarySchema 2 := { body := ic_operation_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat i p : φ.denote η i p ↔ Ic_operation_d H E i p := ic_operation_sat_l hZF.1 ..
  obtain ⟨B, bs⟩ := ZF.exists_functionalImage hZF φ η ω
    (fun i hi => (total i hi).imp fun p hp => (sat i p).mpr hp)
    (fun i p q hp hq => unique i p q ((sat i p).mp hp) ((sat i q).mp hq))
  obtain ⟨E', ef, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η
    (fun i hi => (total i hi).imp fun p hp => (sat i p).mpr hp)
    (fun i _ p q hp hq => unique i p q ((sat i p).mp hp) ((sat i q).mp hq))
    (fun i p hi hp => (bs p).mpr ⟨i, hi, hp⟩)
  have moves i p : Rd_entry_d i p E' ↔ Ic_operation_d H E i p := (es i p).trans
    ⟨fun h => (sat i p).mp h.2, fun h => ⟨by
      rcases h with ⟨hp, _⟩ | ⟨_, _, _, _, _, _, p, _, _, _, _, _, _, _, hp, _⟩
      all_goals
        obtain ⟨j, hj, succ⟩ := (nice.tree.move_domain i).mp ⟨_, hp⟩
        exact hω.transitive hZF j hj i succ.predecessor_mem, (sat i p).mpr h⟩⟩
  have tree : It_tree_d hZF ω c' ω T Q' G' E' := by
    refine ⟨hω, hist.diagram, ?_, ?_, ef.1, ?_, ?_, ?_⟩
    · intro q hq
      have eq := hZF.1.eq_of_same_members q o (fun x => iff_of_false (hq x) (ho x))
      obtain ⟨_, _, hz, _⟩ := hist.row_l hZF initial
      exact eq.symm ▸ hz
    · intro i a ha
      obtain ⟨c, X, A, π, z, Z, α, _, _, hz, row⟩ := hist.at_l hZF ((hist.diagram.model_domain i).mpr ⟨a, ha⟩)
      have eq := hist.diagram.model_function.2 i a z ha hz
      subst a
      obtain ⟨_, _, V, _, _, _, K, _, _, mz, _, _, full, _⟩ := row
      exact ⟨Z, V, K, mz, full.source⟩
    · intro i
      refine (ef.2.1 i).symm.trans ⟨fun hi => ?_, fun ⟨j, hj, succ⟩ => hω.transitive hZF j hj i succ.predecessor_mem⟩
      obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
      exact ⟨j, hjω, hj⟩
    · intro i j hj succ
      have hi := hω.transitive hZF j hj i succ.predecessor_mem
      by_cases act : ∃ ρ, Rd_entry_d i ρ L
      · obtain ⟨k, b, a, d, f, p, κ, ρ, F, N₀, R₀, X₀, R₁, pred, hb, ha, _, hf, hp, pay, mn, _, loc, _⟩ := nice.step_l hZF hj succ act
        obtain ⟨b₀, N, B, σ, u, U, β, ai, hb₀, hu, own⟩ := hist.at_l hZF hi
        obtain ⟨a₀, X, A, π, z, Z, α, ak, ha₀, hz, row⟩ := hist.at_l hZF (hω.transitive hZF j hj k pred.1)
        obtain ⟨_, P, C, τ, v, V, γ, aj, _, hv, _⟩ := hist.at_l hZF hj
        have eq := nice.tree.diagram.model_function.2 i b₀ b hb₀ hb
        subst b₀
        have eq := nice.tree.diagram.model_function.2 k a₀ a ha₀ ha
        subst a₀
        obtain ⟨g, hg⟩ := hist.diagram.map_l hZF (nice.tree.diagram.map_bound_l hZF hf)
        obtain ⟨κ', ρ', F', hκ, hρ, hF, big, agree⟩ := hist.steps i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g
          succ pred ai ak aj hp pay hg
        obtain ⟨R, S, W, s, _, _, _, mn₀, mb, mu, source, cut, full, hB, rank, limit, hσ⟩ := own
        obtain ⟨en, er⟩ := smdl_unique_l I mn.1 mn₀.1
        subst N₀ R₀
        have ord := (loc.ordinals_l (ZF.modelsKP hZF) source.transitive).1
        have data := loc
        obtain ⟨_, _, _, _, pre⟩ := data
        simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
        have low := (hσ.subset_l hZF hω source.transitive cut.transitive mn₀ mb
          (hσ.omega_l I hZF hω source.transitive cut.transitive mn₀ mb source.omega_mem) hκ).mp (ord.transitive ω pre.1.2.2.1)
        have ord' := hσ.ordinal_l hZF hω source.transitive cut.transitive mn₀ mb hκ ord
        have hkU := full.source.transitive B hB κ' (hσ.1.1.output_mem_of_pairMember hκ)
        obtain ⟨K, owner⟩ := full.source.rebase_l hZF hkU low (sc_ordinal_small_l hZF hω full.source.transitive mu full.source.theory hkU ord')
        have up := (loc.map_l hZF hω source.transitive cut.transitive mn₀ mb hσ hκ hρ hF).of_rank_l hZF owner hB rank limit
        obtain ⟨_, _, Vz, _, _, _, _, _, _, mz, _⟩ := row
        obtain ⟨q, pq⟩ := payload κ' ρ' F'
        exact ⟨k, u, z, v, g, q, pred, hu, hz, hv, hg,
          (moves i q).mpr (Or.inr ⟨N, B, σ, u, U, β, p, κ, ρ, F, κ', ρ', F', ai, hp, pay, hκ, hρ, hF, pq⟩),
          Or.inr ⟨κ', ρ', F', U, W, Z, Vz, pq, mu, mz, up, fun n D A hn hd ha => (agree n D A hn hd ha).symm, big⟩⟩
      · obtain ⟨k, b, a, d, f, p, pred, hb, _, _, _, hp, step⟩ := nice.tree.steps i j hj succ
        have pad : (∀ x, ¬ M.mem x p) ∧ k = i := by
          rcases step with ⟨empty, eq, _⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
          · exact ⟨empty, eq⟩
          · exact (act ⟨ρ, (nice.levels i ρ).mpr ⟨p, κ, F, hp, pay⟩⟩).elim
        obtain ⟨empty, eq⟩ := pad
        subst k
        obtain ⟨b₀, X, A, π, z, Z, α, here, _, hz, _⟩ := hist.at_l hZF hi
        obtain ⟨same, ident⟩ := hist.pads i j p succ hj hp empty
        obtain ⟨r, hr, cell⟩ := here
        have next : Ic_at_d H j X A π z Z α := ⟨r, (same r).mp hr, cell⟩
        obtain ⟨_, _, hz', _⟩ := hist.row_l hZF next
        obtain ⟨g, hg⟩ := hist.diagram.map_l hZF ((pred.2 i).mpr (Or.inr (nice.tree.diagram.order.refl i hi)))
        exact ⟨i, z, z, z, g, p, pred, hz, hz, hz', hg, (moves i p).mpr (Or.inl ⟨hp, empty⟩),
          Or.inl ⟨empty, rfl, rfl, fun x y hxy => ident g x y hg hxy⟩⟩
    · intro δ hδ limit
      obtain ⟨i, hi, succ⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hδ limit.2.1
      exact (it_successor_not_limit_l hZF.1 (hω.members_areOrdinals hZF i hi) succ limit).elim
  -- 支撑列按新操作码读取；函数性由实际三元组唯一性保证。
  let ρ : Env M 1 := ⟨fun _ => E', fun _ => E'⟩
  let ψ : BinarySchema 1 := { body := set[3] ⟪∃ p κ F,
    ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 1 : Term 3)⌝ₛ, p, ⌜(Term.bound 2 : Term 3)⌝ₛ) ∧
    ⌜it_payload_m⌝ₚ(p, κ, ⌜(Term.newest : Term 3)⌝ₛ, F)⟫ }
  have ls i a : ψ.denote ρ i a ↔ ∃ p κ F, Rd_entry_d i p E' ∧ It_payload_d p κ a F := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, it_payload_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  let χ : UnarySchema 1 := { body := .existsE ψ.body, freeClosed := ψ.freeClosed }
  have χs i : χ.denote ρ i ↔ ∃ a, ψ.denote ρ i a := Formula.satisfies_exists_iff _ _
  obtain ⟨D, ds₀⟩ := ZF.separation_exists_d hZF χ ρ ω
  have ds i : M.mem i D ↔ ∃ a, ψ.denote ρ i a := by
    refine (ds₀ i).trans ?_
    change (M.mem i ω ∧ χ.denote ρ i) ↔ _
    rw [χs]
    exact ⟨And.right, fun h => ⟨by
      obtain ⟨a, ha⟩ := h
      obtain ⟨p, _, _, hp, _⟩ := (ls i a).mp ha
      exact ef.input_mem_of_pairMember hp, h⟩⟩
  have lt i (hi : M.mem i D) : ∃ a, ψ.denote ρ i a := (ds i).mp hi
  have lu i a b (ha : ψ.denote ρ i a) (hb : ψ.denote ρ i b) : a = b := by
    obtain ⟨p, κ, F, hp, pay⟩ := (ls i a).mp ha
    obtain ⟨q, μ, G, hq, pay'⟩ := (ls i b).mp hb
    exact (pay.unique_l (ef.1.2 i q p hq hp ▸ pay')).2.1
  obtain ⟨C, cs⟩ := ZF.exists_functionalImage hZF ψ ρ D lt lu
  obtain ⟨L', lf, ls'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ lt (fun i _ => lu i)
    (fun i a hi ha => (cs a).mpr ⟨i, hi, ha⟩)
  have levels i a : Rd_entry_d i a L' ↔ ∃ p κ F, Rd_entry_d i p E' ∧ It_payload_d p κ a F := (ls' i a).trans
    ⟨fun h => (ls i a).mp h.2, fun h => ⟨(ds i).mpr ⟨a, (ls i a).mpr h⟩, (ls i a).mpr h⟩⟩
  refine ⟨E', L', ⟨tree, lf.1, levels, ?_, ?_⟩, moves⟩
  · intro i q κ' ρ' F' c U V hq pq hc mu
    obtain ⟨X, A, π, z, Z, α, p, κ, ρ, F, k, r, f, here, hp, pay, hκ, hρ, hF, pay'⟩ := ((moves i q).mp hq).active_l pq
    obtain ⟨e₁, e₂, e₃⟩ := pay'.unique_l pq
    subst k r f
    obtain ⟨b, hb, hz, row⟩ := hist.row_l hZF here
    have eq := hist.diagram.model_function.2 i c z hc hz
    subst c
    obtain ⟨R, S, V₀, a, _, _, _, mx, ma, mz, source, cut, full, hA, rank, limit, hπ⟩ := row
    obtain ⟨eu, ev⟩ := smdl_unique_l I mu.1 mz.1
    subst U V
    obtain ⟨strength, card⟩ := nice.exactness i p κ ρ F b X R hp pay hb mx
    exact ⟨(strength.map_l hZF hω source.transitive cut.transitive mx ma hπ cut.theory hκ hρ hF).of_rank_l hZF
      full.source.transitive hA rank limit,
      (card.map_l hZF hω source.transitive cut.transitive mx ma hπ hρ).of_rank_l hZF
        full.source.transitive full.source.theory.algebra.pair hA rank limit⟩
  · intro i j a b hi hj hij
    obtain ⟨p', κ', F', hp', pp'⟩ := (levels i a).mp hi
    obtain ⟨q', μ', G', hq', qq'⟩ := (levels j b).mp hj
    obtain ⟨X, A, π, z, Z, α, p, κ, ρ, F, _, a₀, _, ai, hp, pp, _, hρ, _, pp₀⟩ := ((moves i p').mp hp').active_l pp'
    obtain ⟨Y, B, σ, u, U, β, q, μ, ψ, F₀, _, b₀, _, aj, hq, qq, _, hψ, _, qq₀⟩ := ((moves j q').mp hq').active_l qq'
    have ea := (pp₀.unique_l pp').2.1
    have eb := (qq₀.unique_l qq').2.1
    subst a₀ b₀
    have hρL := (nice.levels i ρ).mpr ⟨p, κ, F, hp, pp⟩
    obtain ⟨ν', same, _⟩ := (hist.past i j X A π z Z α Y B σ u U β ai aj hij).active_l
      (ZF.modelsKP hZF) nice.function hρL
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF ai
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hπ⟩ := row
    have eq := hπ.1.1.1.2 ρ ν' a same.left_end hρ
    subst ν'
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF aj
    obtain ⟨R, S, _, c, _, _, _, my, mb, _, source, cut, _, _, _, _, hσ⟩ := row
    have lt := nice.increasing i j ρ ψ hρL ((nice.levels j ψ).mpr ⟨q, μ, F₀, hq, qq⟩) hij
    exact ((mb.2 a b).mp ((hσ.relation_l I hZF hω my.1 mb.1 same.right_end hψ).mp
      ((my.2 ρ ψ).mpr ⟨hσ.1.1.input_mem_of_pairMember same.right_end, hσ.1.1.input_mem_of_pairMember hψ, lt⟩))).2.2

/-- 给定首行自动复制整棵 nice 树，同时返回全部工作模型和原根嵌入。 -/
theorem Ic_row_d.copy_l (hZFC : M.Models ZFC) {ω c X A π z Z α o T Q G E L : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (row : Ic_row_d (ZFC.models_zf_l hZFC) ω c X A π z Z α) (ho : ∀ x, ¬ M.mem x o) :
    ∃ H Q' G' E' L', Ic_history_d (ZFC.models_zf_l hZFC) ω T Q G E L ω H T Q' G' ∧
      It_pnice_d (ZFC.models_zf_l hZFC) ω z ω T Q' G' E' L' ∧ Ic_at_d H o X A π z Z α ∧
      ∀ i p, Rd_entry_d i p E' ↔ Ic_operation_d H E i p := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨D, f, s₀, H₀, S₀, Q₀, G₀, fn, first, pack, start, valid, chain⟩ := row.sequence_l hZFC nice ho
  obtain ⟨H, Q', G', hist, kept⟩ := ic_sequence_union_l hZF nice.tree.omega nice.tree.diagram fn valid chain
  obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := start
  have first : Ic_at_d H o X A π z Z α := ⟨r, ⟨p, pair, (kept o s₀ H₀ S₀ Q₀ G₀ first pack).1 p hp⟩, cell⟩
  obtain ⟨E', L', copied, moves⟩ := hist.nice_l hZF nice ho first
  exact ⟨H, Q', G', E', L', hist, copied, first, moves⟩

end YesMetaZFC.SetTheory.LargeCardinal
