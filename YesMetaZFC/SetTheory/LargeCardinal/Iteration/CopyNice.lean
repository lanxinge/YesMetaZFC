import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 已实施复制步的原生支撑证据

工作扩展器的质量直接从历史中的实际后继读取。工作环境的不可达支撑
先限制到同一工作秩段，再沿原复制图回拉；原模型无需传递隶属呈示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 只读取已进入历史的实际后继，不要求历史已经具有长度 ω。 -/
theorem Ic_history_d.quality_l {ω T Q G E L m H S Q' G' i j p κ ρ F X A π z Z α : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (here : Ic_at_d H i X A π z Z α) (hp : Rd_entry_d i p E) (pay : It_payload_d p κ ρ F)
    (hj : M.mem j m) (succ : M.SuccessorOf j i) (step : It_step_d hZF ω T Q G E i j) :
    ∃ κ' ρ' F', Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π ∧
      Ic_quality_d hZF ω κ' ρ' F' z Z := by
  obtain ⟨k,_,_,_,_,_,pred,_⟩ := step
  have hk := hist.diagram.order.ordinal.transitive j hj k pred.1
  obtain ⟨_,Y,B,σ,u,U,β,parent,_,_,_⟩ := hist.at_l hZF hk
  obtain ⟨_,P,C,τ,v,V,γ,next,_,_,_⟩ := hist.at_l hZF hj
  have kk := ((hist.order k k).mp (hist.diagram.order.refl k hk)).1
  obtain ⟨g,hg⟩ := hist.diagram.map_l hZF
    ((hist.order k j).mpr ⟨(pred.2 k).mpr (Or.inr kk),hj⟩)
  obtain ⟨κ',ρ',F',hκ,hρ,hF,_,_,good⟩ :=
    hist.steps i j k X A π z Z α Y B σ u U β P C τ v V γ p κ ρ F g
      succ pred here parent next hp pay hg
  exact ⟨κ',ρ',F',hκ,hρ,hF,good⟩

/-- 工作环境中的真实不可达性经秩限制和同一复制图返回原模型。 -/
theorem Ic_row_d.inaccessible_l {ω c X A π z Z α R w s L φ : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (mx : Smdl_d I c X R)
    (numbers : Rr_layer_d I ω X R w s) (ext : Rf_ext_d I X R)
    (image : Rd_entry_d L φ π) (card : Sc_inaccessible_d ω Z φ) :
    Rr_truth_d I X R (sc_inaccessible_m (.bound 1) .newest) (Fin.cases L (fun _ : Fin 1 => w)) := by
  obtain ⟨R₀,S,V,a,K,K',model,ma,_,source,ambient,hA,rank,limit,copy⟩ := row
  have eq := (smdl_unique_l I model mx).2
  subst R₀
  have small := card.rank_l hZF ambient.source.transitive
    (ambient.source.algebra_l (ZF.modelsKP hZF)).pair hA rank limit
    (copy.1.1.output_mem_of_pairMember image)
  have iw := (numbers.omega_image_mem_l I hZF source.omega ext mx ma source.transitive copy).1
  obtain ⟨hw,hφ,truth⟩ := small
  let ψ : Formula 1 2 := sc_inaccessible_m (.bound 1) .newest
  let η : Env (rt_model_l A ⟨⟨ω,hw⟩⟩) 2 :=
    ⟨Fin.cases ⟨φ,hφ⟩ (fun _ => ⟨ω,hw⟩),fun _ => ⟨ω,hw⟩⟩
  have closed : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ]
  let ε : Env (smdl_structure_l I (R := S) ma.1.2.1) 2 := ⟨η.bound,η.free⟩
  let ε₀ : Env (smdl_structure_l I (R := S) ma.1.2.1) 2 := ⟨η.bound,fun _ => η.bound 0⟩
  have native : Formula.satisfies ε ψ := (smem_formula_l I ma _ ψ η).mp truth
  have coords : (fun i => (η.bound i).val) = Fin.cases φ (fun _ : Fin 1 => ω) :=
    funext (Fin.cases rfl (fun _ => rfl))
  have fact : Rr_truth_d I A S ψ (Fin.cases φ (fun _ : Fin 1 => ω)) :=
    coords ▸ (rr_truth_native_l I ma.1.2.1 ψ closed η.bound).mpr
      ((Formula.closed_env_l ψ closed (ρ := ε) (η := ε₀) rfl).mp native)
  exact fact.pull_l I hZF source.omega mx ma.1 copy closed (Fin.cases image (fun _ => iw))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整复制树仍为 nice 树

扩展器及支撑逐行由原复制图搬运。已实施的边保存同一工作扩展器的
实际质量和施加一致性；历史的支撑次序保证严格递增。原节点只用原关系
模型，不要求原树另有字面 nice 判断。
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
    (original : It_tree_d hZF ω c ω T Q G E)
    (levels₀ : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (ho : ∀ x, ¬ M.mem x o) (initial : Ic_at_d H o X₀ A₀ π₀ c' Z₀ α₀) :
    ∃ E' L', It_pnice_d hZF ω c' ω T Q' G' E' L' ∧ ∀ i p, Rd_entry_d i p E' ↔ Ic_operation_d H E i p := by
  classical
  have hω := original.omega
  have payload (κ ρ F : M.Domain) : ∃ p, It_payload_d p κ ρ F := by
    obtain ⟨r, hr⟩ := (I).total ρ F
    obtain ⟨p, hp⟩ := (I).total κ r
    exact ⟨p, r, hp, hr⟩
  have code_unique {p q κ ρ F : M.Domain} (h : It_payload_d p κ ρ F) (g : It_payload_d q κ ρ F) : p = q := by
    obtain ⟨r, hp, hr⟩ := h
    obtain ⟨s, hq, hs⟩ := g
    exact pn_triple_unique_l hZF.1 ⟨r, hr, hp⟩ ⟨s, hs, hq⟩
  have quality {i p κ ρ F X A π z Z α} (here : Ic_at_d H i X A π z Z α)
      (hp : Rd_entry_d i p E) (pay : It_payload_d p κ ρ F) :
      ∃ κ' ρ' F', Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π ∧
        Ic_quality_d hZF ω κ' ρ' F' z Z := by
    have hi := (hist.domain i).mpr (here.imp fun _ h => h.1)
    obtain ⟨j, succ, hj⟩ := hω.1.2 i hi
    exact hist.quality_l hZF here hp pay hj succ (original.steps i j hj succ)
  have total i (hi : M.mem i ω) : ∃ q, Ic_operation_d H E i q := by
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
    obtain ⟨p, hp⟩ := (original.move_domain i).mpr ⟨j, hjω, hj⟩
    by_cases act : ∃ κ ρ F, It_payload_d p κ ρ F
    · obtain ⟨κ, ρ, F, pay⟩ := act
      obtain ⟨c, X, A, π, z, Z, α, here, hc, _, row⟩ := hist.at_l hZF hi
      obtain ⟨κ', ρ', F', hκ, hρ, hF, _⟩ := quality here hp pay
      obtain ⟨q, hq⟩ := payload κ' ρ' F'
      exact ⟨q, Or.inr ⟨X, A, π, z, Z, α, p, κ, ρ, F, κ', ρ', F', here, hp, pay, hκ, hρ, hF, hq⟩⟩
    · obtain ⟨k, c, d, b, f, q, _, _, _, _, _, hq, step⟩ := original.steps i j hjω hj
      have eq := original.move_function.2 i q p hq hp
      subst q
      rcases step with ⟨empty, _⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
      · exact ⟨p, Or.inl ⟨hp, empty⟩⟩
      · exact (act ⟨κ, ρ, F, pay⟩).elim
  have read {i p q κ ρ F X A π z Z α} (here : Ic_at_d H i X A π z Z α)
      (hp : Rd_entry_d i p E) (pay : It_payload_d p κ ρ F) (move : Ic_operation_d H E i q) :
      ∃ κ' ρ' F', Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π ∧ It_payload_d q κ' ρ' F' := by
    rcases move with ⟨hq, empty⟩ | move
    · have eq := original.move_function.2 i p q hp hq
      obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
      exact (empty u ((pair u).mpr (Or.inl rfl))).elim
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, p₁, κ₁, ρ₁, F₁, κ', ρ', F', here', hp', pay', rest⟩ := move
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here'.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have ep := original.move_function.2 i p₁ p hp' hp
    subst p₁
    obtain ⟨e₁, e₂, e₃⟩ := pay'.unique_l pay
    subst κ₁ ρ₁ F₁
    exact ⟨κ', ρ', F', rest⟩
  have unique i p q (hp : Ic_operation_d H E i p) (hq : Ic_operation_d H E i q) : p = q := by
    rcases hp with ⟨hp, empty⟩ | hp
    · rcases hq with ⟨hq, _⟩ | ⟨_, _, _, _, _, _, r, κ, ρ, F, _, _, _, _, hr, pay, _⟩
      · exact original.move_function.2 i p q hp hq
      · have eq := original.move_function.2 i r p hr hp
        obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
        exact (empty u ((pair u).mpr (Or.inl rfl))).elim
    obtain ⟨X, A, π, z, Z, α, r, κ, ρ, F, κ', ρ', F', here, hr, pay, hκ, hρ, hF, hp'⟩ := hp
    obtain ⟨_, _, _, hκ', hρ', hF', hq'⟩ := read here hr pay hq
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hπ⟩ := row
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
        obtain ⟨j, hj, succ⟩ := (original.move_domain i).mp ⟨_, hp⟩
        exact hω.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem, (sat i p).mpr h⟩⟩
  have roots q (hq : ∀ x, ¬ M.mem x q) : Rd_entry_d q c' Q' := by
    have eq := hZF.1.eq_of_same_members q o (fun x => iff_of_false (hq x) (ho x))
    obtain ⟨_, _, hz, _⟩ := hist.row_l hZF initial
    exact eq.symm ▸ hz
  have sources i a (ha : Rd_entry_d i a Q') : It_source_d hZF ω a := by
    obtain ⟨c, X, A, π, z, Z, α, _, _, hz, row⟩ := hist.at_l hZF ((hist.diagram.model_domain i).mpr ⟨a, ha⟩)
    have eq := hist.diagram.model_function.2 i a z ha hz
    subst a
    obtain ⟨_, _, V, _, _, _, _, _, mz, _, full, _⟩ := row
    exact it_source_mem_l hZF mz full.source
  have tree : It_tree_d hZF ω c' ω T Q' G' E' := by
    refine {
      omega := hω
      diagram := hist.diagram
      root := roots
      move_function := ef.1
      move_domain := ?_
      steps := ?_
      limits := ?_
      sources := sources }
    · intro i
      refine (ef.2.1 i).symm.trans ⟨fun hi => ?_, fun ⟨j, hj, succ⟩ => hω.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem⟩
      obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
      exact ⟨j, hjω, hj⟩
    · intro i j hj succ
      have hi := hω.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem
      by_cases act : ∃ ρ, Rd_entry_d i ρ L
      · obtain ⟨k, b, a, d, f, p, pred, hb, ha, _, hf, hp, op⟩ := original.steps i j hj succ
        have active : It_active_d hZF ω b a d f p := by
          rcases op with ⟨empty, _⟩ | op
          · obtain ⟨ρ, hiρ⟩ := act
            obtain ⟨q, κ, F, hq, pay⟩ := (levels₀ i ρ).mp hiρ
            have eq := original.move_function.2 i q p hq hp
            obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
            exact (empty u ((pair u).mpr (Or.inl rfl))).elim
          · exact op
        obtain ⟨κ, ρ, F, _, _, _, _, pay, _⟩ := active
        obtain ⟨b₀, N, B, σ, u, U, β, ai, hb₀, hu, own⟩ := hist.at_l hZF hi
        obtain ⟨a₀, X, A, π, z, Z, α, ak, ha₀, hz, row⟩ := hist.at_l hZF (hω.transitive (ZF.modelsKP hZF) j hj k pred.1)
        obtain ⟨_, P, C, τ, v, V, γ, aj, _, hv, _⟩ := hist.at_l hZF hj
        have eq := original.diagram.model_function.2 i b₀ b hb₀ hb
        subst b₀
        have eq := original.diagram.model_function.2 k a₀ a ha₀ ha
        subst a₀
        obtain ⟨g, hg⟩ := hist.diagram.map_l hZF (original.diagram.map_bound_l hZF hf)
        obtain ⟨κ', ρ', F', hκ, hρ, hF, big, agree, good⟩ := hist.steps i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g
          succ pred ai ak aj hp pay hg
        obtain ⟨_, _, W, _, _, _, _, _, mu, _, full, _, _, _, _⟩ := own
        obtain ⟨Rᵤ, _, _, code, up, strong, card⟩ := good
        have eq := (smdl_unique_l I code.1 mu.1).2
        subst Rᵤ
        have ord' := (up.ordinals_l (ZF.modelsKP hZF) full.source.transitive ⟨u, mu⟩).1
        have data := up
        obtain ⟨hwU, hkU, _, _, pre⟩ := (it_local_mem_l I ⟨u, mu⟩).mp data
        simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
        have low := ord'.transitive ω pre.1.2.2.1
        obtain ⟨K, owner⟩ := full.source.rebase_l hkU low
          (sc_ordinal_small_l hZF hω full.source.transitive mu full.source.theory hkU ord')
        obtain ⟨_, _, Vz, _, _, _, _, _, mz, _, parentFull, _⟩ := row
        -- 同一工作扩展器的质量和共同有限幂恢复父模型中的实际施加。
        have reverse : Ea_agree_d ω κ' U Z := fun n D A hn hd ha => (agree n D A hn hd ha).symm
        obtain ⟨Kp, parent⟩ := reverse.subset_l.alphabet_l hZF owner parentFull.source ord'
        obtain ⟨_, powers, _, _⟩ := full.read_l hZF
        have family := (up.measures_l hZF hω (owner.read_source_l hZF) owner.code owner.theory
          (fun _ D _ hd _ => powers D hd)).transfer_l reverse
        have coherent := (up.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
        -- 复制历史给出的这条真实坍塌边，产生相同目标与映射的原关系活动证书。
        obtain ⟨q, pq, copied⟩ := big.active_l hZF (owner.read_source_l hZF) mu owner.theory
          parent mz up reverse family coherent
        exact ⟨k, u, z, v, g, q, pred, hu, hz, hv, hg,
          (moves i q).mpr (Or.inr ⟨N, B, σ, u, U, β, p, κ, ρ, F, κ', ρ', F', ai, hp, pay, hκ, hρ, hF, pq⟩),
          Or.inr copied⟩
      · obtain ⟨k, b, a, d, f, p, pred, hb, _, _, _, hp, step⟩ := original.steps i j hj succ
        have pad : (∀ x, ¬ M.mem x p) ∧ k = i := by
          rcases step with ⟨empty, eq, _⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
          · exact ⟨empty, eq⟩
          · exact (act ⟨ρ, (levels₀ i ρ).mpr ⟨p, κ, F, hp, pay⟩⟩).elim
        obtain ⟨empty, eq⟩ := pad
        subst k
        obtain ⟨b₀, X, A, π, z, Z, α, here, _, hz, _⟩ := hist.at_l hZF hi
        obtain ⟨same, ident⟩ := hist.pads i j p succ hj hp empty
        obtain ⟨r, hr, cell⟩ := here
        have next : Ic_at_d H j X A π z Z α := ⟨r, (same r).mp hr, cell⟩
        obtain ⟨_, _, hz', _⟩ := hist.row_l hZF next
        obtain ⟨g, hg⟩ := hist.diagram.map_l hZF ((pred.2 i).mpr (Or.inr (original.diagram.order.refl i hi)))
        exact ⟨i, z, z, z, g, p, pred, hz, hz, hz', hg, (moves i p).mpr (Or.inl ⟨hp, empty⟩),
          Or.inl ⟨empty, rfl, rfl, fun x y hxy => ident g x y hg hxy⟩⟩
    · intro δ hδ limit
      obtain ⟨i, hi, succ⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hδ limit.2.1
      exact (it_successor_not_limit_l hZF.1 (hω.members_areOrdinals (ZF.modelsKP hZF) i hi) succ limit).elim
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
  · intro i q κ' ρ' F' hq pq
    obtain ⟨X, A, π, z, Z, α, p, κ, ρ, F, k, r, f, here, hp, pay, hκ, hρ, hF, pay'⟩ := ((moves i q).mp hq).active_l pq
    obtain ⟨e₁, e₂, e₃⟩ := pay'.unique_l pq
    subst k r f
    obtain ⟨b, hb, hz, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, map⟩ := row
    obtain ⟨κ₀, ρ₀, F₀, hκ₀, hρ₀, hF₀, good⟩ := quality here hp pay
    have eκ := map.1.1.1.2 κ κ₀ κ' hκ₀ hκ
    have eρ := map.1.1.1.2 ρ ρ₀ ρ' hρ₀ hρ
    have eF := map.1.1.1.2 F F₀ F' hF₀ hF
    subst κ₀ ρ₀ F₀
    obtain ⟨Rᵤ, _, trans, model, _, strength, card⟩ := good
    exact ⟨z, Z, Rᵤ, hz, model, trans, strength, card⟩
  · intro i j a b hi hj hij
    obtain ⟨p', κ', F', hp', pp'⟩ := (levels i a).mp hi
    obtain ⟨q', μ', G', hq', qq'⟩ := (levels j b).mp hj
    obtain ⟨X, A, π, z, Z, α, p, κ, ρ, F, _, a₀, _, ai, hp, pp, _, hρ, _, pp₀⟩ := ((moves i p').mp hp').active_l pp'
    obtain ⟨Y, B, σ, u, U, β, q, μ, ψ, F₀, _, b₀, _, aj, hq, qq, _, hψ, _, qq₀⟩ := ((moves j q').mp hq').active_l qq'
    have ea := (pp₀.unique_l pp').2.1
    have eb := (qq₀.unique_l qq').2.1
    subst a₀ b₀
    have hρL := (levels₀ i ρ).mpr ⟨p, κ, F, hp, pp⟩
    obtain ⟨r, succ, hr⟩ := hω.1.2 j (ef.input_mem_of_pairMember hq')
    exact hist.increasing i j r X A π z Z α Y B σ u U β ρ ψ a b ai aj succ hr hρL
      ((levels₀ j ψ).mpr ⟨q, μ, F₀, hq, qq⟩) hρ hψ hij

end YesMetaZFC.SetTheory.LargeCardinal
