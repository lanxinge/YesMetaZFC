import YesMetaZFC.SetTheory.LargeCardinal.IterationApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderExactStrength
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # nice 树的原始强度条件

操作列中的每个扩展器以支撑为最大强度，该支撑在所属模型中不可达，
并沿操作序严格递增。单根及实际超幂添枝直接构造这些条件的实例。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_payload_d.unique_l {p κ L F κ' L' F' : M.Domain}
    (h : It_payload_d p κ L F) (g : It_payload_d p κ' L' F') : κ = κ' ∧ L = L' ∧ F = F' := by
  obtain ⟨r, hp, hr⟩ := h
  obtain ⟨s, gp, gs⟩ := g
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp gp
  exact ⟨rfl, kpair_injective_l M hr gs⟩

/-- 支撑列只记录实际扩展器；恒等 padding 不添加虚假的支撑。 -/
structure It_pnice_d (ω c α T Q G E L : M.Domain) : Prop where
  tree : It_tree_d hZF ω c α T Q G E
  function : M.IsSetFunction I L
  levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F
  exactness : ∀ i p κ ρ F a X R, Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d i a Q →
    Smem_d I a X R → Ex_strength_d hZF ω κ ρ X F ∧ Sc_inaccessible_d ω X ρ
  increasing : ∀ i j ρ φ, Rd_entry_d i ρ L → Rd_entry_d j φ L → M.mem i j → M.mem ρ φ

/-- 无 padding 的子类用于逐项复制；共同强度条件全部继承自一般树。 -/
structure It_nice_d (ω c α T Q G E L : M.Domain) : Prop extends It_pnice_d hZF ω c α T Q G E L where
  active : ∀ i p, Rd_entry_d i p E → ∃ κ ρ F, It_payload_d p κ ρ F

/-- 有限树的末项支撑界住整列；最后一项允许等号。 -/
theorem It_pnice_d.last_bound_l {ω c β α ξ T Q G E H L : M.Domain}
    (h : It_pnice_d hZF ω c β T Q G E H) (hb : M.SuccessorOf β α) (ha : M.SuccessorOf α ξ)
    (last : Rd_entry_d ξ L H) : ∀ i μ, Rd_entry_d i μ H → M.mem μ L ∨ μ = L := by
  intro i μ hi
  obtain ⟨p, _, _, hp, _⟩ := (h.levels i μ).mp hi
  obtain ⟨j, hj, sj⟩ := (h.tree.move_domain i).mp ⟨p, hp⟩
  have oa := h.tree.diagram.order.ordinal.mem hb.predecessor_mem
  have hia : M.mem i α := ((hb j).mp hj).elim
    (fun hj => oa.transitive j hj i sj.predecessor_mem)
    (fun eq => (hZF.1.eq_of_same_members j α eq) ▸ sj.predecessor_mem)
  rcases (ha i).mp hia with lt | eq
  · exact Or.inl (h.increasing i ξ μ L hi last lt)
  · have eq := hZF.1.eq_of_same_members i ξ eq
    exact Or.inr (h.function.2 ξ μ L (eq ▸ hi) last)

/-- 原树步中的 padding 与非空扩展器码矛盾，故读取的是同一条实际超幂边。 -/
theorem It_nice_d.step_l {ω c₀ α T Q G E L i j : M.Domain}
    (h : It_nice_d hZF ω c₀ α T Q G E L) (hj : M.mem j α) (succ : M.SuccessorOf j i) :
    ∃ k c d b f p κ ρ F X R Y S,
      It_pred_d T k j ∧ Rd_entry_d i c Q ∧ Rd_entry_d k d Q ∧ Rd_entry_d j b Q ∧ It_map_d G k j f ∧
      Rd_entry_d i p E ∧ It_payload_d p κ ρ F ∧ Smem_d I c X R ∧ Smem_d I d Y S ∧
      It_local_d ω X κ ρ F ∧ Ea_agree_d ω κ X Y ∧ It_ultra_d hZF ω κ ρ F d b f ∧
      Ex_strength_d hZF ω κ ρ X F ∧ Sc_inaccessible_d ω X ρ ∧ Rd_entry_d i ρ L := by
  obtain ⟨k, c, d, b, f, p, pred, hc, hd, hb, hf, hp, step⟩ := h.tree.steps i j hj succ
  rcases step with ⟨empty, _⟩ | ⟨κ, ρ, F, X, R, Y, S, payload, mx, my, loc, agree, ultra⟩
  · obtain ⟨_, _, _, r, ⟨u, v, _, _, pair⟩, _⟩ := h.active i p hp
    exact (empty u ((pair u).mpr (Or.inl rfl))).elim
  · obtain ⟨strength, inaccessible⟩ := h.exactness i p κ ρ F c X R hp payload hc mx
    exact ⟨k, c, d, b, f, p, κ, ρ, F, X, R, Y, S, pred, hc, hd, hb, hf, hp, payload, mx, my,
      loc, agree, ultra, strength, inaccessible, (h.levels i ρ).mpr ⟨p, κ, F, hp, payload⟩⟩

theorem it_nice_root_l {ω c : M.Domain} (source : It_source_d hZF ω c) :
    ∃ z α T Q G, (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf α z ∧ It_nice_d hZF ω c α T Q G z z := by
  obtain ⟨z, α, T, Q, G, hz, hα, tree⟩ := it_root_l hZF source
  have no i p (h : Rd_entry_d i p z) : False := h.elim fun r hr => hz r hr.2
  exact ⟨z, α, T, Q, G, hz, hα, ⟨tree, tree.move_function,
    fun i ρ => ⟨fun h => (no i ρ h).elim, fun ⟨p, _, _, h, _⟩ => (no i p h).elim⟩,
    fun i p _ _ _ _ _ _ h => (no i p h).elim,
    fun i _ ρ _ h => (no i ρ h).elim⟩, fun i p h => (no i p h).elim⟩

/-- 同一个真实扩展器添枝，同时延长其最大强度列。 -/
theorem it_pnice_apply_l {ω c₀ α ξ T Q G E L k c d b j X R Y S κ ρ F : M.Domain}
    (h : It_pnice_d hZF ω c₀ α T Q G E L) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (loc : It_local_d ω X κ ρ F) (agree : Ea_agree_d ω κ X Y) (ultra : It_ultra_d hZF ω κ ρ F d b j)
    (source : It_source_d hZF ω b) (strength : Ex_strength_d hZF ω κ ρ X F)
    (inaccessible : Sc_inaccessible_d ω X ρ) (above : ∀ i φ, Rd_entry_d i φ L → M.mem φ ρ) :
    ∃ β U Q' G' E' L' p, It_pnice_d hZF ω c₀ β U Q' G' E' L' ∧
      It_extension_d α ξ k T Q G E β U Q' G' E' ∧ Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧
      It_payload_d p κ ρ F ∧ Rd_entry_d ξ p E' ∧ Rd_entry_d ξ ρ L' := by
  classical
  obtain ⟨β, U, Q', G', E', p, tree, extension, hb, hj, _, payload, hp⟩ :=
    it_apply_l hZF h.tree hα hc hd mx my loc agree ultra source
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have old i q (hq : Rd_entry_d i q E) : M.mem i ξ := by
    obtain ⟨m, hm, sm⟩ := (h.tree.move_domain i).mp ⟨q, hq⟩
    rcases (hα m).mp hm with hm | eq
    · exact (h.tree.diagram.order.ordinal.mem hα.predecessor_mem).transitive m hm i sm.predecessor_mem
    · exact (hZF.1.eq_of_same_members m ξ eq) ▸ sm.predecessor_mem
  have fresh q (hq : Rd_entry_d ξ q L) : False := by
    obtain ⟨p, _, _, hp, _⟩ := (h.levels ξ q).mp hq
    exact ir ξ (old ξ p hp)
  obtain ⟨L', lf, ls⟩ := it_move_push_l (ZF.modelsKP hZF) h.function fresh (p := ρ)
  have moves i q : Rd_entry_d i q E' ↔ Rd_entry_d i q E ∨ i = ξ ∧ q = p := by
    by_cases eq : i = ξ
    · subst i
      exact ⟨fun hq => Or.inr ⟨rfl, tree.move_function.2 ξ q p hq hp⟩,
        fun hq => hq.elim (extension.2.2.2.2.1 ξ q) (fun e => e.2.symm ▸ hp)⟩
    · exact (extension.2.2.2.2.2 i q eq).trans ⟨Or.inl, fun hh => hh.elim id (fun hh => (eq hh.1).elim)⟩
  have levels i φ : Rd_entry_d i φ L' ↔ ∃ q μ H, Rd_entry_d i q E' ∧ It_payload_d q μ φ H := by
    rw [ls]
    constructor
    · rintro (hi | ⟨rfl, rfl⟩)
      · obtain ⟨q, μ, H, hi, pay⟩ := (h.levels i φ).mp hi
        exact ⟨q, μ, H, (moves i q).mpr (Or.inl hi), pay⟩
      · exact ⟨p, κ, F, hp, payload⟩
    · rintro ⟨q, μ, H, hq, pay⟩
      rcases (moves i q).mp hq with hq | ⟨rfl, rfl⟩
      · exact Or.inl ((h.levels i φ).mpr ⟨q, μ, H, hq, pay⟩)
      · exact Or.inr ⟨rfl, (payload.unique_l pay).2.1.symm⟩
  refine ⟨β, U, Q', G', E', L', p, ⟨tree, lf, levels, ?_, ?_⟩,
    extension, hb, hj, payload, hp, (ls ξ ρ).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro i q μ φ H a N V hq pay ha mn
    rcases (moves i q).mp hq with hq | ⟨rfl, rfl⟩
    · have hi := h.tree.diagram.order.ordinal.transitive ξ hα.predecessor_mem i (old i q hq)
      obtain ⟨a₀, ha₀⟩ := (h.tree.diagram.model_domain i).mp hi
      have eq := tree.diagram.model_function.2 i a a₀ ha (extension.2.2.1 i a₀ ha₀)
      exact h.exactness i q μ φ H a N V hq pay (eq.symm ▸ ha₀) mn
    · obtain ⟨rfl, rfl, rfl⟩ := payload.unique_l pay
      have eq := tree.diagram.model_function.2 i a c ha (extension.2.2.1 i c hc)
      subst a
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mn.1 mx.1
      exact ⟨strength, inaccessible⟩
  · intro i m φ ψ hi hm him
    rcases (ls i φ).mp hi with hi | ⟨rfl, rfl⟩
    · rcases (ls m ψ).mp hm with hm | ⟨rfl, rfl⟩
      · exact h.increasing i m φ ψ hi hm him
      · exact above i φ hi
    · rcases (ls m ψ).mp hm with hm | ⟨rfl, rfl⟩
      · obtain ⟨q, _, _, hq, _⟩ := (h.levels m ψ).mp hm
        exact (ir _ ((h.tree.diagram.order.ordinal.mem hα.predecessor_mem).transitive m (old m q hq) _ him)).elim
      · exact (ir _ him).elim

/-- 恒等延长保存原模型与全部旧图，支撑列保持原值。 -/
theorem It_pnice_d.pad_l {ω c₀ α ξ T Q G E L : M.Domain}
    (h : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ) :
    ∃ β U Q' G' E' c j, It_pnice_d hZF ω c₀ β U Q' G' E' L ∧
      It_extension_d α ξ ξ T Q G E β U Q' G' E' ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d α c Q' ∧
      It_map_d G' ξ α j ∧ (∀ x y, Rd_entry_d x y j → x = y) ∧
      ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p := by
  classical
  obtain ⟨β, U, Q', G', E', c, j, _, tree, ext, hc, hc', edge, identity, keep, empty⟩ := it_pad_l hZF h.tree succ
  have old {i p κ ρ F} (hp : Rd_entry_d i p E') (pay : It_payload_d p κ ρ F) : Rd_entry_d i p E := by
    by_cases eq : i = ξ
    · subst i
      obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := pay
      exact (empty p hp u ((pair u).mpr (Or.inl rfl))).elim
    · exact (ext.2.2.2.2.2 i p eq).mp hp
  refine ⟨β, U, Q', G', E', c, j, ⟨tree, h.function, ?_, ?_, h.increasing⟩,
    ext, hc, hc', edge, identity, empty⟩
  · intro i ρ
    exact (h.levels i ρ).trans ⟨fun ⟨p, κ, F, hp, pay⟩ => ⟨p, κ, F, keep i p hp, pay⟩,
      fun ⟨p, κ, F, hp, pay⟩ => ⟨p, κ, F, old hp pay, pay⟩⟩
  · intro i p κ ρ F a X R hp pay ha mx
    have hp := old hp pay
    obtain ⟨n, hn, sn⟩ := (h.tree.move_domain i).mp ⟨p, hp⟩
    have hi := h.tree.diagram.order.ordinal.transitive n hn i sn.predecessor_mem
    obtain ⟨b, hb⟩ := (h.tree.diagram.model_domain i).mp hi
    have eq := tree.diagram.model_function.2 i a b ha (ext.2.2.1 i b hb)
    exact h.exactness i p κ ρ F a X R hp pay (eq.symm ▸ hb) mx

end YesMetaZFC.SetTheory.LargeCardinal
