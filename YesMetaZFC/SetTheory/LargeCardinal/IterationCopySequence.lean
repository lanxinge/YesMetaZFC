import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyExtend
import YesMetaZFC.Model.SetTheory.ClassChoice

/-! # 全部内部有限复制历史的实际 ω 序列

初值为给定嵌入。类依赖选择只使用已证明的总延伸步，自动收集全部有限
历史；不假定外部 ω 标准，也不预设容纳完整复制树的统一秩界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_row_d.start_l {ω c X A π z Z α o T Q G E L : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (tree : It_diagram_d hZF ω ω T Q G)
    (ho : ∀ x, ¬ M.mem x o) (hc : Rd_entry_d o c Q) :
    ∃ m H S Q' G', M.SuccessorOf m o ∧ Ic_history_d hZF ω T Q G E L m H S Q' G' ∧ Ic_at_d H o X A π z Z α := by
  have data := row
  obtain ⟨_, _, V, _, _, _, K, _, _, hz, _, _, full, hA, _⟩ := data
  obtain ⟨o₀, m, S, Q', G', ho₀, hm, root⟩ := it_root_l hZF ⟨Z, V, K, hz, full.source⟩
  have eq := hZF.1.eq_of_same_members o₀ o (fun x => iff_of_false (ho₀ x) (ho x))
  subst o₀
  have one i (hi : M.mem i m) : i = o := ((hm i).mp hi).elim (fun h => (ho i h).elim) (hZF.1.eq_of_same_members i o)
  obtain ⟨r, cell⟩ := ic_cell_exists_l (ZF.modelsKP hZF) X A π z Z α
  obtain ⟨C, cs⟩ := KP.exists_singleton (ZF.modelsKP hZF) r
  obtain ⟨H, hf, hs⟩ := ZF.exists_constantFunction hZF I (source := m) ((cs r).mpr rfl)
  have top : Ic_at_d H o X A π z Z α := ⟨r, (hs o r).mpr ⟨hm.predecessor_mem, rfl⟩, cell⟩
  have index {i Y B σ u U β} (hi : Ic_at_d H i Y B σ u U β) : i = o := by
    obtain ⟨t, ht, _⟩ := hi
    exact one i (hf.input_mem_of_pairMember ht)
  have order i j : Rd_entry_d i j S ↔ Rd_entry_d i j T ∧ M.mem j m := by
    constructor
    · intro hij
      obtain ⟨hi, hj⟩ := root.diagram.order.bound i j hij
      have ei := one i hi
      have ej := one j hj
      subst i j
      exact ⟨tree.order.refl o ((tree.model_domain o).mpr ⟨c, hc⟩), hm.predecessor_mem⟩
    · rintro ⟨hij, hj⟩
      have ej := one j hj
      subst j
      have ei := (tree.order.forward i o hij).elim id (fun hi => (ho i hi).elim)
      subst i
      exact root.diagram.order.refl o hm.predecessor_mem
  refine ⟨m, H, S, Q', G', hm, ⟨root.diagram, order, hf.1, hf.2.1, ?_, ?_, ?_, ?_, ?_⟩, top⟩
  · intro i t ht
    obtain ⟨hi, et⟩ := (hs i t).mp ht
    have ei := one i hi
    subst i t
    exact ⟨c, X, A, π, z, Z, α, cell, hc, root.root o ho, row⟩
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ai aj hij
    exact (ho i (index aj ▸ hij)).elim
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ai aj hg
    have ei := index ai
    have ej := index aj
    subst i j
    rw [(ai.unique_l (ZF.modelsKP hZF) hf.1 top).2.1, (aj.unique_l (ZF.modelsKP hZF) hf.1 top).2.1]
    have e := root.diagram.elementary o o g z Z V z Z V hg (root.root o ho) (root.root o ho) hz.1 hz.1
    obtain ⟨B, _, hab⟩ := e.1.1.2.2 A hA
    exact (root.diagram.identity o g hg A B hab).symm ▸ hab
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g ai aj hfi hgi x x' y y' hxx hxy hyy
    have ei := index ai
    have ej := index aj
    subst i j
    have eq := ai.unique_l (ZF.modelsKP hZF) hf.1 aj
    exact tree.identity o f hfi x y hxy ▸ root.diagram.identity o g hgi x' y' hyy ▸ eq.2.2.1 ▸ hxx
  · intro i j k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ succ _ _ _ aj
    exact (ho i (index aj ▸ succ.predecessor_mem)).elim

def Ic_pack_d (s H S Q G : M.Domain) : Prop := ∃ p, KPair_d M p Q G ∧ Rd_triple_d s H S p
def ic_pack_m {d} (s H S Q G : Term d) : Formula 1 d := set[d] ⟪
  ∃ p, ⌜kpair0_m⌝ₚ(p, ⌜Q⌝ₛ, ⌜G⌝ₛ) ∧ ⌜rd_triple0_m⌝ₚ(⌜s⌝ₛ, ⌜H⌝ₛ, ⌜S⌝ₛ, p)⟫
derive_free_closed ic_pack_m
theorem ic_pack_sat_l (hE : Extensional M) {d} (η : Env M d) (s H S Q G : Term d) :
    Formula.satisfies η (ic_pack_m s H S Q G) ↔ Ic_pack_d (s.eval η) (H.eval η) (S.eval η) (Q.eval η) (G.eval η) := by
  simp only [ic_pack_m, Ic_pack_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]; rfl
theorem ic_pack_exists_l (hKP : M.Models KP) (H S Q G : M.Domain) : ∃ s, Ic_pack_d s H S Q G := by
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total Q G
  obtain ⟨q, hq⟩ := (kp_pair_l hKP).total S p
  obtain ⟨s, hs⟩ := (kp_pair_l hKP).total H q
  exact ⟨s, p, hp, q, hq, hs⟩
theorem Ic_pack_d.unique_l {s H S Q G H' S' Q' G' : M.Domain}
    (h : Ic_pack_d s H S Q G) (g : Ic_pack_d s H' S' Q' G') : H = H' ∧ S = S' ∧ Q = Q' ∧ G = G' := by
  obtain ⟨p, hp, hs⟩ := h
  obtain ⟨q, hq, ht⟩ := g
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hs ht
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hq
  exact ⟨rfl, rfl, rfl, rfl⟩

def Ic_state_d (ω T Q G E L i s : M.Domain) : Prop := ∃ m H S Q' G',
  M.SuccessorOf m i ∧ Ic_pack_d s H S Q' G' ∧ Ic_history_d hZF ω T Q G E L m H S Q' G'
def ic_state_m {d} (ω T Q G E L i s : Term d) : Formula 1 d := set[d] ⟪
  ∃ m H S Q' G', ⌜KP.succ0_m⌝ₚ(m, ⌜i⌝ₛ) ∧ ⌜ic_pack_m⌝ₚ(⌜s⌝ₛ, H, S, Q', G') ∧
    ⌜ic_history_m⌝ₚ(⌜ω⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ, ⌜L⌝ₛ, m, H, S, Q', G')⟫
derive_free_closed ic_state_m
theorem ic_state_sat_l {d} (η : Env M d) (ω T Q G E L i s : Term d) :
    Formula.satisfies η (ic_state_m ω T Q G E L i s) ↔ Ic_state_d hZF
      (ω.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) (i.eval η) (s.eval η) := by
  simp only [ic_state_m, Ic_state_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hZF.1, ic_pack_sat_l hZF.1, ic_history_sat_l hZF, Definitional.Term.eval_weaken]; rfl

def Ic_extend_d (s t : M.Domain) : Prop := ∃ H S Q G H' S' Q' G', Ic_pack_d s H S Q G ∧ Ic_pack_d t H' S' Q' G' ∧
  M.MemberSubset H H' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G'
def ic_extend_m {d} (s t : Term d) : Formula 1 d := set[d] ⟪
  ∃ H S Q G H' S' Q' G', ⌜ic_pack_m⌝ₚ(⌜s⌝ₛ, H, S, Q, G) ∧ ⌜ic_pack_m⌝ₚ(⌜t⌝ₛ, H', S', Q', G') ∧
    H ⊆ H' ∧ Q ⊆ Q' ∧ G ⊆ G'⟫
derive_free_closed ic_extend_m
theorem ic_extend_sat_l (hE : Extensional M) {d} (η : Env M d) (s t : Term d) :
    Formula.satisfies η (ic_extend_m s t) ↔ Ic_extend_d (s.eval η) (t.eval η) := by
  simp only [ic_extend_m, Ic_extend_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, ic_pack_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ic_extend_d.read_l {s t H S Q G H' S' Q' G' : M.Domain} (h : Ic_extend_d s t)
    (hs : Ic_pack_d s H S Q G) (ht : Ic_pack_d t H' S' Q' G') :
    M.MemberSubset H H' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G' := by
  obtain ⟨A, B, C, D, A', B', C', D', hp, hq, keep⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.unique_l hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hq.unique_l ht
  exact keep

theorem Ic_extend_d.trans_l {s t u : M.Domain} (h : Ic_extend_d s t) (g : Ic_extend_d t u) : Ic_extend_d s u := by
  obtain ⟨H, S, Q, G, H', S', Q', G', hs, ht, hh, hq, hg⟩ := h
  have g₀ := g
  obtain ⟨A, B, C, D, H'', S'', Q'', G'', hp, hu, _⟩ := g
  obtain ⟨hh', hq', hg'⟩ := g₀.read_l ht hu
  exact ⟨H, S, Q, G, H'', S'', Q'', G'', hs, hu,
    fun x hx => hh' x (hh x hx), fun x hx => hq' x (hq x hx), fun x hx => hg' x (hg x hx)⟩
end

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 类选择的转移见证由实际复制定理提供；所得序列从指定首行出发。 -/
theorem Ic_row_d.sequence_l {ω c X A π z Z α o T Q G E L : M.Domain}
    (nice : It_nice_d hZF ω c ω T Q G E L) (row : Ic_row_d hZF ω c X A π z Z α) (ho : ∀ x, ¬ M.mem x o) :
    ∃ D f s₀ H₀ S₀ Q₀ G₀, Fn0_d ω D f ∧ Rd_entry_d o s₀ f ∧ Ic_pack_d s₀ H₀ S₀ Q₀ G₀ ∧
      Ic_at_d H₀ o X A π z Z α ∧ (∀ i s, Rd_entry_d i s f → Ic_state_d hZF ω T Q G E L i s) ∧
      ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Ic_extend_d s t := by
  obtain ⟨m, H, S, Q', G', hm, hist, first⟩ := row.start_l hZF nice.tree.diagram ho (nice.tree.root o ho)
  obtain ⟨s₀, pack⟩ := ic_pack_exists_l (ZF.modelsKP hZF) H S Q' G'
  let η : Env M 6 := ⟨Fin.cases L (Fin.cases E (Fin.cases G (Fin.cases Q (Fin.cases T (fun _ => ω))))), fun _ => ω⟩
  let V : BinarySchema 6 := { body := ic_state_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let φ : UnarySchema 8 := { body := ic_extend_m (.bound 1) .newest }
  have valid i s : V.denote η i s ↔ Ic_state_d hZF ω T Q G E L i s := ic_state_sat_l hZF ..
  have step i s t : φ.denote ((η.push i).push s) t ↔ Ic_extend_d s t := ic_extend_sat_l hZF.1 ..
  obtain ⟨D, f, hf, hs, all, next⟩ := ZFC.class_indexed_choice_l I hZFC V φ η nice.tree.omega ho
    ((valid o s₀).mpr ⟨m, H, S, Q', G', hm, pack, hist⟩) (by
      intro i j s hi hij hv
      obtain ⟨m, H, S, Q', G', hm, pack, hist⟩ := (valid i s).mp hv
      have eq := hm.eq hZF.1 hij
      subst m
      obtain ⟨l, J, S', Q'', G'', hl, hist', rows, codes, maps⟩ := hist.extend_l hZFC nice hi hij
      obtain ⟨t, pack'⟩ := ic_pack_exists_l (ZF.modelsKP hZF) J S' Q'' G''
      exact ⟨t, (valid j t).mpr ⟨l, J, S', Q'', G'', hl, pack', hist'⟩,
        (step i s t).mpr ⟨H, S, Q', G', J, S', Q'', G'', pack, pack', rows, codes, maps⟩⟩)
  exact ⟨D, f, s₀, H, S, Q', G', fn0_of_function_l (ZF.modelsKP hZF) hf, hs, pack, first,
    fun i s hs => (valid i s).mp (all i s hs), fun i j s t hij hs ht => (step i s t).mp (next i j s t hij hs ht)⟩

end YesMetaZFC.SetTheory.LargeCardinal
