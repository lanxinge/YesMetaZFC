import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSaved

/-! # 统一历史中的全部旧回答

历史是背景模型自己的序数长度函数图。每行记录原树结点、完整工作源、原
反射层、共同高度及完整回答证书；改变当前模型时，原行逐字保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_past_cell_d (r i Y R μ K η C L V q : M.Domain) : Prop :=
  Rt_tuple_d (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j) r

def tg_past_cell_m {d} (r i Y R μ K η C L V q : Term d) : Formula 1 d :=
  rt_tuple_m (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j) r

@[simp] theorem tg_past_cell_closed_l {d} (r i Y R μ K η C L V q : Term d)
    (hr : r.freeSupport = []) (hi : i.freeSupport = []) (hY : Y.freeSupport = []) (hR : R.freeSupport = [])
    (hμ : μ.freeSupport = []) (hK : K.freeSupport = []) (hη : η.freeSupport = [])
    (hC : C.freeSupport = []) (hL : L.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_past_cell_m r i Y R μ K η C L V q).FreeClosed := by
  apply rt_tuple_closed_l _ _ ?_ hr
  intro j
  exact Fin.cases hi (Fin.cases hY (Fin.cases hR (Fin.cases hμ (Fin.cases hK
    (Fin.cases hη (Fin.cases hC (Fin.cases hL (Fin.cases hV (Fin.cases hq (fun k => Fin.elim0 k)))))))))) j

theorem tg_past_cell_sat_l (hE : Extensional M) {d} (ρ : Env M d) (r i Y R μ K η C L V q : Term d) :
    Formula.satisfies ρ (tg_past_cell_m r i Y R μ K η C L V q) ↔
      Tg_past_cell_d (r.eval ρ) (i.eval ρ) (Y.eval ρ) (R.eval ρ) (μ.eval ρ) (K.eval ρ)
        (η.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  rw [tg_past_cell_m, rt_tuple_sat_l hE]
  have eq : (fun j : Fin 10 => ([i, Y, R, μ, K, η, C, L, V, q].get j).eval ρ) =
      (fun j => [i.eval ρ, Y.eval ρ, R.eval ρ, μ.eval ρ, K.eval ρ, η.eval ρ, C.eval ρ, L.eval ρ, V.eval ρ, q.eval ρ].get j) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) j
  exact eq ▸ Iff.rfl

def Tg_past_at_d (H n i Y R μ K η C L V q : M.Domain) : Prop :=
  ∃ r, Rd_entry_d n r H ∧ Tg_past_cell_d r i Y R μ K η C L V q

def tg_past_at_m {d} (H n i Y R μ K η C L V q : Term d) : Formula 1 d := set[d] ⟪
  ∃ r, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, r, ⌜H⌝ₛ) ∧
    ⌜tg_past_cell_m⌝ₚ(r, ⌜i⌝ₛ, ⌜Y⌝ₛ, ⌜R⌝ₛ, ⌜μ⌝ₛ, ⌜K⌝ₛ, ⌜η⌝ₛ, ⌜C⌝ₛ, ⌜L⌝ₛ, ⌜V⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed tg_past_at_m

theorem tg_past_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H n i Y R μ K η C L V q : Term d) :
    Formula.satisfies ρ (tg_past_at_m H n i Y R μ K η C L V q) ↔
      Tg_past_at_d (H.eval ρ) (n.eval ρ) (i.eval ρ) (Y.eval ρ) (R.eval ρ) (μ.eval ρ)
        (K.eval ρ) (η.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [tg_past_at_m, Tg_past_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, tg_past_cell_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_past_links_d (I : kpair_convention_l.Interpretation M) (H Q : M.Domain) : Prop :=
  ∀ m i Y R μ K η C L V q, Tg_past_at_d H m i Y R μ K η C L V q → ∃ c, Rd_entry_d i c Q ∧ Smem_d I c Y R

def tg_past_links_m {d} (H Q : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η C L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
    ∃ c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R)⟫
derive_free_closed tg_past_links_m

theorem tg_past_links_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (H Q : Term d) : Formula.satisfies ρ (tg_past_links_m H Q) ↔
      Tg_past_links_d I (H.eval ρ) (Q.eval ρ) := by
  simp only [tg_past_links_m, Tg_past_links_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l hE,
    rd_entry0_sat_l hE, smem_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem tg_past_links_empty_l (I : kpair_convention_l.Interpretation M) {e Q : M.Domain}
    (he : ∀ x, ¬ M.mem x e) : Tg_past_links_d I e Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (he p hp).elim

def Tg_past_fixed_d (H j : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  Tg_past_at_d H m i Y R μ K η C L V q → ∀ x, M.mem x V → Rd_entry_d x x j

structure Tg_past_d (hZF : M.Models ZF) (ω n H X b : M.Domain) : Prop where
  sequence : M.IsSequenceOfLength (kp_pair_l (ZF.modelsKP hZF)) H n
  rows : ∀ m r, Rd_entry_d m r H → ∃ i Y R μ K η C L V q,
    Tg_past_cell_d r i Y R μ K η C L V q ∧ Tg_saved_d hZF ω Y R μ K η C L V q ∧
    M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b

def tg_past_m {d} (ω n H X b : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜n⌝ₛ) ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜H⌝ₛ) ∧
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜n⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ m r, ⌜rd_entry0_m⌝ₚ(m, r, ⌜H⌝ₛ) → ∃ i Y R μ K η C L V q,
    ⌜tg_past_cell_m⌝ₚ(r, i, Y, R, μ, K, η, C, L, V, q) ∧
    ⌜tg_saved_m⌝ₚ(⌜ω⌝ₛ, Y, R, μ, K, η, C, L, V, q) ∧
    V ∈ ⌜X⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, L, V) ∧ L ⊆ ⌜b⌝ₛ)⟫
derive_free_closed tg_past_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_past_sat_l {d} (ρ : Env M d) (ω n H X b : Term d) :
    Formula.satisfies ρ (tg_past_m ω n H X b) ↔
      Tg_past_d hZF (ω.eval ρ) (n.eval ρ) (H.eval ρ) (X.eval ρ) (b.eval ρ) := by
  simp only [tg_past_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    rd_entry0_sat_l hZF.1, tg_past_cell_sat_l hZF.1, tg_saved_sat_l hZF,
    Formula.satisfies_mem_iff, pn_rank_sat_l (ZF.modelsKP hZF), Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩,
    fun h => ⟨h.sequence.1, h.sequence.2.1, h.sequence.2.2, h.rows⟩⟩

theorem tg_past_empty_l {ω e X b : M.Domain} (he : ∀ x, ¬ M.mem x e) : Tg_past_d hZF ω e e X b := by
  have fn : Fn0_d e e e := ⟨fun p hp => (he p hp).elim, fun p hp => (he p hp).elim, fun p hp => (he p hp).elim⟩
  have graph := fn0_function_l (ZF.modelsKP hZF) fn
  exact ⟨⟨Structure.IsOrdinal.of_no_members he, graph.1, graph.2.1⟩,
    fun _ _ ⟨p, _, hp⟩ => (he p hp).elim⟩

/-- 指定轮号直接读回同一原模型、原证书与当前共同秩段。 -/
theorem Tg_past_d.read_l {ω n H X b m i Y R μ K η C L V q : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (ha : Tg_past_at_d H m i Y R μ K η C L V q) :
    Tg_saved_d hZF ω Y R μ K η C L V q ∧ M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b := by
  obtain ⟨r, hr, cell⟩ := ha
  obtain ⟨i', Y', R', μ', K', η', C', L', V', q', cell', saved, member, rank, bound⟩ := h.rows m r hr
  have eq := rt_tuple_inj_l cell' cell
  have eY : Y' = Y := congrFun eq 1; have eR : R' = R := congrFun eq 2
  have eμ : μ' = μ := congrFun eq 3; have eK : K' = K := congrFun eq 4; have eη : η' = η := congrFun eq 5
  have eC : C' = C := congrFun eq 6; have eL : L' = L := congrFun eq 7
  have eV : V' = V := congrFun eq 8; have eq' : q' = q := congrFun eq 9
  exact eY ▸ eR ▸ eμ ▸ eK ▸ eη ▸ eC ▸ eL ▸ eV ▸ eq' ▸ ⟨saved, member, rank, bound⟩

/-- 增加一行时，全部旧记录保持原值，且仍能按原轮号访问。 -/
theorem Tg_past_d.push_l {ω n H X b n' b' i Y R μ K η C L V q : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (succ : M.SuccessorOf n' n)
    (saved : Tg_saved_d hZF ω Y R μ K η C L V q) (member : M.mem V X) (rank : Vr_d X L V)
    (oldBound : M.MemberSubset b b') (bound : M.MemberSubset L b') :
    ∃ H', Tg_past_d hZF ω n' H' X b' ∧ Tg_past_at_d H' n i Y R μ K η C L V q ∧
      ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H) := by
  obtain ⟨r, cell⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j)
  obtain ⟨H', seq, entries⟩ := Structure.IsSequenceOfLength.exists_append (value := r) (ZF.modelsKP hZF) I
    h.sequence (KP.successor_isOrdinal (ZF.modelsKP hZF) h.sequence.1 succ) succ
  refine ⟨H', ⟨seq, ?_⟩, ⟨r, (entries n r).mpr (Or.inr ⟨rfl, rfl⟩), cell⟩, ?_⟩
  · intro m s hs
    rcases (entries m s).mp hs with hs | ⟨_, rfl⟩
    · obtain ⟨i, Y, R, μ, K, η, C, L, V, q, cell, saved, member, rank, bound⟩ := h.rows m s hs
      exact ⟨i, Y, R, μ, K, η, C, L, V, q, cell, saved, member, rank, fun x hx => oldBound x (bound x hx)⟩
    · exact ⟨i, Y, R, μ, K, η, C, L, V, q, cell, saved, member, rank, bound⟩
  · intro m s hm
    exact (entries m s).trans ⟨fun hs => hs.elim id (fun hs => (KP.mem_irrefl_d (ZF.modelsKP hZF) n (hs.1 ▸ hm)).elim), Or.inl⟩

/-- 树的两条后继边保留旧模型列，追加行因而仍指向它的实际产生结点。 -/
theorem Tg_past_d.links_push_l {ω n H n' H' N b' Q Q' i Y R μ K η C L V q c : M.Domain}
    (updated : Tg_past_d hZF ω n' H' N b') (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (links : Tg_past_links_d I H Q) (keep : ∀ m d, Rd_entry_d m d Q → Rd_entry_d m d Q')
    (node : Rd_entry_d i c Q') (model : Smem_d I c Y R) : Tg_past_links_d I H' Q' := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ hm
  obtain ⟨r, hr, cell⟩ := hm
  have domain := (updated.sequence.2.2 m).mpr ⟨r, hr⟩
  rcases (succ m).mp domain with lt | eq
  · obtain ⟨d, hd, md⟩ := links m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
    exact ⟨d, keep i₀ d hd, md⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, cell'⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have tuple := rt_tuple_inj_l cell cell'
    have ei : i₀ = i := congrFun tuple 0
    have eY : Y₀ = Y := congrFun tuple 1
    have eR : R₀ = R := congrFun tuple 2
    subst i₀ Y₀ R₀
    exact ⟨c, node, model⟩

/-- 按内部轮号选取旧源；其树结点、完整记录和当前共同层一次返回。 -/
theorem Tg_past_d.select_l {ω n H X b Q m : M.Domain} (h : Tg_past_d hZF ω n H X b)
    (links : Tg_past_links_d I H Q) (hm : M.mem m n) :
    ∃ i Y R μ K η C L V q c, Tg_past_at_d H m i Y R μ K η C L V q ∧ Rd_entry_d i c Q ∧ Smem_d I c Y R ∧
      Tg_saved_d hZF ω Y R μ K η C L V q ∧ M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b := by
  obtain ⟨r, hr⟩ := (h.sequence.2.2 m).mp hm
  obtain ⟨i, Y, R, μ, K, η, C, L, V, q, cell, saved, member, rank, bound⟩ := h.rows m r hr
  have ha : Tg_past_at_d H m i Y R μ K η C L V q := ⟨r, hr, cell⟩
  obtain ⟨c, node, model⟩ := links m i Y R μ K η C L V q ha
  exact ⟨i, Y, R, μ, K, η, C, L, V, q, c, ha, node, model, saved, member, rank, bound⟩

/-- 一个共同支撑层同时保存整段历史，无须逐轮重新构造旧回答。 -/
theorem Tg_past_d.transfer_l {ω n H X b N L W : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (xt : M.TransitiveSet X) (nt : M.TransitiveSet N)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W N) (next : Vr_d N L W)
    (limit : M.IsLimitOrdinal L) (below : M.mem b L) :
    Tg_past_d hZF ω n H N b := by
  refine ⟨h.sequence, ?_⟩
  intro m r hr
  obtain ⟨i, Y, R, μ, K, η, C, ζ, V, q, cell, saved, hV, old, sub⟩ := h.rows m r hr
  have hζ := ordinal_down_l (ZF.modelsKP hZF) saved.limit.1 limit.1 sub below
  obtain ⟨hVW, inner⟩ := rank.rank_l hZF xt hW limit (rank.ordinal_subset_l hZF xt hW ζ hζ) hV old
  exact ⟨i, Y, R, μ, K, η, C, ζ, V, q, cell, saved, nt W hW' V hVW,
    next.of_rank_l hZF nt hW' hVW inner, sub⟩

/-- 临界点高于历史界的偶数边逐点固定全部旧回答所在层。 -/
theorem Tg_past_d.fixed_l {ω n H X b κ W j : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (xt : M.TransitiveSet X) (hW : M.mem W X) (rank : Vr_d X κ W)
    (below : M.MemberSubset b κ) (fixed : ∀ x, M.mem x W → Rd_entry_d x x j) : Tg_past_fixed_d H j := by
  intro m i Y R μ K η C L V q ha
  obtain ⟨_, hV, old, bound⟩ := h.read_l hZF ha
  have sub := (rank.compare_l hZF xt hW hV old (fun x hx => below x (bound x hx))).1
  exact fun x hx => fixed x (sub x hx)

end YesMetaZFC.SetTheory.LargeCardinal
