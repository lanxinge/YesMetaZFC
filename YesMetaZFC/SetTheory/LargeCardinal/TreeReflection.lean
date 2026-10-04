import YesMetaZFC.SetTheory.LargeCardinal.Measurable

/-! # 强嵌入下的共同分支回拉

对局及有限前缀均为内部函数图。存在贯穿每个内部长度的分支是一个实际 Σ₁ 断言；
目标侧分支属于嵌入载体时，全内部初等性将其回拉到原秩层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Eb_d (ω D T f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ s, M.mem s T ∧ Fn0_d n D s ∧ M.MemberSubset s f

def eb_m {d} (ω D T f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (Formula.existsMem T.weaken (.conj (fn0_m (.bound 1) D.weaken.weaken .newest)
    (Formula.subset .newest f.weaken.weaken))))
derive_free_closed eb_m

theorem eb_delta_l {d} (ω D T f : Term d) : (eb_m ω D T f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.atom _ _ _))))

theorem eb_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D T f : Term d) :
    Formula.satisfies ρ (eb_m ω D T f) ↔ Eb_d (ω.eval ρ) (D.eval ρ) (T.eval ρ) (f.eval ρ) := by
  simp only [eb_m, Eb_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem eb_mono_l {ω D E T f} (hDE : M.MemberSubset D E) (h : Eb_d ω D T f) : Eb_d ω E T f :=
  ⟨h.1.mono_target_l hDE, fun n hn => (h.2 n hn).imp fun _ hs => ⟨hs.1, hs.2.1.mono_target_l hDE, hs.2.2⟩⟩

theorem ed_branch_pull_l (hZF : M.Models ZF) {ω X A Y B j D D' T T' f}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hjω : M.PairMember I ω ω j) (hjD : M.PairMember I D D' j) (hjT : M.PairMember I T T' j)
    (hfY : M.mem f Y) (hf : Eb_d ω D' T' f) : ∃ g, M.mem g X ∧ Eb_d ω D T g := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  have h : Spred_emb_d I ω X A Y B j := ⟨c, R, d, S, hx, hy, hj⟩
  let hn : Nonempty {x // M.mem x X} := hx.1.2.1.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  let hm : Nonempty {x // M.mem x Y} := hy.1.2.1.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  let ρ : Env (rt_model_l X hn) 3 := ⟨Fin.cases ⟨T, hj.1.1.input_mem_of_pairMember hjT⟩
    (Fin.cases ⟨D, hj.1.1.input_mem_of_pairMember hjD⟩ (fun _ => ⟨ω, hj.1.1.input_mem_of_pairMember hjω⟩)),
    fun _ => ⟨ω, hj.1.1.input_mem_of_pairMember hjω⟩⟩
  let η : Env (rt_model_l Y hm) 3 := ⟨Fin.cases ⟨T', hj.1.1.output_mem_of_pairMember hjT⟩
    (Fin.cases ⟨D', hj.1.1.output_mem_of_pairMember hjD⟩ (fun _ => ⟨ω, hj.1.1.output_mem_of_pairMember hjω⟩)),
    fun _ => ⟨ω, hj.1.1.output_mem_of_pairMember hjω⟩⟩
  let φ : Formula 1 4 := eb_m (.bound 3) (.bound 2) (.bound 1) .newest
  have hd : φ.IsDelta0 := eb_delta_l ..
  have hc : φ.FreeClosed := eb_m_freeClosed _ _ _ _ rfl rfl rfl rfl
  have tr := spred_source_l I hZF hω h hn hm (.existsE φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc) ρ η (Fin.cases hjT (Fin.cases hjD (fun _ => hjω)))
  have ht : Formula.satisfies (η.push ⟨f, hfY⟩) φ :=
    (rt_model_delta_l hY hm hd _).mpr ((eb_sat_l hZF.1 _ _ _ _ _).mpr hf)
  obtain ⟨g, hg⟩ := (Formula.satisfies_exists_iff ρ φ).mp (tr.mpr ((Formula.satisfies_exists_iff η φ).mpr ⟨⟨f, hfY⟩, ht⟩))
  exact ⟨g.val, g.property, (eb_sat_l hZF.1 _ _ _ _ _).mp ((rt_model_delta_l hX hn hd _).mp hg)⟩

/-- 先界定需要覆盖的实际集合，再选择足够强的嵌入。 -/
theorem wd_cover_embedding_l (hZF : M.Models ZF) {ω δ X A κ L G}
    (hV : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hk : Wd_strong_d I ω δ X A κ) (hL : M.mem L δ) (hGX : M.mem G X) :
    ∃ ν N B j W k, Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L k ∧ M.mem G N := by
  obtain ⟨γ, V, hγ, hVγ, hGV⟩ := (ZF.v_limit_mem_l I hZF hV hδ.2.2 G).mp hGX
  obtain ⟨η, hη, hLη⟩ := hδ.2.2 L hL
  have bound : ∃ ν, M.mem ν δ ∧ M.mem L ν ∧ M.MemberSubset γ ν := by
    rcases hδ.1.wellOrder.linear.compare γ hγ η hη with he | he | he
    · exact ⟨η, hη, hLη, fun x hx => (he x).mp hx⟩
    · exact ⟨η, hη, hLη, (hδ.1.mem hη).transitive γ he⟩
    · exact ⟨γ, hγ, (hδ.1.mem hγ).transitive η he L hLη, fun _ hx => hx⟩
  obtain ⟨ν, hν, hLν, hγν⟩ := bound
  obtain ⟨N, B, j, W, k, hw⟩ := hk ν hν
  obtain ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩ := hw
  have hGN := hWN G (ZF.v_mono_l I hZF hVγ hW hγν G hGV)
  have hLk := hc.ordinal_image.transitive ν hνk L hLν
  exact ⟨ν, N, B, j, W, k, ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩, hLk, hGN⟩

end YesMetaZFC.SetTheory.LargeCardinal
