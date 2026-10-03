import YesMetaZFC.SetTheory.Descriptive.Projective.CountableBase

/-! # 全部内部层号上的可数并交矩阵

同时归纳并、交两种矩阵；后继交换二者，故没有外部层号递归。
最后沿常行对角取连续逆像，得到作用于同一个自由实数的并交码。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Jc_d (b : Bool) (ω A B J n H c : M.Domain) : Prop := Bcode_d I ω A A c ∧
  ∀ C K, Bden_d I ω A A B c C → Pval_d I ω B J n C K → Aj_d I b ω A B J n H K
def jc_m (b : Bool) {d} (ω A B J n H c : Term d) : Formula 1 d := .conj (bcode_m (𝒞 := 𝒞) ω A A c)
  (.forallE (.forallE (.imp
    (bden_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken B.weaken.weaken c.weaken.weaken (.bound 1)) (.imp
    (pval_m (𝒞 := 𝒞) ω.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken (.bound 1) .newest)
    (aj_m (𝒞 := 𝒞) b ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken H.weaken.weaken .newest)))))
derive_free_closed jc_m
theorem jc_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H c : Term d) :
    Formula.satisfies ρ (jc_m (𝒞 := 𝒞) b ω A B J n H c) ↔
      Jc_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [jc_m, Jc_d, Formula.satisfies_conj_iff, bcode_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, bden_sat_l I hE, pval_sat_l I hE, aj_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem jc_pair_l (hZF : M.Models ZF) {ω A B J H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H) : ∀ n, M.mem n ω →
      ∃ c d, Jc_d I true ω A B J n H c ∧ Jc_d I false ω A B J n H d := by
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push H
  let φ : UnarySchema 5 := { body := .existsE (.existsE (.conj
    (jc_m (𝒞 := 𝒞) true (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1))
    (jc_m (𝒞 := 𝒞) false (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3) .newest))) }
  have hp n : φ.denote ρ n ↔ ∃ c d, Jc_d I true ω A B J n H c ∧ Jc_d I false ω A B J n H d := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, jc_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨T, fun n => (hT n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz
    have base b : ∃ c, Jc_d I b ω A B J z H c := by
      obtain ⟨c, hc, hv⟩ := array_base_l I hZF hB hA ha hJ hH hz b
      refine ⟨c, hc, fun C K hC hK => ?_⟩
      have e := (pval_zero_l I hZF hB.1 hz (fun x hx => ((hC x).mp hx).1)).mp hK
      subst K
      exact fun w => (hC w).trans (and_congr_right fun hw => hv w hw)
    obtain ⟨c, hc⟩ := base true
    obtain ⟨d, hd⟩ := base false
    exact ⟨c, d, hc, hd⟩
  · rintro n hn ⟨c, d, hc, hd⟩ m hm
    have next {b c} (hc : Jc_d I b ω A B J n H c) : Jc_d I (!b) ω A B J m H c := by
      refine ⟨hc.1, fun C K hC hK => ?_⟩
      obtain ⟨D, hd, hk⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hK
      exact aj_step_l I hZF hB hJ hcc hH hn hm (hc.2 C D hC hd) hk
    exact ⟨d, c, next hd, next hc⟩

/-- 输入实际内部 Borel 矩阵族，在任意内部 Σ 层构造同层并码或交码。 -/
theorem pm_countable_l (hZF : M.Models ZF) {ω A B J n H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hn : M.mem n ω) (hH : Bfam_d I ω A A H) (b : Bool) :
    ∃ d, Bcode_d I ω A A d ∧ ∀ x, Pm_d I ω A B J n d x ↔ M.mem x B ∧
      (if b then ∃ i c, M.PairMember I i c H ∧ Pm_d I ω A B J n c x
       else ∀ i c, M.PairMember I i c H → Pm_d I ω A B J n c x) := by
  obtain ⟨c, c', hc, hc'⟩ := jc_pair_l I hZF hB hA ha hJ hcc hH n hn
  have matrix : ∃ c, Jc_d I b ω A B J n H c := by cases b; exact ⟨c', hc'⟩; exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := matrix
  obtain ⟨f, hf, diag⟩ := array_diag_l I hZF hB hA hJ
  obtain ⟨X, L, hL⟩ := lgraph_exists_l I hZF hB hJ
  obtain ⟨E, he⟩ := ha
  obtain ⟨d, hd, hd'⟩ := ppull_exists_l I hZF hB hA he hL hf.1 hn hc.1
  obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨D, hD, _⟩ := bden_exists_unique_l I hZF ω A A B d
  obtain ⟨K, hK, _⟩ := pval_exists_unique_l I hZF (J := J) hB.1 hn (fun x hx => ((hC x).mp hx).1)
  obtain ⟨V, hV, _⟩ := pval_exists_unique_l I hZF (J := J) hB.1 hn (fun x hx => ((hD x).mp hx).1)
  have pull := ppull_value_l I hZF hB hA hJ he hL hf hn hc.1 hd hC hD hK hV
  have hj := hc.2 C K hC hK
  refine ⟨d, hd', fun x => (pm_mem_l I hZF hB.1 hD hV).symm.trans ((pull x).trans (and_congr_right fun hx => ?_))⟩
  obtain ⟨w, hw, hxw⟩ := hf.1.2.2 x hx
  have mem : (∃ y, M.PairMember I x y f ∧ M.mem y K) ↔ Aw_d I b ω A B J n H w := by
    refine ⟨fun ⟨y, hy, hk⟩ => ((hj w).mp (hf.1.1.2 x y w hy hxw ▸ hk)).2,
      fun h => ⟨w, hxw, (hj w).mpr ⟨hw, h⟩⟩⟩
  refine mem.trans ?_
  cases b
  · exact ⟨fun h i c hic => h i c x hic (diag x w hxw i (hH.2 i c hic).1),
      fun h i c y hic hr => (row_unique_l I hZF.1 (diag x w hxw i (hH.2 i c hic).1) hr) ▸ h i c hic⟩
  · exact ⟨fun ⟨i, c, y, hic, hr, hy⟩ => ⟨i, c, hic,
      row_unique_l I hZF.1 hr (diag x w hxw i (hH.2 i c hic).1) ▸ hy⟩,
      fun ⟨i, c, hic, hx⟩ => ⟨i, c, x, hic, diag x w hxw i (hH.2 i c hic).1, hx⟩⟩

end YesMetaZFC.SetTheory.Descriptive
