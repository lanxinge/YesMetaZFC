import YesMetaZFC.SetTheory.Descriptive.Projective.Operations

/-! # 射影码量词的集合语义

Π¹ₙ 上加存在量词得到 Σ¹ₙ₊₁，Σ¹ₙ 上加全称量词得到 Π¹ₙ₊₁。
全称量词也直接给出逐实数判据；自由变量和见证均量化于内部 Baire 空间。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def All_d (B J R K : M.Domain) : Prop := ∀ x, M.mem x K ↔ M.mem x B ∧
  ∀ y z, M.mem y B → M.mem z B → Rp_d I J x y z → M.mem z R
def all_m {d} (B J R K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (.forallE (.forallE
    (.imp (.mem (.bound 1) B.weaken.weaken.weaken) (.imp (.mem .newest B.weaken.weaken.weaken)
      (.imp (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.mem .newest R.weaken.weaken.weaken))))))))
derive_free_closed all_m
theorem all_sat_l {d} (ρ : Env M d) (B J R K : Term d) :
    Formula.satisfies ρ (all_m (𝒞 := 𝒞) B J R K) ↔
      All_d I (B.eval ρ) (J.eval ρ) (R.eval ρ) (K.eval ρ) := by
  simp only [all_m, All_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_imp_iff, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem all_compl_l {B J R C D K} (hc : Cm_d B R C) (hd : Pr_d I B J C D)
    (hk : Cm_d B D K) : All_d I B J R K := by
  classical
  intro x
  refine (hk x).trans (and_congr_right fun hx => ⟨?_, ?_⟩)
  · intro hn y z hy hz hp
    exact Classical.byContradiction (fun hr => hn ((hd x).mpr ⟨hx, y, z, hy, hz, hp, (hc z).mpr ⟨hz, hr⟩⟩))
  · intro h hxD
    obtain ⟨_, y, z, hy, hz, hp, hzC⟩ := (hd x).mp hxD
    exact ((hc z).mp hzC).2 (h y z hy hz hp)

theorem all_unique_l (hE : Extensional M) {B J R K L} (h : All_d I B J R K) (k : All_d I B J R L) : K = L :=
  hE.eq_of_same_members K L (fun x => (h x).trans (k x).symm)

theorem all_exists_l (hZF : M.Models ZF) (B J R : M.Domain) : ∃ K, All_d I B J R K := by
  obtain ⟨C, hc⟩ := cm_exists_l (ZF.modelsKP hZF) B R
  obtain ⟨D, hd⟩ := pr_exists_l I hZF B J C
  obtain ⟨K, hk⟩ := cm_exists_l (ZF.modelsKP hZF) B D
  exact ⟨K, all_compl_l I hc hd hk⟩

/-- 补码与补集同时构造；仅要求 KP 和已有解释。 -/
theorem pcode_compl_l (hKP : M.Models KP) {ω A B J p K} (hω : M.IsOmega ω)
    (hp : Pcode_d I ω A p) (hk : Pden_d I ω A B J p K) :
    ∃ q L, Pedit_d I false p q ∧ Pcode_d I ω A q ∧ Cm_d B K L ∧ Pden_d I ω A B J q L := by
  obtain ⟨q, hq, hq'⟩ := pedit_exists_l I hKP hω hp false
  obtain ⟨L, hl⟩ := cm_exists_l hKP B K
  exact ⟨q, L, hq, hq', hl, pedit_compl_l I hKP.1 hq hk hl⟩

theorem pedit_proj_l (hZF : M.Models ZF) {ω A B J n o p q K L} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n o p) (ho : M.IsOrdinalOne o) (he : Pedit_d I true p q)
    (hk : Pden_d I ω A B J p K) (hl : Pr_d I B J K L) : Pden_d I ω A B J q L := by
  obtain ⟨hn, _, c, hp, _⟩ := hc
  obtain ⟨n', m, t, u, c', hp', hq, hm, ht⟩ := he
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  obtain ⟨n', t, c', C, D, hp', hC, hv, hd⟩ := hk
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  have hu : ∀ x, ¬ M.mem x u := ht.elim (fun h => (ptag_disjoint_l h.1 ho).elim) And.right
  have hd : Cm_d B D K := hd.elim (fun h => (ptag_disjoint_l h.1 ho).elim) And.right
  exact ⟨m, u, c, C, L, hq, hC, (pval_succ_l I hZF hω hn hm).mpr ⟨D, hv, K, hd, hl⟩, Or.inl ⟨hu, rfl⟩⟩

theorem pedit_all_l (hZF : M.Models ZF) {ω A B J n z p q K L} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n z p) (hz : ∀ x, ¬ M.mem x z) (he : Pedit_d I true p q)
    (hk : Pden_d I ω A B J p K) (hl : All_d I B J K L) : Pden_d I ω A B J q L := by
  obtain ⟨hn, _, c, hp, _⟩ := hc
  obtain ⟨n', m, t, u, c', hp', hq, hm, ht⟩ := he
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  obtain ⟨n', t, c', C, D, hp', hC, hv, hd⟩ := hk
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  have hu : M.IsOrdinalOne u := ht.elim And.right (fun h => (ptag_disjoint_l hz h.1).elim)
  have e : D = K := hd.elim And.right (fun h => (ptag_disjoint_l hz h.1).elim)
  subst D
  obtain ⟨V, hvC⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  obtain ⟨W, hw⟩ := pr_exists_l I hZF B J V
  obtain ⟨L', hl'⟩ := cm_exists_l (ZF.modelsKP hZF) B W
  have e := all_unique_l I hZF.1 (all_compl_l I hvC hw hl') hl
  exact ⟨m, u, c, C, W, hq, hC, (pval_succ_l I hZF hω hn hm).mpr ⟨K, hv, V, hvC, hw⟩,
    Or.inr ⟨hu, e ▸ hl'⟩⟩

/-- 同一实际改写给出所有层的量词运算；极性决定存在或全称。 -/
theorem pcode_quant_l (hZF : M.Models ZF) {ω A B J n t p K} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n t p) (hk : Pden_d I ω A B J p K) :
    ∃ m u q L, M.SuccessorOf m n ∧ Pc_d I ω A m u q ∧ Pedit_d I true p q ∧
      Pden_d I ω A B J q L ∧
      (((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u ∧ All_d I B J K L) ∨
       (M.IsOrdinalOne t ∧ (∀ x, ¬ M.mem x u) ∧ Pr_d I B J K L)) := by
  obtain ⟨q, he, hq⟩ := pedit_exists_l I (ZF.modelsKP hZF) hω (pc_code_l I hc) true
  obtain ⟨n', m, t', u, c, hp, hq', hm, ht⟩ := he
  obtain ⟨d, hd, _⟩ := hc.2.2
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hd
  subst n' t' d
  obtain ⟨m', u', c', hq'', hmω, _, hc'⟩ := hq
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hq'' hq'
  subst m' u' c'
  have he : Pedit_d I true p q := ⟨n, m, t, u, c, hp, hq', hm, ht⟩
  have out : Pc_d I ω A m u q := ⟨hmω, ht.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), c, hq', hc'⟩
  rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩
  · obtain ⟨L, hl⟩ := all_exists_l I hZF B J K
    exact ⟨m, u, q, L, hm, out, he, pedit_all_l I hZF hω hc ht he hk hl, Or.inl ⟨ht, hu, hl⟩⟩
  · obtain ⟨L, hl⟩ := pr_exists_l I hZF B J K
    exact ⟨m, u, q, L, hm, out, he, pedit_proj_l I hZF hω hc ht he hk hl, Or.inr ⟨ht, hu, hl⟩⟩

end YesMetaZFC.SetTheory.Descriptive
