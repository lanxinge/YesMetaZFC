import YesMetaZFC.SetTheory.Descriptive.Projective.Monotone

/-! # 单个内部射影码

码为 (n,(ε,c))：n 是内部层号，ε=0 表示 Σ 分支，ε=1 表示其补，c 是 Borel 码。
解释唯一且实际存在；这里没有外部自然数长度的语法替代。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ppack_d (p n t c : M.Domain) : Prop := ∃ q, I.Codes p n q ∧ I.Codes q t c
def ppack_m {d} (p n t c : Term d) : Formula 1 d := .existsE (.conj
  (𝒞.code p.weaken n.weaken .newest) (𝒞.code .newest t.weaken c.weaken))
derive_free_closed ppack_m
theorem ppack_sat_l {d} (ρ : Env M d) (p n t c : Term d) :
    Formula.satisfies ρ (ppack_m (𝒞 := 𝒞) p n t c) ↔ Ppack_d I (p.eval ρ) (n.eval ρ) (t.eval ρ) (c.eval ρ) := by
  simp only [ppack_m, Ppack_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem ppack_exists_l (n t c : M.Domain) : ∃ p, Ppack_d I p n t c := by
  obtain ⟨q, hq⟩ := I.total t c
  obtain ⟨p, hp⟩ := I.total n q
  exact ⟨p, q, hp, hq⟩
theorem ppack_unique_l {p n t c n' t' c'} (h : Ppack_d I p n t c) (k : Ppack_d I p n' t' c') :
    n = n' ∧ t = t' ∧ c = c' := by
  obtain ⟨q, hp, hq⟩ := h
  obtain ⟨q', hp', hq'⟩ := k
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  exact ⟨rfl, I.injective hq hq'⟩

def Pcode_d (ω A p : M.Domain) : Prop := ∃ n t c, Ppack_d I p n t c ∧ M.mem n ω ∧
  ((∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t) ∧ Bcode_d I ω A A c
def pcode_m {d} (ω A p : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) (.conj
  (.mem (.bound 2) ω.weaken.weaken.weaken) (.conj
  (.disj (Formula.isEmpty (.bound 1)) (Formula.isOrdinalOne (.bound 1)))
  (bcode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken A.weaken.weaken.weaken .newest))))))
derive_free_closed pcode_m

theorem pcode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A p : Term d) :
    Formula.satisfies ρ (pcode_m (𝒞 := 𝒞) ω A p) ↔ Pcode_d I (ω.eval ρ) (A.eval ρ) (p.eval ρ) := by
  simp only [pcode_m, Pcode_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ppack_sat_l I, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isOrdinalOne_iff, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Pden_d (ω A B J p K : M.Domain) : Prop := ∃ n t c C D, Ppack_d I p n t c ∧
  Bden_d I ω A A B c C ∧ Pval_d I ω B J n C D ∧
  (((∀ x, ¬ M.mem x t) ∧ D = K) ∨ (M.IsOrdinalOne t ∧ Cm_d B D K))
def pden_m {d} (ω A B J p K : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2)) (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken
    A.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
  (pval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken
    J.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) .newest)
  (.disj (.conj (Formula.isEmpty (.bound 3)) (Formula.extensionalEq .newest K.weaken.weaken.weaken.weaken.weaken))
    (.conj (Formula.isOrdinalOne (.bound 3))
      (cm_m B.weaken.weaken.weaken.weaken.weaken .newest K.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed pden_m

theorem pden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J p K : Term d) :
    Formula.satisfies ρ (pden_m (𝒞 := 𝒞) ω A B J p K) ↔
      Pden_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (p.eval ρ) (K.eval ρ) := by
  simp only [pden_m, Pden_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ppack_sat_l I, bden_sat_l I hE, pval_sat_l I hE, Formula.satisfies_disj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_isOrdinalOne_iff, cm_sat_l, Definitional.Term.eval_weaken]; rfl

omit I in
theorem ptag_disjoint_l {t : M.Domain} (ht : ∀ x, ¬ M.mem x t) (ho : M.IsOrdinalOne t) : False :=
  ho.elim fun z h => ht z h.2.predecessor_mem

theorem pden_unique_l (hZF : M.Models ZF) {ω A B J p K L} (hω : M.IsOmega ω)
    (h : Pden_d I ω A B J p K) (k : Pden_d I ω A B J p L) : K = L := by
  obtain ⟨n, t, c, C, D, hp, hc, hd, hv⟩ := h
  obtain ⟨n', t', c', C', D', hp', hc', hd', hv'⟩ := k
  obtain ⟨rfl, rfl, rfl⟩ := ppack_unique_l I hp hp'
  have e := hZF.1.eq_of_same_members C C' (fun x => (hc x).trans (hc' x).symm)
  subst C'
  have e := pval_unique_l I hZF hω hd hd'
  subst D'
  rcases hv with ⟨ht, hk⟩ | ⟨ht, hk⟩ <;> rcases hv' with ⟨ht', hl⟩ | ⟨ht', hl⟩
  · exact hk.symm.trans hl
  · exact (ptag_disjoint_l ht ht').elim
  · exact (ptag_disjoint_l ht' ht).elim
  · exact cm_unique_l hZF.1 hk hl

theorem pden_exists_unique_l (hZF : M.Models ZF) {ω A B J p} (hω : M.IsOmega ω) (hp : Pcode_d I ω A p) :
    ∃ K, Pden_d I ω A B J p K ∧ ∀ L, Pden_d I ω A B J p L → L = K := by
  obtain ⟨n, t, c, hp, hn, ht, _⟩ := hp
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨D, hd, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  have out : ∃ K, Pden_d I ω A B J p K := by
    rcases ht with ht | ht
    · exact ⟨D, n, t, c, C, D, hp, hc, hd, Or.inl ⟨ht, rfl⟩⟩
    · obtain ⟨K, hk⟩ := cm_exists_l (ZF.modelsKP hZF) B D
      exact ⟨K, n, t, c, C, D, hp, hc, hd, Or.inr ⟨ht, hk⟩⟩
  obtain ⟨K, hK⟩ := out
  exact ⟨K, hK, fun L hL => pden_unique_l I hZF hω hL hK⟩

def Projective_d (ω A B J K : M.Domain) : Prop := ∃ n, M.mem n ω ∧ (Ps_d I ω A B J n K ∨ Pp_d I ω A B J n K)
def projective_m {d} (ω A B J K : Term d) : Formula 1 d := Formula.existsMem ω (.disj
  (ps_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest K.weaken)
  (pp_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest K.weaken))
derive_free_closed projective_m

theorem projective_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J K : Term d) :
    Formula.satisfies ρ (projective_m (𝒞 := 𝒞) ω A B J K) ↔
      Projective_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) := by
  simp only [projective_m, Projective_d, Formula.satisfies_existsMem_iff, Formula.satisfies_disj_iff,
    ps_sat_l I hE, pp_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem projective_code_l (hZF : M.Models ZF) {ω A B J K} (hω : M.IsOmega ω) :
    Projective_d I ω A B J K ↔ ∃ p, Pcode_d I ω A p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨n, hn, hk | hk⟩
    · obtain ⟨c, C, hc, hC, hv⟩ := hk
      obtain ⟨t, ht⟩ := KP.exists_empty (ZF.modelsKP hZF)
      obtain ⟨p, hp⟩ := ppack_exists_l I n t c
      exact ⟨p, ⟨n, t, c, hp, hn, Or.inl ht, hc⟩, n, t, c, C, K, hp, hC, hv, Or.inl ⟨ht, rfl⟩⟩
    · obtain ⟨L, ⟨c, C, hc, hC, hv⟩, hL⟩ := hk
      obtain ⟨t, ht, _⟩ := hω.exists_ordinalOne_mem
      obtain ⟨p, hp⟩ := ppack_exists_l I n t c
      exact ⟨p, ⟨n, t, c, hp, hn, Or.inr ht, hc⟩, n, t, c, C, L, hp, hC, hv, Or.inr ⟨ht, hL⟩⟩
  · rintro ⟨p, ⟨n, t, c, hp, hn, _, hc⟩, n', t', c', C, D, hp', hC, hv, ht⟩
    obtain ⟨rfl, rfl, rfl⟩ := ppack_unique_l I hp hp'
    refine ⟨n, hn, ?_⟩
    exact ht.elim (fun h => Or.inl ⟨c, C, hc, hC, h.2 ▸ hv⟩)
      (fun h => Or.inr ⟨D, ⟨c, C, hc, hC, hv⟩, h.2⟩)

theorem projective_compl_l (hKP : M.Models KP) {ω A B J K} (hK : Projective_d I ω A B J K) :
    ∃ L, Cm_d B K L ∧ Projective_d I ω A B J L := by
  obtain ⟨n, hn, hk | hk⟩ := hK
  · obtain ⟨L, hl⟩ := cm_exists_l hKP B K
    exact ⟨L, hl, n, hn, Or.inr ⟨K, hk, hl⟩⟩
  · obtain ⟨L, hl, hc⟩ := hk
    exact ⟨L, cm_symm_l (ps_subset_l I hl) hc, n, hn, Or.inl hl⟩

theorem projective_collection_l (hZF : M.Models ZF) (ω A B J : M.Domain) :
    ∃ C, ∀ K, M.mem K C ↔ Projective_d I ω A B J K := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := { body := projective_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨C, fun K => ((hC K).trans (and_congr_right fun _ => projective_sat_l I hZF.1 _ _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨_, _, h | h⟩ := h
  · exact (hP K).mpr (ps_subset_l I h)
  · exact (hP K).mpr (h.elim fun L h => fun x hx => ((h.2 x).mp hx).1)

end YesMetaZFC.SetTheory.Descriptive
