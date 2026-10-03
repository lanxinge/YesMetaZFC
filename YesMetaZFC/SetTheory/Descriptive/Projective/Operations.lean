import YesMetaZFC.SetTheory.Descriptive.Projective.Code

/-! # 射影码的补与交替量词

直接改写 (层号,极性,Borel 码)：补仅翻转极性；增加量词还把层号取后继。
改写关系由原公式给出且输出唯一，因而可作用于整个内部码族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ppack_ext_l {p q n t c} (h : Ppack_d I p n t c) (k : Ppack_d I q n t c) : p = q := by
  obtain ⟨a, ha, hb⟩ := h
  obtain ⟨b, hc, hd⟩ := k
  exact I.unique ha (I.unique hd hb ▸ hc)

/-- 指定层号和极性的合法码；层号依然是内部集合。 -/
def Pc_d (ω A n t p : M.Domain) : Prop := M.mem n ω ∧
  ((∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t) ∧ ∃ c, Ppack_d I p n t c ∧ Bcode_d I ω A A c
def pc_m {d} (ω A n t p : Term d) : Formula 1 d := .conj (.mem n ω) (.conj
  (.disj (Formula.isEmpty t) (Formula.isOrdinalOne t)) (.existsE (.conj
    (ppack_m (𝒞 := 𝒞) p.weaken n.weaken t.weaken .newest)
    (bcode_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken .newest))))
derive_free_closed pc_m
theorem pc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A n t p : Term d) :
    Formula.satisfies ρ (pc_m (𝒞 := 𝒞) ω A n t p) ↔
      Pc_d I (ω.eval ρ) (A.eval ρ) (n.eval ρ) (t.eval ρ) (p.eval ρ) := by
  simp only [pc_m, Pc_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_isOrdinalOne_iff,
    Formula.satisfies_exists_iff, ppack_sat_l I, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem pc_code_l {ω A n t p} (h : Pc_d I ω A n t p) : Pcode_d I ω A p := by
  obtain ⟨hn, ht, c, hp, hc⟩ := h
  exact ⟨n, t, c, hp, hn, ht, hc⟩

theorem pden_subset_l {ω A B J p K} (h : Pden_d I ω A B J p K) : M.MemberSubset K B := by
  obtain ⟨n, _, _, _, D, _, _, hv, ht⟩ := h
  obtain ⟨H, hH, hn⟩ := hv
  exact ht.elim (fun h => h.2 ▸ hH.bound _ D hn) (fun h x hx => ((h.2 x).mp hx).1)

theorem pc_sigma_l {ω A B J n z K} (hn : M.mem n ω) (hz : ∀ x, ¬ M.mem x z) :
    Ps_d I ω A B J n K ↔ ∃ p, Pc_d I ω A n z p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    obtain ⟨p, hp⟩ := ppack_exists_l I n z c
    exact ⟨p, ⟨hn, Or.inl hz, c, hp, hc⟩, n, z, c, C, K, hp, hC, hv, Or.inl ⟨hz, rfl⟩⟩
  · rintro ⟨p, ⟨_, _, c, hp, hc⟩, m, t, d, C, D, hq, hC, hv, ht⟩
    obtain ⟨hm, ht', hd⟩ := ppack_unique_l I hq hp
    subst m t d
    exact ht.elim (fun h => ⟨c, C, hc, hC, h.2 ▸ hv⟩) (fun h => (ptag_disjoint_l hz h.1).elim)

theorem pc_pi_l {ω A B J n o K} (hn : M.mem n ω) (ho : M.IsOrdinalOne o) :
    Pp_d I ω A B J n K ↔ ∃ p, Pc_d I ω A n o p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨D, ⟨c, C, hc, hC, hv⟩, hd⟩
    obtain ⟨p, hp⟩ := ppack_exists_l I n o c
    exact ⟨p, ⟨hn, Or.inr ho, c, hp, hc⟩, n, o, c, C, D, hp, hC, hv, Or.inr ⟨ho, hd⟩⟩
  · rintro ⟨p, ⟨_, _, c, hp, hc⟩, m, t, d, C, D, hq, hC, hv, ht⟩
    obtain ⟨hm, ht', hd⟩ := ppack_unique_l I hq hp
    subst m t d
    exact ht.elim (fun h => (ptag_disjoint_l h.1 ho).elim) (fun h => ⟨D, ⟨c, C, hc, hC, hv⟩, h.2⟩)

/-- false 为补码，true 为下一层的对偶量词码。两种操作均保留原 Borel 矩阵。 -/
def Pedit_d (b : Bool) (p q : M.Domain) : Prop := ∃ n m t u c,
  Ppack_d I p n t c ∧ Ppack_d I q m u c ∧ (if b then M.SuccessorOf m n else m = n) ∧
  (((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u) ∨ (M.IsOrdinalOne t ∧ ∀ x, ¬ M.mem x u))
def pedit_m (b : Bool) {d} (p q : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2) .newest) (.conj
    (ppack_m (𝒞 := 𝒞) q.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest) (.conj
    (if b then Formula.isSuccessor (.bound 3) (.bound 4) else Formula.extensionalEq (.bound 3) (.bound 4))
    (.disj (.conj (Formula.isEmpty (.bound 2)) (Formula.isOrdinalOne (.bound 1)))
      (.conj (Formula.isOrdinalOne (.bound 2)) (Formula.isEmpty (.bound 1)))))))))))
@[simp] theorem pedit_closed_l (b : Bool) {d} (p q : Term d)
    (hp : p.freeSupport = []) (hq : q.freeSupport = []) : (pedit_m (𝒞 := 𝒞) b p q).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [pedit_m, Definitional.Formula.FreeClosed, hp, hq]
theorem pedit_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (pedit_m (𝒞 := 𝒞) b p q) ↔ Pedit_d I b (p.eval ρ) (q.eval ρ) := by
  cases b <;> simp only [pedit_m, Pedit_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, ppack_sat_l I,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isOrdinalOne_iff, Definitional.Term.eval_weaken] <;> rfl

theorem pedit_unique_l (hE : Extensional M) {b p q r} (h : Pedit_d I b p q) (k : Pedit_d I b p r) : q = r := by
  obtain ⟨n, m, t, u, c, hp, hq, hm, ht⟩ := h
  obtain ⟨n', m', t', u', c', hp', hr, hm', ht'⟩ := k
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hp'
  subst n' t' c'
  have e : m = m' := by
    cases b
    · exact hm.trans hm'.symm
    · exact Structure.SuccessorOf.eq hE hm hm'
  subst m'
  have e : u = u' := by
    rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩ <;> rcases ht' with ⟨ht', hu'⟩ | ⟨ht', hu'⟩
    · exact Structure.IsOrdinalOne.eq hE hu hu'
    · exact (ptag_disjoint_l ht ht').elim
    · exact (ptag_disjoint_l ht' ht).elim
    · exact hE.eq_of_same_members u u' (fun x => iff_of_false (hu x) (hu' x))
  exact ppack_ext_l I hq (e.symm ▸ hr)

theorem pedit_exists_l (hKP : M.Models KP) {ω A p} (hω : M.IsOmega ω)
    (hp : Pcode_d I ω A p) (b : Bool) : ∃ q, Pedit_d I b p q ∧ Pcode_d I ω A q := by
  obtain ⟨n, t, c, hp, hn, ht, hc⟩ := hp
  obtain ⟨z, hz⟩ := KP.exists_empty hKP
  obtain ⟨o, ho⟩ := KP.exists_successor hKP z
  have tag : ∃ u, ((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u) ∨ (M.IsOrdinalOne t ∧ ∀ x, ¬ M.mem x u) :=
    ht.elim (fun h => ⟨o, Or.inl ⟨h, z, hz, ho⟩⟩) (fun h => ⟨z, Or.inr ⟨h, hz⟩⟩)
  obtain ⟨u, hu⟩ := tag
  have level : ∃ m, M.mem m ω ∧ (if b then M.SuccessorOf m n else m = n) := by
    cases b
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
      exact ⟨m, hmω, hm⟩
  obtain ⟨m, hmω, hm⟩ := level
  obtain ⟨q, hq⟩ := ppack_exists_l I m u c
  exact ⟨q, ⟨n, m, t, u, c, hp, hq, hm, hu⟩,
    m, u, c, hq, hmω, hu.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), hc⟩

theorem pedit_compl_l (hE : Extensional M) {ω A B J p q K L} (h : Pedit_d I false p q)
    (hp : Pden_d I ω A B J p K) (hl : Cm_d B K L) : Pden_d I ω A B J q L := by
  obtain ⟨n, m, t, u, c, hp', hq, hm, ht⟩ := h
  obtain ⟨n', t', c', C, D, hp, hC, hv, hk⟩ := hp
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hp'
  subst n' t' c'
  have hm : m = n := hm
  subst m
  refine ⟨n, u, c, C, D, hq, hC, hv, ?_⟩
  rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩ <;> rcases hk with ⟨ht', hk⟩ | ⟨ht', hk⟩
  · exact Or.inr ⟨hu, hk.symm ▸ hl⟩
  · exact (ptag_disjoint_l ht ht').elim
  · exact (ptag_disjoint_l ht' ht).elim
  · obtain ⟨H, hH, hn⟩ := hv
    have hd := cm_symm_l (hH.bound n D hn) hk
    exact Or.inl ⟨hu, cm_unique_l hE hd hl⟩

end YesMetaZFC.SetTheory.Descriptive
