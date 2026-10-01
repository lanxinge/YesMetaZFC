import YesMetaZFC.SetTheory.InnerModel.ProofCode.Uniqueness
import YesMetaZFC.SetTheory.InnerModel.Computation.Totality

/-! # 叶码与运算码的实际构造

合并三份已有推导，取高于三个内部高度的自然数，再加入一条运算行。
扩大证书集合界只搬运已有见证，不重新解释或选择子推导的值。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

theorem pc_step_mono_l {T U F G h c x : M.Domain} (ht : M.MemberSubset T U) (hf : M.MemberSubset F G)
    (hx : Pc_step_d T F h c x) : Pc_step_d U G h c x := by
  have read {a y} : Pc_read_d F h a y → Pc_read_d G h a y :=
    fun ⟨n, hn, r, hr, he⟩ => ⟨n, hn, r, hf r hr, he⟩
  rcases hx with ⟨a, ha, ⟨e, he, ho, hc⟩, haO, W, hw, hx⟩ | ⟨k, a, ha, b, hb, d, hd, u, hu, v, hv, w, hw, hc, h1, h2, h3, hx⟩
  · exact Or.inl ⟨a, ht a ha, ⟨e, ht e he, ho, hc⟩, haO, W, ht W hw, hx⟩
  · obtain ⟨t, htT, p, hpT, ho, hp, hc⟩ := hc
    exact Or.inr ⟨k, a, ht a ha, b, ht b hb, d, ht d hd, u, ht u hu, v, ht v hv, w, ht w hw,
      ⟨t, ht t htT, p, ht p hpT, ho, hp, hc⟩, read h1, read h2, read h3, hx⟩

theorem pc_cover_l (hM : M.Models KPi) (L : List M.Domain) :
    ∃ T, M.TransitiveSet T ∧ ∀ x ∈ L, M.mem x T := by
  obtain ⟨U, hu⟩ := cp_cover_l (KPi.models_iff_l.mp hM).1 L
  obtain ⟨T, ht, hU⟩ := KPi.transitive_cover_l hM U
  exact ⟨T, ht, fun x hx => ht U hU x (hu x hx).2⟩

theorem pc_triple_exists_l (hKP : M.Models KP) (a b c : M.Domain) : ∃ r, Rd_triple_d r a b c := by
  obtain ⟨q, hq⟩ := (kp_pair_l hKP).total b c
  obtain ⟨r, hr⟩ := (kp_pair_l hKP).total a q
  exact ⟨r, q, hq, hr⟩

theorem pc_height_bound_l (hM : M.Models KPi) (L : List M.Domain) (hn : ∀ x ∈ L, KP.N0_d x) :
    ∃ n, KP.N0_d n ∧ ∀ x ∈ L, M.mem x n := by
  let hKP := (KPi.models_iff_l.mp hM).1
  induction L with
  | nil => obtain ⟨e, he⟩ := KP.exists_empty hKP; exact ⟨e, KP.n0_empty_l he, fun _ h => (List.not_mem_nil h).elim⟩
  | cons a L ih =>
    have ha := hn a (by simp)
    obtain ⟨n, ho, hL⟩ := ih (fun x hx => hn x (List.mem_cons_of_mem _ hx))
    have oa := KPi.n0_ordinal_l hM ha
    have on := KPi.n0_ordinal_l hM ho
    rcases Structure.IsOrdinal.trichotomy hKP.1 oa on (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP a n) with he | he | he
    · have he := hKP.1.eq_of_same_members a n he; subst a
      obtain ⟨s, hs⟩ := KP.exists_successor hKP n
      exact ⟨s, KP.n0_succ_l hKP.1 ho hs, fun x hx => ((List.mem_cons.mp hx).elim
        (fun h => h.symm ▸ hs.predecessor_mem) (fun h => (hs x).mpr (Or.inl (hL x h))))⟩
    · exact ⟨n, ho, fun x hx => (List.mem_cons.mp hx).elim (fun h => h.symm ▸ he) (hL x)⟩
    · obtain ⟨s, hs⟩ := KP.exists_successor hKP a
      exact ⟨s, KP.n0_succ_l hKP.1 ha hs, fun x hx => (List.mem_cons.mp hx).elim
        (fun h => h.symm ▸ hs.predecessor_mem) (fun h => (hs x).mpr (Or.inl (oa.transitive n he x (hL x h))))⟩

theorem pc_leaf_exists_l (hM : M.Models KPi) {a x : M.Domain} (ha : M.IsOrdinal a) (hx : Jh_value_d a x) :
    ∃ c T, Pc_leaf_d T c a ∧ Pc_eval_d c x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  obtain ⟨c, hc⟩ := (kp_pair_l hKP).total e a
  obtain ⟨r, hr⟩ := pc_triple_exists_l hKP e c x
  obtain ⟨F, hF⟩ := KP.exists_pair hKP r r
  obtain ⟨W, hw⟩ := (pc_jh_value_l a x).mpr hx
  obtain ⟨T, ht, hT⟩ := pc_cover_l hM [a, e, c, x, W, F]
  have cert : Pc_cert_d F T := by
    refine ⟨ht, hT F (by simp), fun s hs => ?_⟩
    have hs : s = r := ((hF s).mp hs).elim id id; subst s
    exact ⟨e, hT e (by simp), c, hT c (by simp), x, hT x (by simp), hr, KP.n0_empty_l he,
      Or.inl ⟨a, hT a (by simp), ⟨e, hT e (by simp), he, hc⟩, ha, W, hT W (by simp), hw⟩⟩
  exact ⟨c, T, ⟨e, hT e (by simp), he, hc⟩, e, T, F, cert, r, (hF r).mpr (Or.inl rfl), hr⟩

theorem pc_apply_exists_l (hM : M.Models KPi) (k : Rd_sym) {a b d u v w x : M.Domain}
    (ha : Pc_eval_d a u) (hb : Pc_eval_d b v) (hd : Pc_eval_d d w) (hx : Rd_fun_d k u v w x) :
    ∃ c T, Pc_node_d T k c a b d ∧ Pc_eval_d c x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨i, A, F, hF, ha⟩ := ha
  obtain ⟨j, B, G, hG, hb⟩ := hb
  obtain ⟨l, C, H, hH, hd⟩ := hd
  obtain ⟨n, hn, hN⟩ := pc_height_bound_l hM [i, j, l] (by
    intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact (hF.at_l ha).2.2.2.1
    · exact (hG.at_l hb).2.2.2.1
    · exact (hH.at_l hd).2.2.2.1)
  obtain ⟨tag, htag⟩ := num_exists_l hKP (pc_tag_l k)
  obtain ⟨p, hp⟩ := pc_triple_exists_l hKP a b d
  obtain ⟨c, hc⟩ := (kp_pair_l hKP).total tag p
  obtain ⟨r, hr⟩ := pc_triple_exists_l hKP n c x
  obtain ⟨E, he⟩ := KP.exists_unionOfTwo hKP F G
  obtain ⟨D, he'⟩ := KP.exists_unionOfTwo hKP E H
  obtain ⟨K, hk⟩ := KP.exists_insert hKP D r
  have fi : M.MemberSubset F K := fun s hs => (hk s).mpr (Or.inl ((he' s).mpr (Or.inl ((he s).mpr (Or.inl hs)))))
  have gi : M.MemberSubset G K := fun s hs => (hk s).mpr (Or.inl ((he' s).mpr (Or.inl ((he s).mpr (Or.inr hs)))))
  have hi : M.MemberSubset H K := fun s hs => (hk s).mpr (Or.inl ((he' s).mpr (Or.inr hs)))
  obtain ⟨T, ht, hT⟩ := pc_cover_l hM [A, B, C, K, n, c, x, tag, p]
  have ai : M.MemberSubset A T := ht A (hT A (by simp))
  have bi : M.MemberSubset B T := ht B (hT B (by simp))
  have ci : M.MemberSubset C T := ht C (hT C (by simp))
  have old {V U} (hu : Pc_cert_d V U) (hv : M.MemberSubset V K) (hU : M.MemberSubset U T) (s : M.Domain) (hs : M.mem s V) :
      ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧ ∃ x, M.mem x T ∧ Rd_triple_d s h c x ∧ KP.N0_d h ∧ Pc_step_d T K h c x := by
    obtain ⟨h, hh, c, hc, x, hx, he, hn, hs⟩ := hu.row s hs
    exact ⟨h, hU h hh, c, hU c hc, x, hU x hx, he, hn, pc_step_mono_l hU hv hs⟩
  have read {V h c x} (hv : M.MemberSubset V K) (hh : M.mem h n) (hx : Pc_at_d V h c x) : Pc_read_d K n c x :=
    ⟨h, hh, hx.elim fun s hs => ⟨s, hv s hs.1, hs.2⟩⟩
  have cert : Pc_cert_d K T := by
    refine ⟨ht, hT K (by simp), fun s hs => ?_⟩
    rcases (hk s).mp hs with hs | heq
    · rcases (he' s).mp hs with hs | hs
      · exact ((he s).mp hs).elim (old hF fi ai s) (old hG gi bi s)
      · exact old hH hi ci s hs
    · subst s
      exact ⟨n, hT n (by simp), c, hT c (by simp), x, hT x (by simp), hr, hn, Or.inr
        ⟨k, a, ai a (hF.at_l ha).2.1, b, bi b (hG.at_l hb).2.1, d, ci d (hH.at_l hd).2.1,
          u, ai u (hF.at_l ha).2.2.1, v, bi v (hG.at_l hb).2.2.1, w, ci w (hH.at_l hd).2.2.1,
          ⟨tag, hT tag (by simp), p, hT p (by simp), htag, hp, hc⟩,
          read fi (hN i (by simp)) ha, read gi (hN j (by simp)) hb, read hi (hN l (by simp)) hd, hx⟩⟩
  exact ⟨c, T, ⟨tag, hT tag (by simp), p, hT p (by simp), htag, hp, hc⟩,
    n, T, K, cert, r, (hk r).mpr (Or.inr rfl), hr⟩

theorem pc_leaf_value_l (hM : M.Models KPi) {T c a x : M.Domain} (hc : Pc_leaf_d T c a)
    (ha : M.IsOrdinal a) (hx : Jh_value_d a x) : Pc_eval_d c x := by
  obtain ⟨d, _, hd, hx⟩ := pc_leaf_exists_l hM ha hx
  exact pc_leaf_unique_l (KPi.models_iff_l.mp hM).1.1 hd hc ▸ hx

theorem pc_node_value_l (hM : M.Models KPi) {T k c a b d u v w x} (hc : Pc_node_d (M := M) T k c a b d)
    (ha : Pc_eval_d a u) (hb : Pc_eval_d b v) (hd : Pc_eval_d d w) (hx : Rd_fun_d k u v w x) : Pc_eval_d c x := by
  obtain ⟨e, _, he, hx⟩ := pc_apply_exists_l hM k ha hb hd hx
  exact pc_node_unique_l (KPi.models_iff_l.mp hM).1.1 he hc ▸ hx

end YesMetaZFC.SetTheory.InnerModel
