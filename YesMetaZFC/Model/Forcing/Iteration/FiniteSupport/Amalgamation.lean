import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.AmalgamationSyntax

/-! # 有限支撑条件的尾部合并

在模型内部对阶段归纳。支撑并的最大坐标至多出现在一侧；另一侧已属于该坐标
之前的阶段。先在那里合并前缀，再用实际阶段链接保留剩余尾部。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 前缀相容且尾部坐标不交的两个有限支撑条件相容；只需原 ZF。 -/
theorem row_amalgam_l (hZF : M.Models ZF) {δ F H e ω α B R β D V p q}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) false ω F)
    (hB : Entry_d M α B F) (hR : Entry_d M α R H) (hD : Entry_d M β D F) (hV : Entry_d M β V H)
    (hp : M.mem p D) (hq : M.mem q D) (hαβ : M.MemberSubset α β)
    (hdis : Row_disjoint_d α p q)
    (hcmp : Row_cmp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R p q) :
    Cmp_d M D V D p q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 5 := ((((⟨fun _ => α, fun _ => α⟩ : Env M 1).push B).push R).push F).push H
  let φ : UnarySchema 5 := { body := row_amalgam_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ γ : φ.denote ρ γ ↔ Row_amalgam_d I α B R F H γ := row_amalgam_sat_l I hZF.1 _ _ _ _ _ _ _
  have all : ∀ γ, M.mem γ δ → φ.denote ρ γ := by
    intro θ hθ
    apply (h.conditions.1.mem hθ).induction (fun γ => φ.denote ρ γ)
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ.neg ρ θ
      exact ⟨C, fun γ => by simpa only [UnarySchema.denote, UnarySchema.neg, Formula.satisfies_neg_iff] using hC γ⟩
    · intro γ hγo ih
      apply (hφ γ).mpr
      intro D V p q hD hV hp hq hαγ hdis hcmp
      have hs := h.stages γ D V hD hV
      have hγ := (h.conditions.2.2 γ).mpr ⟨D, hD⟩
      have root := h.links α γ B R D V hB hR hD hV hαγ
      have self {θ r} (hr : Row_d M θ r) : M.IsRestrictionOf I r r θ :=
        ⟨hr.graph, fun i s => ⟨fun hh => ⟨hr.domain i s hh, hh⟩, And.right⟩⟩
      obtain ⟨P, hP, hPf⟩ := hS γ D hD p hp
      obtain ⟨Q, hQ, hQf⟩ := hS γ D hD q hq
      obtain ⟨T, hT⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) P Q
      have hTf := ZF.finite_union_l I hZF hω hPf hQf hT
      have hTγ : M.MemberSubset T γ := fun i hi => ((hT i).mp hi).elim
        (fun hi => (hP i).mp hi |>.elim fun s hs' => (hs.rows p hp).domain i s hs')
        (fun hi => (hQ i).mp hi |>.elim fun s hs' => (hs.rows q hq).domain i s hs')
      classical
      by_cases ht : M.MemberSubset T α
      · have hpα : Row_d M α p := ⟨(hs.rows p hp).graph, (hs.rows p hp).functional,
          fun i s hi => ht i ((hT i).mpr (Or.inl ((hP i).mpr ⟨s, hi⟩)))⟩
        have hqα : Row_d M α q := ⟨(hs.rows q hq).graph, (hs.rows q hq).functional,
          fun i s hi => ht i ((hT i).mpr (Or.inr ((hQ i).mpr ⟨s, hi⟩)))⟩
        obtain ⟨a, b, ha, hb, r, hra, hrb⟩ := hcmp
        have he := ha.eq hZF.1 (self hpα)
        subst a
        have he := hb.eq hZF.1 (self hqα)
        subst b
        obtain ⟨p', hp', hpp⟩ := root.restrict p hp
        have he := hpp.eq hZF.1 (self hpα)
        subst p'
        obtain ⟨q', hq', hqq⟩ := root.restrict q hq
        have he := hqq.eq hZF.1 (self hqα)
        subst q'
        have hrD := root.mem r hra.1
        exact ⟨r, ⟨hrD, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hrD),
          (root.order r p hra.1 hp').mpr hra.2.2⟩, (root.order r q hra.1 hq').mpr hrb⟩
      · have hne : ∃ i, M.mem i T := by
          apply Classical.byContradiction
          intro he
          exact ht (fun i hi => False.elim (he ⟨i, hi⟩))
        obtain ⟨m, hm, hmax⟩ := ZF.finite_max_l I hZF hω hγo hTf hTγ hne
        have hmγ := hTγ m hm
        have hmα : ¬ M.mem m α := by
          intro hmα
          apply ht
          intro i hi
          exact (hmax i hi).elim
            (fun him => (h.conditions.1.mem ((h.conditions.2.2 α).mpr ⟨B, hB⟩)).transitive m hmα i him)
            (fun he => he ▸ hmα)
        have hαm : M.MemberSubset α m := by
          rcases h.conditions.1.wellOrder.linear.compare α ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
              m (h.conditions.1.transitive γ hγ m hmγ) with he | he | he
          · exact fun i hi => (he i).mp hi
          · exact (hγo.mem hmγ).transitive.memberSubset he
          · exact False.elim (hmα he)
        obtain ⟨E, hE⟩ := (h.conditions.2.2 m).mp (h.conditions.1.transitive γ hγ m hmγ)
        obtain ⟨W, hW⟩ := (h.relations.2.2 m).mp (h.conditions.1.transitive γ hγ m hmγ)
        have link := h.links m γ E W D V hE hW hD hV (hγo.transitive.memberSubset hmγ)
        have join {a b} (ha : M.mem a D) (hb : M.mem b D)
            (ham : ∀ i s, Entry_d M i s a → M.mem i m)
            (hd : Row_disjoint_d α a b) (hc : Row_cmp_d I α B R a b) : Cmp_d M D V D a b := by
          have harow : Row_d M m a := ⟨(hs.rows a ha).graph, (hs.rows a ha).functional, ham⟩
          obtain ⟨a', haE, haa⟩ := link.restrict a ha
          have he := haa.eq hZF.1 (self harow)
          subst a'
          obtain ⟨b', hbE, hbb⟩ := link.restrict b hb
          obtain ⟨a₀, b₀, ha₀, hb₀, hc₀⟩ := hc
          have hc' : Row_cmp_d I α B R a b' := ⟨a₀, b₀, ha₀, hbb.trans hb₀ hαm, hc₀⟩
          obtain ⟨r, hra, hrb⟩ := (hφ m).mp (ih m hmγ) E W a b' hE hW haE hbE hαm
            (fun i s t hi hj => hd i s t hi ((hbb.2 i t).mp hj).2) hc'
          obtain ⟨s, hsp⟩ := row_splice_exists_l M hZF m r b
          obtain ⟨hsD, hsb, hsr⟩ := link.splice b b' r s hb hbb hra.1 hrb hsp
          exact ⟨s, ⟨hsD, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hsD),
            hs.order.trans s r a hsD (link.mem r hra.1) ha hsr ((link.order r a hra.1 haE).mpr hra.2.2)⟩, hsb⟩
        have lower {a} (had : ∀ i s, Entry_d M i s a → M.mem i T)
            (hn : ∀ s, ¬ Entry_d M m s a) : ∀ i s, Entry_d M i s a → M.mem i m := by
          intro i s hi
          exact (hmax i (had i s hi)).elim id (fun he => False.elim (hn s (he ▸ hi)))
        by_cases hpm : ∃ s, Entry_d M m s p
        · obtain ⟨s, hps⟩ := hpm
          obtain ⟨a, b, ha, hb, r, hra, hrb⟩ := hcmp
          obtain ⟨t, htq, htp⟩ := join hq hp
            (lower (fun i s hi => (hT i).mpr (Or.inr ((hQ i).mpr ⟨s, hi⟩)))
              (fun t hqt => hmα (hdis m s t hps hqt)))
            (fun i s t hq hp => hdis i t s hp hq)
            ⟨b, a, hb, ha, r, ⟨hra.1, hra.2.1, hrb⟩, hra.2.2⟩
          exact ⟨t, ⟨htq.1, htq.2.1, htp⟩, htq.2.2⟩
        · exact join hp hq
            (lower (fun i s hi => (hT i).mpr (Or.inl ((hP i).mpr ⟨s, hi⟩)))
              (fun s hs => hpm ⟨s, hs⟩)) hdis hcmp
  exact (hφ β).mp (all β ((h.conditions.2.2 β).mpr ⟨D, hD⟩)) D V p q hD hV hp hq hαβ hdis hcmp

end YesMetaZFC.Model.Forcing.Internal
