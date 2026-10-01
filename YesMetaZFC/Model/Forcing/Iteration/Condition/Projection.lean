import YesMetaZFC.Model.Forcing.Iteration.Condition.Splice
import YesMetaZFC.Model.Forcing.Internal.Forcing.Conditions

/-! # 坐标阶段之间的限制投影与尾部提升

所有限制都使用库中实际集合函数图的限制谓词。阶段链接记录原样包含、序的
反射、限制投影的单调性、保留尾部时的规范最大下界，以及固定尾部比较的稠密闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_tail_reg_d (I : kpair_convention_l.Interpretation M) (α B R D V : M.Domain) : Prop :=
  ∀ p q a b, M.mem p D → M.mem q D → M.IsRestrictionOf I a p α → M.IsRestrictionOf I b q α →
    Entry_d M a b R →
      Dense_d M B R B (fun c => ∀ w, Row_splice_d M α c p w → Entry_d M w q V) a → Entry_d M p q V

def row_splice_dense_m {n} (α B R V p q a : Term n) : Formula 1 n :=
  .forallE (.imp (below_m B.weaken R.weaken B.weaken .newest a.weaken)
    (.existsE (.conj (below_m B.weaken.weaken R.weaken.weaken B.weaken.weaken .newest (.bound 1))
      (.forallE (.imp (row_splice_m α.weaken.weaken.weaken (.bound 1) p.weaken.weaken.weaken .newest)
        (entry_m .newest q.weaken.weaken.weaken V.weaken.weaken.weaken))))))
derive_free_closed row_splice_dense_m

theorem row_splice_dense_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R V p q a : Term n) :
    Formula.satisfies ρ (row_splice_dense_m α B R V p q a) ↔
      Dense_d M (B.eval ρ) (R.eval ρ) (B.eval ρ)
        (fun c => ∀ w, Row_splice_d M (α.eval ρ) c (p.eval ρ) w → Entry_d M w (q.eval ρ) (V.eval ρ)) (a.eval ρ) := by
  simp only [row_splice_dense_m, Dense_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, below_sat_l M hE, row_splice_sat_l M hE,
    entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def row_tail_reg_m {n} (α B R D V : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 3) D.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 2) D.weaken.weaken.weaken.weaken)
        (.imp (Formula.isRestriction kpair_convention_l (.bound 1) (.bound 3) α.weaken.weaken.weaken.weaken)
          (.imp (Formula.isRestriction kpair_convention_l .newest (.bound 2) α.weaken.weaken.weaken.weaken)
            (.imp (entry_m (.bound 1) .newest R.weaken.weaken.weaken.weaken)
              (.imp (row_splice_dense_m α.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken
                R.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
                (entry_m (.bound 3) (.bound 2) V.weaken.weaken.weaken.weaken))))))))))
derive_free_closed row_tail_reg_m

theorem row_tail_reg_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R D V : Term n) : Formula.satisfies ρ (row_tail_reg_m α B R D V) ↔
      Row_tail_reg_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_tail_reg_m, Row_tail_reg_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isRestriction_iff I, entry_sat_l M hE,
    row_splice_dense_sat_l hE, Definitional.Term.eval_weaken]
  rfl

structure Row_link_d (I : kpair_convention_l.Interpretation M) (α B R D V : M.Domain) : Prop where
  rows : ∀ p, M.mem p B → Row_d M α p
  mem : ∀ p, M.mem p B → M.mem p D
  order : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q V ↔ Entry_d M p q R)
  restrict : ∀ p, M.mem p D → ∃ a, M.mem a B ∧ M.IsRestrictionOf I a p α
  below : ∀ p a, M.mem p D → M.IsRestrictionOf I a p α → Entry_d M p a V
  mono : ∀ p q a b, M.mem p D → M.mem q D → M.IsRestrictionOf I a p α →
    M.IsRestrictionOf I b q α → Entry_d M p q V → Entry_d M a b R
  splice : ∀ p a q r, M.mem p D → M.IsRestrictionOf I a p α → M.mem q B →
    Entry_d M q a R → Row_splice_d M α q p r → M.mem r D ∧ Entry_d M r p V ∧ Entry_d M r q V
  splice_glb : ∀ p a q r u, M.mem p D → M.IsRestrictionOf I a p α → M.mem q B →
    Entry_d M q a R → Row_splice_d M α q p r → M.mem u D →
      Entry_d M u p V → Entry_d M u q V → Entry_d M u r V
  tail : Row_tail_reg_d I α B R D V

/-- 同一阶段的限制就是恒等投影；不需要原 ZF，只用现成的配对解释和外延性。 -/
theorem row_link_id_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    {α B R} (O : Cond_order_d M B R B) (hrow : ∀ p, M.mem p B → Row_d M α p) :
    Row_link_d (kpair_interpretation_l M hE hP) α B R B R := by
  let I := kpair_interpretation_l M hE hP
  have self p (hp : M.mem p B) : M.IsRestrictionOf I p p α :=
    ⟨(hrow p hp).graph, fun i s => ⟨fun hs => ⟨(hrow p hp).domain i s hs, hs⟩, And.right⟩⟩
  have eq p a (hp : M.mem p B) (ha : M.IsRestrictionOf I a p α) : a = p := ha.eq hE (self p hp)
  refine ⟨hrow, fun _ hp => hp, fun _ _ _ _ => Iff.rfl, fun p hp => ⟨p, hp, self p hp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro p a hp ha
    exact (eq p a hp ha) ▸ O.refl p hp
  · intro p q a b hp hq ha hb hpq
    have ha' := eq p a hp ha
    have hb' := eq q b hq hb
    subst a
    subst b
    exact hpq
  · intro p a q r hp ha hq hqa hr
    have ha' := eq p a hp ha
    have hr' := row_splice_absorb_l hE (hrow p hp) hr
    subst a
    subst r
    exact ⟨hq, hqa, O.refl q hq⟩
  · intro p _ q r u hp _ _ _ hr _ _ huq
    exact (row_splice_absorb_l hE (hrow p hp) hr).symm ▸ huq
  · intro p q a b hp hq ha hb hab _
    exact (eq p a hp ha) ▸ (eq q b hq hb) ▸ hab

/-- 两段实际阶段链接复合；新前缀先在中间阶段拼接，再保留上层尾部提升。 -/
theorem row_link_comp_l (hZF : M.Models ZF) {α β B R D V E W}
    (L : Cond_order_d M E W E) (hαβ : M.MemberSubset α β)
    (h : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D V E W) :
    Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R E W := by
  refine ⟨h.rows, fun p hp => k.mem p (h.mem p hp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hp hq
    exact (k.order p q (h.mem p hp) (h.mem q hq)).trans (h.order p q hp hq)
  · intro p hp
    obtain ⟨b, hb, hbp⟩ := k.restrict p hp
    obtain ⟨a, ha, hab⟩ := h.restrict b hb
    exact ⟨a, ha, hab.comp_l hbp hαβ⟩
  · intro p a hp ha
    obtain ⟨b, hb, hbp⟩ := k.restrict p hp
    have hab := hbp.trans ha hαβ
    obtain ⟨a', ha', hab'⟩ := h.restrict b hb
    have he := hab.eq hZF.1 hab'
    subst a'
    exact L.trans p b a hp (k.mem b hb) (k.mem a (h.mem a ha')) (k.below p b hp hbp)
      ((k.order b a hb (h.mem a ha')).mpr (h.below b a hb hab))
  · intro p q a b hp hq ha hb hpq
    obtain ⟨c, hc, hcp⟩ := k.restrict p hp
    obtain ⟨d, hd, hdq⟩ := k.restrict q hq
    exact h.mono c d a b hc hd (hcp.trans ha hαβ) (hdq.trans hb hαβ) (k.mono p q c d hp hq hcp hdq hpq)
  · intro p a q r hp ha hq hqa hr
    obtain ⟨b, hb, hbp⟩ := k.restrict p hp
    obtain ⟨d, hd⟩ := row_splice_exists_l M hZF α q b
    obtain ⟨hdD, hdb, hdq⟩ := h.splice b a q d hb (hbp.trans ha hαβ) hq hqa hd
    have hrd := row_splice_nested_l hZF.1 hαβ hbp.2 hd hr
    obtain ⟨hrE, hrp, hrd⟩ := k.splice p b d r hp hbp hdD hdb hrd
    exact ⟨hrE, hrp, L.trans r d q hrE (k.mem d hdD) (k.mem q (h.mem q hq)) hrd
      ((k.order d q hdD (h.mem q hq)).mpr hdq)⟩
  · intro p a q r u hp ha hq hqa hr hu hup huq
    obtain ⟨b, hb, hbp⟩ := k.restrict p hp
    obtain ⟨c, hc, hcu⟩ := k.restrict u hu
    have self : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) q q β :=
      ⟨(k.rows q (h.mem q hq)).graph, fun i s =>
        ⟨fun hi => ⟨(k.rows q (h.mem q hq)).domain i s hi, hi⟩, And.right⟩⟩
    have hcb := k.mono u p c b hu hp hcu hbp hup
    have hcq := k.mono u q c q hu (k.mem q (h.mem q hq)) hcu self huq
    obtain ⟨d, hd⟩ := row_splice_exists_l M hZF α q b
    obtain ⟨hdD, hdb, _⟩ := h.splice b a q d hb (hbp.trans ha hαβ) hq hqa hd
    have hcd := h.splice_glb b a q d c hb (hbp.trans ha hαβ) hq hqa hd hc hcb hcq
    have hud := L.trans u c d hu (k.mem c hc) (k.mem d hdD) (k.below u c hu hcu)
      ((k.order c d hc hdD).mpr hcd)
    exact k.splice_glb p b d r u hp hbp hdD hdb (row_splice_nested_l hZF.1 hαβ hbp.2 hd hr) hu hup hud
  · intro p q a b hp hq ha hb hab hd
    let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    obtain ⟨s, hs, hsp⟩ := k.restrict p hp
    obtain ⟨t, ht, htq⟩ := k.restrict q hq
    have has := hsp.trans ha hαβ
    have hbt := htq.trans hb hαβ
    have pre {u a} (hu : M.mem u D) (ha : M.IsRestrictionOf I a u α) : M.mem a B := by
      obtain ⟨a', ha', hu'⟩ := h.restrict u hu
      exact (ha.eq hZF.1 hu').symm ▸ ha'
    have haB := pre hs has
    have trans x y z (hx : M.mem x B) (hy : M.mem y B) (hz : M.mem z B)
        (hxy : Entry_d M x y R) (hyz : Entry_d M y z R) : Entry_d M x z R :=
      (h.order x z hx hz).mp ((k.order x z (h.mem x hx) (h.mem z hz)).mp
        (L.trans x y z (k.mem x (h.mem x hx)) (k.mem y (h.mem y hy)) (k.mem z (h.mem z hz))
          ((k.order x y (h.mem x hx) (h.mem y hy)).mpr ((h.order x y hx hy).mpr hxy))
          ((k.order y z (h.mem y hy) (h.mem z hz)).mpr ((h.order y z hy hz).mpr hyz))))
    -- 先将稠密比较投影到中间阶段，再在中间阶段闭合尾部序。
    have hst : Entry_d M s t V := h.tail s t a b hs ht has hbt hab (by
      intro c hc
      obtain ⟨d, hdc, hdd⟩ := hd c hc
      have hda := trans d c a hdc.1 hc.1 haB hdc.2.2 hc.2.2
      refine ⟨d, hdc, fun u hu => ?_⟩
      obtain ⟨huD, hus, _⟩ := h.splice s a d u hs has hdc.1 hda hu
      obtain ⟨r, hr⟩ := row_splice_exists_l M hZF α d p
      have hru := row_splice_nested_l hZF.1 hαβ hsp.2 hu hr
      have hrt := k.splice p s u r hp hsp huD hus hru
      exact k.mono r q u t hrt.1 hq
        ⟨(k.rows u huD).graph, row_splice_prefix_l (k.rows u huD) hru⟩ htq (hdd r hr))
    -- 任意中间前缀先加强其最早前缀；最大下界性质控制两次拼接。
    apply k.tail p q s t hp hq hsp htq hst
    intro v hv
    obtain ⟨c, hc, hcv⟩ := h.restrict v hv.1
    have hca : Below_d M B R B c a := ⟨hc, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hc)),
      h.mono v s c a hv.1 hs hcv has hv.2.2⟩
    obtain ⟨d, hdc, hdd⟩ := hd c hca
    obtain ⟨w, hw⟩ := row_splice_exists_l M hZF α d v
    obtain ⟨hwD, hwv, hwd⟩ := h.splice v c d w hv.1 hcv hdc.1 hdc.2.2 hw
    have hws := (k.order w s hwD hs).mp (L.trans w v s (k.mem w hwD) (k.mem v hv.1) (k.mem s hs)
      ((k.order w v hwD hv.1).mpr hwv) ((k.order v s hv.1 hs).mpr hv.2.2))
    refine ⟨w, ⟨hwD, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hwD)), hwv⟩, fun r hr => ?_⟩
    obtain ⟨u, hu⟩ := row_splice_exists_l M hZF α d s
    have hda := trans d c a hdc.1 hc haB hdc.2.2 hca.2.2
    obtain ⟨huD, hus, _⟩ := h.splice s a d u hs has hdc.1 hda hu
    have hwu := h.splice_glb s a d u w hs has hdc.1 hda hu hwD hws hwd
    obtain ⟨z, hz⟩ := row_splice_exists_l M hZF α d p
    have hz' := row_splice_nested_l hZF.1 hαβ hsp.2 hu hz
    have hzE := (k.splice p s u z hp hsp huD hus hz').1
    obtain ⟨hrE, hrp, hrw⟩ := k.splice p s w r hp hsp hwD hws hr
    have hru := L.trans r w u hrE (k.mem w hwD) (k.mem u huD) hrw ((k.order w u hwD huD).mpr hwu)
    exact L.trans r z q hrE hzE hq (k.splice_glb p s u z r hp hsp huD hus hz' hrE hrp hru) (hdd z hz)

/-- 规范前缀拼接确为原条件与新前缀的最大下界，适用于任意预序。 -/
theorem row_splice_glb_l {I : kpair_convention_l.Interpretation M} {α B R D V p a q r u}
    (L : Cond_order_d M D V D) (h : Row_link_d I α B R D V)
    (hp : M.mem p D) (ha : M.IsRestrictionOf I a p α) (hq : M.mem q B) (hqa : Entry_d M q a R)
    (hr : Row_splice_d M α q p r) (hu : M.mem u D) :
    Entry_d M u r V ↔ Entry_d M u p V ∧ Entry_d M u q V := by
  obtain ⟨hrD, hrp, hrq⟩ := h.splice p a q r hp ha hq hqa hr
  exact ⟨fun hur => ⟨L.trans u r p hu hrD hp hur hrp,
    L.trans u r q hu hrD (h.mem q hq) hur hrq⟩,
    fun ⟨hup, huq⟩ => h.splice_glb p a q r u hp ha hq hqa hr hu hup huq⟩

end YesMetaZFC.Model.Forcing.Internal
